"""Batch processor / API orchestrator (bench-runner).

Execution model
---------------
* **One test case = one isolated session** (REQ-RUN-006). Each execution gets its
  own :class:`~epicon.conversation.Conversation` and its own client. Nothing
  mutable is shared, so a long or failed session cannot leak context into another.
* **Cumulative context per turn** (REQ-RUN-004/005). For every turn the user prompt
  is appended to the history, the whole history is transmitted, the call blocks
  until the response arrives, and the reply is appended before the next turn
  starts. The prefix is never rewritten, which is what keeps the provider's KV
  cache warm.
* **Bounded parallelism.** Test cases run on a thread pool; inside it, a
  :class:`~epicon.throttle.ProviderThrottle` caps requests-per-minute and
  concurrent requests per provider.
* **Journal first, log last** (REQ-RUN-015/016). Every completed turn is fsync-ed
  to an append-only ``.jsonl`` journal before the next call goes out, so a killed
  process can be resumed at the turn after the last one that finished. The unified
  session log is written to ``results/`` when the sixteenth turn lands.

What this module deliberately does *not* do
-------------------------------------------
It does not judge the model. SRS 1.3 excludes runtime answer parsing, so every
turn's ``evaluation`` is written with ``is_correct``, ``failure_mode`` and
``comments`` set to ``null``; the Lean ground truth is copied alongside for the
human auditor and nothing compares the two. A failed session is distinguished by
``run_metadata.status``, not by an evaluation verdict.
"""

from __future__ import annotations

import platform
import sys
import threading
import time
from collections.abc import Callable, Iterable, Sequence
from concurrent.futures import Future, ThreadPoolExecutor
from dataclasses import dataclass, field
from importlib import metadata
from pathlib import Path

from . import paths, providers, storage
from .clients.base import RetryPolicy, split_thinking
from .clients.factory import ClientFactory
from .conversation import Conversation
from .credentials import CredentialStore
from .errors import ConfigError, EpiconError
from .model_spec import ModelSpec
from .models import (
    STATUS_COMPLETED,
    STATUS_FAILED,
    ConversationTurn,
    EvaluationSummary,
    LoggedPrompt,
    LoggedResponse,
    ModelMetadata,
    RunLog,
    TestCase,
    Turn,
    TurnEvaluation,
    TurnUsage,
    utc_now,
)
from .storage import JournalState, TurnJournal
from .throttle import ProviderThrottle, ThrottleSettings

EventKind = str  # batch_start | case_start | turn_start | turn_end | case_end | batch_end | retry


@dataclass
class ProgressEvent:
    """Emitted to the CLI/GUI as work proceeds."""

    kind: EventKind
    message: str = ""
    case_id: str | None = None
    run_id: str | None = None
    turn_id: int | None = None
    turn_total: int | None = None
    completed: int | None = None
    total: int | None = None
    run_log: RunLog | None = None
    error: BaseException | None = None


ProgressCallback = Callable[[ProgressEvent], None]


@dataclass
class RunnerConfig:
    """Everything tunable about a batch."""

    #: Which model answers. Required; supplied by a manifest or CLI flags.
    model: ModelSpec | None = None
    #: Run index 1..5, part of the output path (REQ-RUN-012).
    run_index: int = 1
    #: Reviewer ids to pre-seed ``researcher_review`` slots with.
    reviewers: list[str] = field(default_factory=list)
    max_workers: int = 4
    throttle: dict[str, ThrottleSettings] = field(default_factory=dict)
    default_throttle: ThrottleSettings = field(default_factory=ThrottleSettings)
    retry: RetryPolicy = field(default_factory=RetryPolicy)
    request_timeout: float = 600.0
    #: Pause between turns of the same session; keeps bursty sessions polite.
    turn_delay: float = 0.0
    results_dir: Path | None = None
    journal_dir: Path | None = None
    write_logs: bool = True
    stop_on_error: bool = False
    #: REQ-RUN-016: rebuild turns 1..k from the journal instead of re-querying them.
    resume: bool = False
    #: Keep the journal after a successful write (useful when auditing recovery).
    keep_journal: bool = False


@dataclass
class BatchResult:
    """Outcome of a batch, ready for a summary line or an Excel export."""

    logs: list[RunLog] = field(default_factory=list)
    started_at: str = ""
    finished_at: str = ""
    duration_s: float = 0.0

    @property
    def completed(self) -> list[RunLog]:
        return [log for log in self.logs if log.status == STATUS_COMPLETED]

    @property
    def failed(self) -> list[RunLog]:
        return [log for log in self.logs if log.status != STATUS_COMPLETED]

    def summary(self) -> str:
        usage = TurnUsage()
        answered = 0
        for log in self.logs:
            usage = usage + log.usage_totals
            answered += log.answered_turns
        return (
            f"{len(self.completed)}/{len(self.logs)} sessions COMPLETED "
            f"in {self.duration_s:.1f}s | {answered} turns answered | "
            f"in={usage.input_tokens} out={usage.output_tokens} "
            f"cached={usage.cached_tokens}"
        )


def environment_info() -> dict[str, object]:
    """Python, platform and SDK versions, for diagnostics."""
    versions: dict[str, str] = {}
    for package in ("anthropic", "openai"):
        try:
            versions[package] = metadata.version(package)
        except metadata.PackageNotFoundError:  # pragma: no cover
            versions[package] = "not installed"
    return {
        "python": sys.version.split()[0],
        "platform": platform.platform(),
        "sdk_versions": versions,
    }


def fallback_metadata(model: ModelSpec, *, system_prompt_used: bool) -> ModelMetadata:
    """``model_metadata`` derived from the spec alone, without a live client."""
    try:
        api_endpoint = model.api_endpoint or providers.get_provider(model.provider).api_flavour
    except EpiconError:
        api_endpoint = model.api_endpoint
    return ModelMetadata(
        provider=model.provider,
        model_id=model.model_id,
        api_endpoint=api_endpoint,
        temperature=model.temperature,
        top_p=model.top_p,
        max_tokens=model.token_ceiling,
        thinking_budget_allocated=model.thinking_budget,
        system_prompt_used=system_prompt_used,
    )


class BatchRunner:
    """Runs test cases, one isolated session each, and writes their run logs."""

    def __init__(
        self,
        credentials: CredentialStore,
        config: RunnerConfig | None = None,
        *,
        on_event: ProgressCallback | None = None,
        client_factory: ClientFactory | None = None,
    ) -> None:
        self.config = config or RunnerConfig()
        self.credentials = credentials
        self.factory = client_factory or ClientFactory(
            credentials, retry=self.config.retry, timeout=self.config.request_timeout
        )
        self.throttle = ProviderThrottle(self.config.throttle, self.config.default_throttle)
        self._on_event = on_event
        self._cancel = threading.Event()
        self._lock = threading.Lock()
        self._completed = 0

    # -- control ------------------------------------------------------------ #
    def cancel(self) -> None:
        """Ask the batch to stop; in-flight requests finish, queued work is dropped."""
        self._cancel.set()

    @property
    def cancelled(self) -> bool:
        return self._cancel.is_set()

    def _emit(self, event: ProgressEvent) -> None:
        if self._on_event is None:
            return
        try:
            self._on_event(event)
        except Exception:  # pragma: no cover - a bad listener must not kill the batch
            pass

    def _model(self, override: ModelSpec | None = None) -> ModelSpec:
        model = override or self.config.model
        if model is None:
            raise ConfigError(
                "No model configured. Supply one in the manifest's 'model' block or via "
                "--provider/--model on the command line."
            )
        return model

    # -- batch -------------------------------------------------------------- #
    def run(
        self, cases: Sequence[TestCase], *, model: ModelSpec | None = None
    ) -> BatchResult:
        """Execute *cases* with bounded parallelism."""
        resolved = self._model(model)
        self._cancel.clear()
        self._completed = 0
        total = len(cases)
        started_wall = time.monotonic()
        result = BatchResult(started_at=utc_now())

        self._emit(
            ProgressEvent(
                kind="batch_start",
                total=total,
                message=(
                    f"Starting {total} session(s) against {resolved.label} "
                    f"(run {self.config.run_index}) with {self.config.max_workers} worker(s)"
                ),
            )
        )

        workers = max(1, min(self.config.max_workers, total or 1))
        with ThreadPoolExecutor(max_workers=workers, thread_name_prefix="epicon") as pool:
            futures: dict[Future[RunLog], TestCase] = {
                pool.submit(self._run_case_guarded, case, resolved): case for case in cases
            }
            # Collected in submission order so the result list matches `cases`.
            for future, case in futures.items():
                try:
                    result.logs.append(future.result())
                except Exception as exc:  # pragma: no cover - guarded inside the worker
                    self._emit(
                        ProgressEvent(
                            kind="case_end",
                            case_id=case.case_id,
                            message=f"Unhandled error: {exc}",
                            error=exc,
                        )
                    )

        result.finished_at = utc_now()
        result.duration_s = time.monotonic() - started_wall
        self._emit(
            ProgressEvent(
                kind="batch_end",
                total=total,
                completed=len(result.completed),
                message=result.summary(),
            )
        )
        return result

    def run_files(
        self, targets: Iterable[Path | str] | None = None, *, model: ModelSpec | None = None
    ) -> BatchResult:
        cases, _ = storage.load_test_cases(list(targets) if targets else None)
        return self.run(cases, model=model)

    def _run_case_guarded(self, case: TestCase, model: ModelSpec) -> RunLog:
        if self._cancel.is_set():
            return self._stub_log(case, model, "Cancelled before start.")
        try:
            return self.run_case(case, model=model)
        except Exception as exc:  # last-resort guard: always produce a log
            return self._stub_log(case, model, f"{type(exc).__name__}: {exc}")

    def _new_log(self, case: TestCase, model: ModelSpec, *, run_id: str | None = None) -> RunLog:
        return RunLog.for_test_case(
            case,
            run_id=run_id or storage.next_run_id(self.config.results_dir),
            run_index=self.config.run_index,
            model_metadata=fallback_metadata(
                model, system_prompt_used=bool(case.system_prompt.strip())
            ),
            reviewers=self.config.reviewers,
        )

    def _stub_log(self, case: TestCase, model: ModelSpec, error: str) -> RunLog:
        """A log for a session that never really started."""
        log = self._new_log(case, model)
        log.run_metadata.timestamp_end_utc = log.run_metadata.timestamp_start_utc
        log.run_metadata.total_latency_ms = 0.0
        log.run_metadata.status = STATUS_FAILED
        log.evaluation_summary = EvaluationSummary(total_turns=case.turn_count)
        self._fill_unexecuted(log, case, from_turn_id=1)
        self._emit(
            ProgressEvent(kind="case_end", case_id=case.case_id, message=f"FAILED: {error}")
        )
        if self.config.write_logs:
            storage.write_run_log(
                log, self.config.results_dir, sanitised_model_id=model.sanitised_id
            )
        return log

    # -- single session ----------------------------------------------------- #
    def journal_for(self, case: TestCase, model: ModelSpec) -> Path:
        """Where this session's in-flight journal lives (REQ-RUN-015)."""
        return storage.journal_path(
            model_id=model.model_id,
            sanitised_model_id=model.sanitised_id,
            run_index=self.config.run_index,
            domain=case.domain,
            case_id=case.case_id,
            journal_dir=self.config.journal_dir,
        )

    def run_case(self, case: TestCase, *, model: ModelSpec | None = None) -> RunLog:
        """Execute one test case in a fresh, isolated session."""
        resolved = self._model(model)
        system_prompt = case.system_prompt
        journal_file = self.journal_for(case, resolved)

        recovered = self._recover(case, journal_file)
        log = self._new_log(case, resolved, run_id=recovered.run_id if recovered else None)

        conversation = Conversation(system_prompt=system_prompt)
        resume_from = 1
        prior_latency_ms = 0.0
        if recovered is not None and recovered.turns:
            for turn in recovered.turns:
                log.conversation.append(turn)
                conversation.append_user(turn.prompt.content, turn.turn_id)
                conversation.append_assistant(turn.response.content, turn.turn_id)
                prior_latency_ms += turn.response.latency_ms or 0.0
            resume_from = recovered.resume_from
            log.run_metadata.timestamp_start_utc = (
                str(recovered.header.get("timestamp_start_utc"))
                or log.run_metadata.timestamp_start_utc
            )

        journal = TurnJournal(journal_file)
        client = None
        started_wall = time.monotonic()
        failure: str | None = None

        self._emit(
            ProgressEvent(
                kind="case_start",
                case_id=case.case_id,
                run_id=log.run_id,
                turn_total=case.turn_count,
                message=(
                    f"{case.display_name} ({resolved.label})"
                    + (f" — resuming at turn {resume_from}" if resume_from > 1 else "")
                ),
            )
        )

        def on_retry(attempt: int, delay: float, exc: BaseException) -> None:
            self._emit(
                ProgressEvent(
                    kind="retry",
                    case_id=case.case_id,
                    run_id=log.run_id,
                    message=f"attempt {attempt} failed ({exc}); retrying in {delay:.1f}s",
                    error=exc,
                )
            )

        try:
            journal.open(
                {
                    "run_id": log.run_id,
                    "run_index": self.config.run_index,
                    "case_id": case.case_id,
                    "domain": case.domain,
                    "provider": resolved.provider,
                    "model_id": resolved.model_id,
                    "timestamp_start_utc": log.run_metadata.timestamp_start_utc,
                }
            )
            client = self.factory.create(resolved.provider, on_retry=on_retry)

            pending = [
                spec_turn
                for spec_turn in case.conversation_framework
                if spec_turn.turn_id >= resume_from
            ]
            for position, spec_turn in enumerate(pending):
                if self._cancel.is_set():
                    failure = "Batch cancelled."
                    break

                if (position or resume_from > 1) and self.config.turn_delay:
                    time.sleep(self.config.turn_delay)

                self._emit(
                    ProgressEvent(
                        kind="turn_start",
                        case_id=case.case_id,
                        run_id=log.run_id,
                        turn_id=spec_turn.turn_id,
                        turn_total=case.turn_count,
                    )
                )

                logged, error = self._run_turn(spec_turn, case, resolved, client, conversation)
                log.conversation.append(logged)

                self._emit(
                    ProgressEvent(
                        kind="turn_end",
                        case_id=case.case_id,
                        run_id=log.run_id,
                        turn_id=spec_turn.turn_id,
                        turn_total=case.turn_count,
                        message=error or _turn_label(logged),
                    )
                )

                if error is not None:
                    # Without this turn's reply the cumulative history is no longer
                    # aligned, so the rest of the session cannot be trusted. The
                    # journal keeps the turns that did complete.
                    failure = error
                    if self.config.stop_on_error:
                        self.cancel()
                    break

                journal.append_turn(logged)
        except Exception as exc:
            # Covers setup failures (a missing credential, an unknown provider).
            failure = f"{type(exc).__name__}: {exc}"
        finally:
            if client is not None:
                log.model_metadata = client.effective_metadata(
                    resolved, system_prompt_used=bool(system_prompt.strip())
                )
                client.close()

            elapsed_ms = (time.monotonic() - started_wall) * 1000.0
            log.run_metadata.timestamp_end_utc = utc_now()
            log.run_metadata.total_latency_ms = round(prior_latency_ms + elapsed_ms, 3)
            self._fill_unexecuted(log, case, from_turn_id=len(log.conversation) + 1)
            log.run_metadata.status = (
                STATUS_COMPLETED
                if failure is None and log.answered_turns == case.turn_count
                else STATUS_FAILED
            )
            log.evaluation_summary = EvaluationSummary(total_turns=case.turn_count)

            if self.config.write_logs:
                storage.write_run_log(
                    log, self.config.results_dir, sanitised_model_id=resolved.sanitised_id
                )
                if log.completed and not self.config.keep_journal:
                    journal.discard()
                else:
                    journal.close()
            else:
                journal.close()

            with self._lock:
                self._completed += 1
                completed = self._completed

            self._emit(
                ProgressEvent(
                    kind="case_end",
                    case_id=case.case_id,
                    run_id=log.run_id,
                    completed=completed,
                    run_log=log,
                    message=(
                        f"{log.status} ({log.run_metadata.total_latency_ms or 0:.0f}ms) · "
                        f"{log.answered_turns}/{case.turn_count} turns answered · "
                        f"{log.log_path or 'not written'}"
                        + (f" · {failure}" if failure else "")
                    ),
                )
            )

        return log

    # -- crash recovery ----------------------------------------------------- #
    def _recover(self, case: TestCase, journal_file: Path) -> JournalState | None:
        """Read an interrupted journal and verify it still matches the test case.

        A journal is only usable if the prompts it recorded are the ones this case
        would send now; otherwise the reconstructed prefix would differ from the
        one the model actually saw, which REQ-RUN-005 forbids.
        """
        if not self.config.resume:
            return None
        state = storage.read_journal(journal_file)
        if state is None or not state.turns:
            return None

        for turn in state.turns:
            spec_turn = case.turn(turn.turn_id)
            if spec_turn is None or spec_turn.content != turn.prompt.content:
                raise ConfigError(
                    f"{case.case_id}: the journal at {journal_file} was written for a "
                    f"different version of turn {turn.turn_id}. Resuming would transmit a "
                    f"context the model never saw; delete the journal to start over."
                )
            if not turn.response.content:
                raise ConfigError(
                    f"{case.case_id}: journal turn {turn.turn_id} has no response content."
                )
        return state

    # -- turns -------------------------------------------------------------- #
    def _run_turn(
        self,
        spec_turn: Turn,
        case: TestCase,
        model: ModelSpec,
        client,
        conversation: Conversation,
    ) -> tuple[ConversationTurn, str | None]:
        """Transmit one turn. Returns the logged turn and an error, if any."""
        content = spec_turn.content
        logged = ConversationTurn(
            turn_id=spec_turn.turn_id,
            phase=spec_turn.phase,
            turn_type=spec_turn.turn_type,
            oracle_theorem_ref=case.oracle_theorem_for(spec_turn.turn_id),
            prompt=LoggedPrompt(content=content),
            evaluation=TurnEvaluation.unscored_for(spec_turn.expected_answer),
        )
        started = time.monotonic()

        # 1. Append the user prompt to the cumulative history.
        conversation.append_user(content, spec_turn.turn_id)
        try:
            # 2. Transmit the whole history and block for the reply.
            with self.throttle.slot(model.provider):
                response = client.send(conversation.system_prompt, conversation.messages(), model)
        except EpiconError as exc:  # ApiError and credential/provider errors
            # Drop the unanswered prompt so the history stays aligned.
            conversation.rollback_pending_user()
            logged.response = LoggedResponse(
                content="",
                finish_reason="error",
                latency_ms=round((time.monotonic() - started) * 1000, 3),
            )
            return logged, str(exc)

        answer, inline_thinking = split_thinking(response.text)
        # 3. Append the reply before the next turn is built. The answer goes back
        #    verbatim; a reasoning trace does not, because providers either reject
        #    it or ignore it in subsequent requests.
        conversation.append_assistant(answer, spec_turn.turn_id)
        logged.response = LoggedResponse(
            content=answer,
            thinking_content=response.reasoning or inline_thinking,
            finish_reason=response.finish_reason,
            latency_ms=float(response.latency_ms),
            usage=response.usage.to_log_usage(),
        )
        return logged, None

    def _fill_unexecuted(self, log: RunLog, case: TestCase, *, from_turn_id: int) -> None:
        """Record the turns that were never sent, so ``total_turns`` stays truthful.

        They carry an empty response; ``evaluation`` holds the same nulls as every
        other turn, because 'not executed' is a transport fact, not an audit verdict.
        """
        for spec_turn in case.conversation_framework:
            if spec_turn.turn_id < from_turn_id or log.turn(spec_turn.turn_id) is not None:
                continue
            log.conversation.append(
                ConversationTurn(
                    turn_id=spec_turn.turn_id,
                    phase=spec_turn.phase,
                    turn_type=spec_turn.turn_type,
                    oracle_theorem_ref=case.oracle_theorem_for(spec_turn.turn_id),
                    prompt=LoggedPrompt(content=spec_turn.content),
                    response=LoggedResponse(content=""),
                    evaluation=TurnEvaluation.unscored_for(spec_turn.expected_answer),
                )
            )
        log.conversation.sort(key=lambda turn: turn.turn_id)


def _turn_label(turn: ConversationTurn) -> str:
    usage = turn.response.usage
    label = f"{len(turn.response.content)} chars, {usage.output_tokens} out"
    if usage.cached_tokens:
        label += f", {usage.cached_tokens} cached"
    if turn.response.thinking_content:
        label += ", +thinking"
    return label


def default_results_dir() -> Path:
    return paths.RESULTS_DIR
