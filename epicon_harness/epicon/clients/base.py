"""Client abstraction shared by both SDK backends."""

from __future__ import annotations

import random
import re
import time
from abc import ABC, abstractmethod
from collections.abc import Callable, Sequence
from dataclasses import dataclass, field
from typing import Any

from ..conversation import Message
from ..errors import ApiError
from ..model_spec import ModelSpec
from ..models import ModelMetadata, Usage
from ..providers import ProviderSpec

#: REQ-RUN-014 names 429, 500 and 503; the neighbouring transient faults are
#: treated the same way because they are equally safe to repeat.
RETRYABLE_STATUS = frozenset({408, 409, 425, 429, 500, 502, 503, 504, 529})

#: Models that inline their reasoning rather than returning it as a field.
_THINK_BLOCK = re.compile(r"<think(?:ing)?>(.*?)</think(?:ing)?>", re.DOTALL | re.IGNORECASE)
#: An unclosed block, left behind when the completion hit its token ceiling.
_OPEN_THINK_BLOCK = re.compile(r"<think(?:ing)?>(.*)\Z", re.DOTALL | re.IGNORECASE)


def split_thinking(text: str) -> tuple[str, str | None]:
    """Separate inline ``<think>`` reasoning from the answer (REQ-RUN-010).

    Returns ``(answer, thinking)``. DeepSeek-style endpoints usually expose the
    trace as its own field, but when the model emits the tags inline they must be
    lifted out so ``response.content`` holds the answer a human is auditing —
    the text itself is never otherwise altered (SRS 1.3).
    """
    if not text or "<think" not in text.lower():
        return text, None

    thoughts = [match.strip() for match in _THINK_BLOCK.findall(text) if match.strip()]
    answer = _THINK_BLOCK.sub("", text)

    # A truncated trace never closed its tag: everything after it is reasoning.
    open_block = _OPEN_THINK_BLOCK.search(answer)
    if open_block is not None:
        if open_block.group(1).strip():
            thoughts.append(open_block.group(1).strip())
        answer = answer[: open_block.start()]

    return answer.strip(), ("\n\n".join(thoughts) or None)


@dataclass
class ChatResponse:
    """Normalised result of one completion request."""

    text: str
    usage: Usage = field(default_factory=Usage)
    reasoning: str | None = None
    finish_reason: str | None = None
    response_id: str | None = None
    request_params: dict[str, Any] = field(default_factory=dict)
    attempts: int = 1
    latency_s: float = 0.0
    raw: Any = field(default=None, repr=False)

    @property
    def cache_hit(self) -> bool:
        return self.usage.cache_read_input_tokens > 0

    @property
    def latency_ms(self) -> int:
        return round(self.latency_s * 1000)


@dataclass(frozen=True)
class RetryPolicy:
    """Exponential backoff with full jitter, over up to five attempts (REQ-RUN-014)."""

    max_attempts: int = 5
    base_delay: float = 1.5
    max_delay: float = 60.0
    jitter: bool = True

    def delay_for(self, attempt: int, retry_after: float | None = None) -> float:
        if retry_after is not None:
            return min(max(retry_after, 0.0), self.max_delay)
        delay = min(self.base_delay * (2 ** (attempt - 1)), self.max_delay)
        return random.uniform(0.0, delay) if self.jitter else delay


class LLMClient(ABC):
    """One client instance serves one isolated test case execution.

    Subclasses implement :meth:`_invoke` (a single request) and the small set of
    error-introspection hooks; the retry loop, timing and error wrapping live
    here so both SDKs behave identically from the runner's point of view.
    """

    #: Spec fields this provider cannot transmit; reported as ``null`` in the log.
    UNSUPPORTED_METADATA_FIELDS: frozenset[str] = frozenset()

    def __init__(
        self,
        spec: ProviderSpec,
        api_key: str,
        *,
        retry: RetryPolicy | None = None,
        timeout: float = 600.0,
        max_retries_sdk: int = 0,
        on_retry: Callable[[int, float, BaseException], None] | None = None,
    ) -> None:
        self.spec = spec
        self.retry = retry or RetryPolicy()
        self.timeout = timeout
        # SDK-level retries are disabled by default so this class owns the
        # backoff schedule and the attempt count recorded in the log.
        self.max_retries_sdk = max_retries_sdk
        self._on_retry = on_retry
        self._client = self._build_client(api_key)

    # -- subclass hooks ---------------------------------------------------- #
    @abstractmethod
    def _build_client(self, api_key: str) -> Any: ...

    @abstractmethod
    def _invoke(
        self, system: str, messages: Sequence[Message], model: ModelSpec
    ) -> ChatResponse: ...

    def _status_code(self, exc: BaseException) -> int | None:
        return getattr(exc, "status_code", None) or getattr(exc, "http_status", None)

    def _retry_after(self, exc: BaseException) -> float | None:
        response = getattr(exc, "response", None)
        headers = getattr(response, "headers", None)
        if not headers:
            return None
        for header in ("retry-after", "Retry-After", "retry-after-ms"):
            value = headers.get(header)
            if value:
                try:
                    seconds = float(value)
                except (TypeError, ValueError):
                    continue
                return seconds / 1000.0 if header.endswith("ms") else seconds
        return None

    def _is_retryable(self, exc: BaseException) -> bool:
        status = self._status_code(exc)
        if status is not None:
            return status in RETRYABLE_STATUS
        # Connection resets / read timeouts surface without a status code.
        name = type(exc).__name__.lower()
        return any(token in name for token in ("timeout", "connection", "apiconnection"))

    # -- public API -------------------------------------------------------- #
    def send(
        self, system: str, messages: Sequence[Message], model: ModelSpec
    ) -> ChatResponse:
        """Transmit the cumulative history and return the model's reply."""
        started = time.monotonic()
        last_exc: BaseException | None = None

        for attempt in range(1, self.retry.max_attempts + 1):
            try:
                response = self._invoke(system, messages, model)
            except Exception as exc:
                last_exc = exc
                retryable = self._is_retryable(exc)
                if not retryable or attempt == self.retry.max_attempts:
                    raise ApiError(
                        f"{self.spec.id}/{model.model_id}: {type(exc).__name__}: {exc}",
                        provider=self.spec.id,
                        model=model.model_id,
                        status_code=self._status_code(exc),
                        attempts=attempt,
                        retryable=retryable,
                    ) from exc
                delay = self.retry.delay_for(attempt, self._retry_after(exc))
                if self._on_retry:
                    self._on_retry(attempt, delay, exc)
                time.sleep(delay)
                continue

            response.attempts = attempt
            response.latency_s = time.monotonic() - started
            return response

        # Unreachable: the loop either returns or raises.
        raise ApiError(
            f"{self.spec.id}/{model.model_id}: retries exhausted ({last_exc})",
            provider=self.spec.id,
            model=model.model_id,
            attempts=self.retry.max_attempts,
        )

    def effective_metadata(
        self, model: ModelSpec, *, system_prompt_used: bool
    ) -> ModelMetadata:
        """The ``model_metadata`` block, reflecting what this client can transmit.

        Parameters the provider does not support — or rejected earlier in the
        session — are reported as ``null`` rather than as requested, so the log
        does not claim a setting that never reached the API.
        """
        unsupported = set(self.UNSUPPORTED_METADATA_FIELDS) | self._runtime_unsupported(model)

        def value(name: str, raw: Any) -> Any:
            return None if name in unsupported else raw

        return ModelMetadata(
            provider=self.spec.id,
            model_id=model.model_id,
            api_endpoint=model.api_endpoint or self.spec.api_flavour,
            temperature=value("temperature", model.temperature),
            top_p=value("top_p", model.top_p),
            max_tokens=model.token_ceiling,
            thinking_budget_allocated=model.thinking_budget,
            system_prompt_used=system_prompt_used,
        )

    def _runtime_unsupported(self, model: ModelSpec) -> set[str]:
        """Fields dropped for this particular spec (overridden by subclasses)."""
        return set()

    def close(self) -> None:
        closer = getattr(self._client, "close", None)
        if callable(closer):
            try:
                closer()
            except Exception:  # pragma: no cover - best effort teardown
                pass

    def __enter__(self) -> LLMClient:
        return self

    def __exit__(self, *_exc_info: object) -> None:
        self.close()

    # -- shared helpers ---------------------------------------------------- #
    def _sampling_params(self, model: ModelSpec) -> dict[str, Any]:
        """REQ-RUN-009: ``temperature`` goes on every payload, unconditionally."""
        params: dict[str, Any] = {"temperature": model.temperature}
        if model.top_p is not None:
            params["top_p"] = model.top_p
        for name in self.spec.unsupported_params:
            params.pop(name, None)
        return params
