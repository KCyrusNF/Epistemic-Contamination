"""Command-line entry point: ``python -m epicon <command>``.

Commands
--------
``run``       execute test cases (manifest-driven, or with model flags)
``validate``  parse every test case and report schema problems
``export``    combine run logs into the multi-run Excel audit workbook
``creds``     manage keyring-stored API keys
``providers`` list routing information
``gui``       launch the assistant GUI
``init``      create the project directories
"""

from __future__ import annotations

import argparse
import getpass
import json
import sys
from collections.abc import Sequence
from datetime import datetime, timezone
from pathlib import Path

from . import paths, providers, storage
from .credentials import KeyringCredentialManager, env_var_for
from .errors import ConfigError, EpiconError
from .export_excel import export_results, export_sessions
from .manifest import Manifest
from .model_spec import ModelSpec
from .models import TestCase
from .runner import (
    BatchRunner,
    ProgressEvent,
    RunnerConfig,
    fallback_metadata,
)
from .throttle import ThrottleSettings


def _console_reporter(verbose: bool):
    def report(event: ProgressEvent) -> None:
        prefix = {
            "batch_start": "==>",
            "batch_end": "==>",
            "case_start": " ->",
            "case_end": " <-",
            "turn_start": "   ·",
            "turn_end": "   ·",
            "retry": "   !",
        }.get(event.kind, "   ")

        if event.kind == "turn_start" and not verbose:
            return
        parts = [prefix]
        if event.case_id:
            parts.append(f"[{event.case_id}]")
        if event.turn_id is not None:
            parts.append(f"turn {event.turn_id}/{event.turn_total}")
        if event.completed is not None and event.total:
            parts.append(f"({event.completed}/{event.total})")
        if event.message:
            parts.append(event.message)
        print(" ".join(parts), flush=True)

    return report


def _model_from_args(args: argparse.Namespace, base: ModelSpec | None) -> ModelSpec | None:
    overrides: dict[str, object] = {
        "provider": args.provider,
        "model_id": args.model,
        "model_short_id": args.model_short_id,
        "top_p": args.top_p,
        "max_tokens": args.max_tokens,
    }
    if args.thinking:
        overrides["thinking"] = {"enabled": True}
    overrides = {key: value for key, value in overrides.items() if value is not None}

    if base is not None:
        return base.merged_with(overrides)
    if not overrides.get("provider") or not overrides.get("model_id"):
        return None
    return ModelSpec.from_dict(overrides, source="<command line>")


def _print_dry_run(cases: list[TestCase], model: ModelSpec, config: RunnerConfig) -> None:
    total_turns = sum(case.turn_count for case in cases)
    print(
        f"Dry run — {len(cases)} session(s), {total_turns} turn(s) against "
        f"{model.label} (run {config.run_index})\n"
    )
    print(f"  {'case_id':10} {'domain':20} {'turns':>5}  system  destination")
    results_dir = config.results_dir or paths.RESULTS_DIR
    for case in cases:
        dest = storage.session_path(
            model_id=model.model_id,
            sanitised_model_id=model.sanitised_id,
            run_index=config.run_index,
            domain=case.domain,
            case_id=case.case_id,
            results_dir=results_dir,
        )
        print(
            f"  {case.case_id:10} {case.domain:20} {case.turn_count:>5}  "
            f"{'yes' if case.system_prompt.strip() else 'no ':3}  "
            f"{paths.as_project_relative(dest)}"
        )

    sample = cases[0]
    print(f"\nmodel_metadata (as it would be recorded, shown for {sample.case_id}):")
    print(
        json.dumps(
            fallback_metadata(
                model, system_prompt_used=bool(sample.system_prompt.strip())
            ).to_dict(),
            indent=2,
        )
    )
    print(f"\nresume: {'on' if config.resume else 'off'}  journals: {config.journal_dir or paths.JOURNAL_DIR}")
    print("No API calls were made.")


def cmd_init(_args: argparse.Namespace) -> int:
    paths.ensure_dirs()
    print(f"Project root: {paths.PROJECT_ROOT}")
    for directory in paths.DATA_DIRS:
        print(f"  {directory.name}/ ready")
    return 0


def cmd_providers(_args: argparse.Namespace) -> int:
    credentials = KeyringCredentialManager(enforce_no_dotenv=False)
    print(f"{'provider':12} {'sdk':10} {'key':>5}  base url")
    for spec in providers.all_providers():
        has_key = "yes" if credentials.has(spec.id) else "no"
        print(f"{spec.id:12} {spec.sdk:10} {has_key:>5}  {spec.base_url or '(sdk default)'}")
    return 0


def cmd_validate(args: argparse.Namespace) -> int:
    targets = [Path(target) for target in args.targets] if args.targets else None
    cases, failures = storage.load_test_cases(targets, strict=False)

    for case in cases:
        system = "system+" if case.system_instruction else ""
        print(
            f"  OK   {case.case_id:10} {case.domain:20} "
            f"{system}{case.turn_count} turn(s)  oracle={len(case.formal_artifacts.oracle_theorems)}"
        )
        try:
            lean_path = case.formal_artifacts.resolved_lean_path()
        except EpiconError as exc:
            print(f"       warning: {exc}", file=sys.stderr)
        else:
            if lean_path is not None and not lean_path.exists():
                print(
                    f"       warning: lean_file '{case.formal_artifacts.lean_file}' "
                    f"does not exist",
                    file=sys.stderr,
                )

    for path, error in failures:
        print(f"  FAIL {path}: {error}", file=sys.stderr)
    print(f"\n{len(cases)} valid, {len(failures)} invalid")
    return 1 if failures else 0


def cmd_run(args: argparse.Namespace) -> int:
    manifest = Manifest.from_file(args.manifest) if args.manifest else None

    if manifest is not None:
        config = manifest.runner_config()
        cases = manifest.resolve_test_cases()
    else:
        config = RunnerConfig()
        targets = [Path(target) for target in args.targets] if args.targets else None
        cases, failures = storage.load_test_cases(targets, strict=False)
        for path, error in failures:
            print(f"  skipping {path}: {error}", file=sys.stderr)

    model = _model_from_args(args, config.model)
    if model is None:
        raise ConfigError(
            "No model configured. Test cases carry no model, so supply one with "
            "--provider and --model, or use a manifest with a 'model' block."
        )
    config.model = model

    if args.run_index:
        config.run_index = args.run_index
    if args.workers:
        config.max_workers = args.workers
    if args.rpm or args.concurrency:
        config.default_throttle = ThrottleSettings(rpm=args.rpm, concurrency=args.concurrency)
    if args.results_dir:
        config.results_dir = Path(args.results_dir)
    if args.turn_delay:
        config.turn_delay = args.turn_delay
    if args.stop_on_error:
        config.stop_on_error = True
    if args.resume:
        config.resume = True
    if args.only:
        wanted = set(args.only)
        cases = [case for case in cases if case.case_id in wanted]

    if not cases:
        print("No test cases selected.", file=sys.stderr)
        return 1

    if args.dry_run:
        _print_dry_run(cases, model, config)
        return 0

    credentials = KeyringCredentialManager()
    if not credentials.has(model.provider):
        print(
            f"Missing API key for '{model.provider}'. "
            f"Run: python -m epicon creds set {model.provider}",
            file=sys.stderr,
        )
        return 2

    runner = BatchRunner(credentials, config, on_event=_console_reporter(args.verbose))
    try:
        result = runner.run(cases)
    except KeyboardInterrupt:
        runner.cancel()
        print("\nCancelled; finishing in-flight requests…", file=sys.stderr)
        return 130

    print(f"\n{result.summary()}")

    if args.export:
        index = storage.TestCaseIndex(cases)
        export = export_sessions([(log, index.for_log(log)) for log in result.logs], args.export)
        print(f"Exported {export.group_count} group(s) to {export.path}")

    return 0 if not result.failed else 3


def cmd_export(args: argparse.Namespace) -> int:
    stamp = datetime.now(timezone.utc).strftime("%Y%m%d")
    output = Path(args.output) if args.output else paths.PROJECT_ROOT / f"export_{stamp}.xlsx"
    result = export_results(
        Path(args.results_dir) if args.results_dir else None,
        output,
        test_cases_dir=Path(args.test_cases_dir) if args.test_cases_dir else None,
        only=args.only,
    )
    if result.run_count == 0:
        print("No run logs found under results/.", file=sys.stderr)
        return 1
    print(
        f"Wrote {result.run_count} session(s) / {result.group_count} sheet(s) / "
        f"{result.turn_count} turn-row(s) to {result.path}"
    )
    return 0


def _read_secret(provider: str, *, from_stdin: bool) -> str | None:
    if from_stdin:
        return sys.stdin.read().strip()

    if not sys.stdin.isatty():
        print(
            f"error: no interactive console, so the key for '{provider}' cannot be "
            f"prompted for without hanging.\n"
            f"  Run it in your own terminal:  python -m epicon creds set {provider}\n"
            f"  Or pipe the key in:           "
            f"type key.txt | python -m epicon creds set {provider} --stdin",
            file=sys.stderr,
        )
        return None

    try:
        return getpass.getpass(f"API key for '{provider}': ")
    except (EOFError, KeyboardInterrupt):
        print("\nAborted; nothing was stored.", file=sys.stderr)
        return None


def cmd_creds(args: argparse.Namespace) -> int:
    credentials = KeyringCredentialManager()

    if args.creds_command == "set":
        secret = args.key or _read_secret(args.provider, from_stdin=args.stdin)
        if not secret:
            return 2
        credentials.set(args.provider, secret)
        print(f"Stored key for '{args.provider}' in the OS keyring.")
        return 0

    if args.creds_command == "delete":
        credentials.delete(args.provider)
        print(f"Deleted key for '{args.provider}'.")
        return 0

    print(f"{'provider':12} {'stored':>7}  env fallback")
    for spec in providers.all_providers():
        stored = "yes" if credentials.has(spec.id) else "no"
        fallback = env_var_for(spec.id) if credentials.allow_env else "(disabled)"
        print(f"{spec.id:12} {stored:>7}  {fallback}")
    return 0


def cmd_gui(args: argparse.Namespace) -> int:
    from .gui.app import main as gui_main

    return gui_main(
        results_dir=Path(args.results_dir) if args.results_dir else None,
        test_cases_dir=Path(args.test_cases_dir) if args.test_cases_dir else None,
    )


def _add_model_arguments(parser: argparse.ArgumentParser) -> None:
    group = parser.add_argument_group(
        "model", "Test cases carry no model configuration; supply it here or in a manifest."
    )
    group.add_argument("-p", "--provider", help="anthropic | openai | google | deepseek | zai")
    group.add_argument("--model", help="model id, e.g. Claude-4.6-Opus or gpt-5.4")
    group.add_argument("--model-short-id", help="SanitizedModelID override used in file names")
    group.add_argument("--top-p", type=float)
    group.add_argument("--max-tokens", type=int, help="override REQ-RUN-010 ceiling")
    group.add_argument(
        "--thinking",
        action="store_true",
        help="enable thinking mode (max_tokens=2048, budget=1024)",
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="epicon", description="LLM evaluation pipeline (Epistemic Contamination)"
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    subparsers.add_parser("init", help="create the project data directories").set_defaults(
        func=cmd_init
    )
    subparsers.add_parser("providers", help="show provider routing and key status").set_defaults(
        func=cmd_providers
    )

    validate = subparsers.add_parser("validate", help="parse and check test cases")
    validate.add_argument("targets", nargs="*", help="files or directories (default: test_cases/)")
    validate.set_defaults(func=cmd_validate)

    run = subparsers.add_parser("run", help="execute test cases")
    run.add_argument("targets", nargs="*", help="test case files or directories")
    run.add_argument("-m", "--manifest", help="manifest name or path under manifests/")
    run.add_argument("--only", nargs="+", metavar="CASE_ID", help="restrict to these case_ids")
    run.add_argument("--run-index", type=int, help="run index 1..5 (REQ-RUN-012)")
    run.add_argument("-w", "--workers", type=int, help="max concurrent sessions")
    run.add_argument("--rpm", type=int, help="requests per minute, per provider")
    run.add_argument("--concurrency", type=int, help="in-flight requests per provider")
    run.add_argument("--turn-delay", type=float, help="seconds to pause between turns")
    run.add_argument("--results-dir", help="root output directory (default: results/)")
    run.add_argument("--stop-on-error", action="store_true")
    run.add_argument(
        "--resume",
        action="store_true",
        help="rebuild turns 1..k from the journal and continue at k+1 (REQ-RUN-016)",
    )
    run.add_argument("--dry-run", action="store_true", help="list the plan without calling any API")
    run.add_argument("--export", metavar="XLSX", help="also export results to this workbook")
    run.add_argument("-v", "--verbose", action="store_true")
    _add_model_arguments(run)
    run.set_defaults(func=cmd_run)

    export = subparsers.add_parser("export", help="export run logs to Excel")
    export.add_argument("-o", "--output", help="target .xlsx path")
    export.add_argument("--results-dir", help="run log directory (default: results/)")
    export.add_argument("--test-cases-dir", help="test case directory (default: test_cases/)")
    export.add_argument("--only", nargs="+", metavar="CASE_ID", help="restrict to these case_ids")
    export.set_defaults(func=cmd_export)

    creds = subparsers.add_parser("creds", help="manage API keys in the OS keyring")
    creds_sub = creds.add_subparsers(dest="creds_command", required=True)
    creds_set = creds_sub.add_parser("set", help="store a key (prompts if not given)")
    creds_set.add_argument("provider")
    creds_set.add_argument("key", nargs="?", help="omit to be prompted without echo")
    creds_set.add_argument(
        "--stdin",
        action="store_true",
        help="read the key from stdin instead of prompting (for automation)",
    )
    creds_delete = creds_sub.add_parser("delete", help="remove a stored key")
    creds_delete.add_argument("provider")
    creds_sub.add_parser("list", help="show which providers have keys")
    creds.set_defaults(func=cmd_creds)

    gui = subparsers.add_parser("gui", help="launch the assistant GUI")
    gui.add_argument("--results-dir")
    gui.add_argument("--test-cases-dir")
    gui.set_defaults(func=cmd_gui)

    return parser


def _use_utf8_streams() -> None:
    for stream in (sys.stdout, sys.stderr):
        reconfigure = getattr(stream, "reconfigure", None)
        if reconfigure is not None:
            try:
                reconfigure(encoding="utf-8", errors="replace")
            except (ValueError, OSError):  # pragma: no cover
                pass


def main(argv: Sequence[str] | None = None) -> int:
    _use_utf8_streams()
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        return int(args.func(args))
    except EpiconError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:  # pragma: no cover
        return 130


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
