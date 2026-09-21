"""Batch manifests: a reproducible description of *what* to run, *by whom*, *how hard*.

Because a test case carries no model configuration, the manifest is where the
model lives. A manifest in ``/manifests`` selects test cases, names the model and
its sampling parameters, declares throttle budgets and names an output directory,
so a sweep can be re-run without retyping CLI flags.
"""

from __future__ import annotations

import json
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Any

from . import paths, providers, storage
from .clients.base import RetryPolicy
from .errors import SchemaError
from .model_spec import ModelSpec
from .models import TestCase
from .runner import RunnerConfig
from .throttle import ThrottleSettings


@dataclass
class Manifest:
    """Declarative batch definition."""

    manifest_id: str
    model: ModelSpec
    description: str = ""
    experiment_phase: str | None = None
    test_case_globs: list[str] = field(default_factory=list)
    include_case_ids: list[str] = field(default_factory=list)
    exclude_case_ids: list[str] = field(default_factory=list)
    domains: list[str] = field(default_factory=list)
    repeat: int = 1
    execution: RunnerConfig = field(default_factory=RunnerConfig)
    source_path: str | None = None

    # -- parsing ------------------------------------------------------------ #
    @classmethod
    def from_dict(cls, data: Mapping[str, Any], source: str = "<manifest>") -> Manifest:
        if not isinstance(data, Mapping):
            raise SchemaError("expected a JSON object", source=source)

        manifest_id = data.get("manifest_id")
        if not isinstance(manifest_id, str) or not manifest_id.strip():
            raise SchemaError("'manifest_id' is required", source=source)
        manifest_id = manifest_id.strip()

        # Custom OpenAI-compatible gateways may be declared inline.
        for spec in data.get("providers") or []:
            providers.register_from_dict(spec, overwrite=True)

        model_block = data.get("model")
        if not model_block:
            raise SchemaError(
                "'model' is required: test cases carry no model configuration", source=source
            )
        model = ModelSpec.from_dict(model_block, source=source)

        selection = data.get("test_cases") or ["test_cases"]
        if isinstance(selection, str):
            selection = [selection]

        experiment_phase = data.get("experiment_phase")
        return cls(
            manifest_id=manifest_id,
            model=model,
            description=str(data.get("description") or ""),
            experiment_phase=(
                str(experiment_phase) if isinstance(experiment_phase, str) else None
            ),
            test_case_globs=[str(item) for item in selection],
            include_case_ids=[str(item) for item in (data.get("include_case_ids") or [])],
            exclude_case_ids=[str(item) for item in (data.get("exclude_case_ids") or [])],
            domains=[str(item) for item in (data.get("domains") or [])],
            repeat=max(1, int(data.get("repeat") or 1)),
            execution=_runner_config_from_dict(data, manifest_id, model),
        )

    @classmethod
    def from_file(cls, path: str | Path) -> Manifest:
        file_path = Path(path)
        if not file_path.exists():
            # Accept a bare manifest name, with or without the .json suffix.
            for candidate in (
                paths.MANIFESTS_DIR / file_path.name,
                paths.MANIFESTS_DIR / f"{file_path.name}.json",
            ):
                if candidate.exists():
                    file_path = candidate
                    break
        try:
            raw = json.loads(file_path.read_text(encoding="utf-8"))
        except FileNotFoundError as exc:
            raise SchemaError("manifest not found", source=str(file_path)) from exc
        except json.JSONDecodeError as exc:
            raise SchemaError(f"invalid JSON ({exc})", source=str(file_path)) from exc
        manifest = cls.from_dict(raw, source=str(file_path))
        return replace(manifest, source_path=paths.as_project_relative(file_path))

    # -- selection ---------------------------------------------------------- #
    def resolve_test_cases(self) -> list[TestCase]:
        """Load, filter and (optionally) repeat the selected test cases."""
        targets: list[Path] = []
        for pattern in self.test_case_globs:
            resolved = paths.resolve_data_path(pattern)
            if resolved.exists():
                targets.append(resolved)
                continue
            # Treat the entry as a glob relative to the project root.
            matches = sorted(paths.PROJECT_ROOT.glob(pattern))
            if not matches:
                raise SchemaError(
                    f"selection '{pattern}' matched no files", source=self.source_path
                )
            targets.extend(matches)

        cases, failures = storage.load_test_cases(targets, strict=False)
        if failures and not cases:
            first_path, first_error = failures[0]
            raise SchemaError(f"no loadable test cases ({first_error})", source=str(first_path))

        selected = [case for case in cases if self._matches(case)]
        if self.repeat > 1:
            return [case for case in selected for _ in range(self.repeat)]
        return selected

    def _matches(self, case: TestCase) -> bool:
        if self.include_case_ids and case.case_id not in self.include_case_ids:
            return False
        if case.case_id in self.exclude_case_ids:
            return False
        if self.domains and case.domain not in self.domains:
            return False
        return True

    def runner_config(self) -> RunnerConfig:
        return self.execution


def _throttle_from_dict(data: Mapping[str, Any] | None) -> ThrottleSettings:
    data = data or {}
    return ThrottleSettings(rpm=data.get("rpm"), concurrency=data.get("concurrency"))


def _runner_config_from_dict(
    data: Mapping[str, Any], manifest_id: str, model: ModelSpec
) -> RunnerConfig:
    execution = data.get("execution") or {}
    throttle_block = execution.get("throttle") or {}

    per_provider = {
        key: _throttle_from_dict(value)
        for key, value in throttle_block.items()
        if key != "default" and isinstance(value, Mapping)
    }

    retry_block = data.get("retry") or execution.get("retry") or {}
    retry = RetryPolicy(
        max_attempts=int(retry_block.get("max_attempts", 5)),
        base_delay=float(retry_block.get("base_delay", 1.5)),
        max_delay=float(retry_block.get("max_delay", 60.0)),
        jitter=bool(retry_block.get("jitter", True)),
    )

    results_raw = execution.get("results_dir") or data.get("results_dir")
    results_dir = (
        paths.resolve_data_path(results_raw)
        if isinstance(results_raw, str) and results_raw
        else paths.RESULTS_DIR
    )
    journal_raw = execution.get("journal_dir") or data.get("journal_dir")
    journal_dir = (
        paths.resolve_data_path(journal_raw)
        if isinstance(journal_raw, str) and journal_raw
        else None
    )

    return RunnerConfig(
        model=model,
        run_index=max(1, int(execution.get("run_index") or data.get("run_index") or 1)),
        reviewers=[str(item) for item in (data.get("reviewers") or [])],
        max_workers=int(execution.get("max_workers", 4)),
        throttle=per_provider,
        default_throttle=_throttle_from_dict(throttle_block.get("default")),
        retry=retry,
        request_timeout=float(execution.get("request_timeout", 600.0)),
        turn_delay=float(execution.get("turn_delay", 0.0)),
        results_dir=results_dir,
        journal_dir=journal_dir,
        write_logs=bool(execution.get("write_logs", True)),
        stop_on_error=bool(execution.get("stop_on_error", False)),
        resume=bool(execution.get("resume", False)),
        keep_journal=bool(execution.get("keep_journal", False)),
    )


def discover_manifests(root: Path | None = None) -> list[Path]:
    return list(storage.iter_json_files(root or paths.MANIFESTS_DIR, recursive=False))


def load_manifests(root: Path | None = None) -> list[Manifest]:
    return [Manifest.from_file(path) for path in discover_manifests(root)]


def selected_cases(
    targets: Sequence[str] | None, manifest: Manifest | None
) -> list[TestCase]:
    """Resolve test cases from a manifest, explicit paths, or the whole directory."""
    if manifest is not None:
        return manifest.resolve_test_cases()
    cases, _ = storage.load_test_cases([Path(t) for t in targets] if targets else None)
    return cases
