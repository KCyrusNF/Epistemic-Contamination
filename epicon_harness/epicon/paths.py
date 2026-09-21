"""Project layout resolution.

Every data directory is resolved from a single root so that the batch processor,
the CLI and the GUI all read and write the same tree:

    <root>/lean         Lean 4 sources: the static oracle referenced by test cases
    <root>/manifests    Batch definitions
    <root>/templates    Canonical test case / run log schemas
    <root>/test_cases   Test case configurations
    <root>/results      Session logs (SRS 1.2 three-tier hierarchy)
    <root>/.journals    In-flight turn journals (SRS REQ-RUN-015)

``results/`` is the root output directory mandated by SRS 1.2; the runner creates
``results/{ModelName}-run-{RunIndex}/{normalised-domain}/`` beneath it. Journals are
scratch state for crash recovery, kept outside ``results/`` so that a partially
written session never looks like a finished one.

The root is taken from ``EPICON_ROOT`` when set, otherwise it is discovered by
walking up from this file until a directory containing ``templates`` and
``test_cases`` is found.
"""

from __future__ import annotations

import os
from pathlib import Path

from .errors import PathOutsideProject

_MARKER_DIRS = ("templates", "test_cases")


def _detect_root() -> Path:
    override = os.environ.get("EPICON_ROOT")
    if override:
        return Path(override).expanduser().resolve()

    here = Path(__file__).resolve()
    for candidate in here.parents:
        if all((candidate / marker).is_dir() for marker in _MARKER_DIRS):
            return candidate
    # Fall back to the directory containing the package.
    return here.parent.parent


PROJECT_ROOT = _detect_root()

LEAN_DIR = PROJECT_ROOT / "lean"
MANIFESTS_DIR = PROJECT_ROOT / "manifests"
TEMPLATES_DIR = PROJECT_ROOT / "templates"
TEST_CASES_DIR = PROJECT_ROOT / "test_cases"
#: SRS 1.2: the root output directory for every session log.
RESULTS_DIR = PROJECT_ROOT / "results"
#: SRS REQ-RUN-015: localized cache path for append-only turn journals.
JOURNAL_DIR = PROJECT_ROOT / ".journals"

DATA_DIRS = (LEAN_DIR, MANIFESTS_DIR, TEMPLATES_DIR, TEST_CASES_DIR, RESULTS_DIR)

TEST_CASE_TEMPLATE = TEMPLATES_DIR / "test_case_template.json"
RUN_LOG_TEMPLATE = TEMPLATES_DIR / "run_log_template.json"


def ensure_dirs() -> None:
    """Create the data directories if they do not exist yet."""
    for directory in DATA_DIRS:
        directory.mkdir(parents=True, exist_ok=True)


def resolve_data_path(raw: str | os.PathLike[str], base: Path | None = None) -> Path:
    """Resolve a path from a test case or manifest, confined to the project root.

    Relative paths are interpreted against *base* (default: the project root).
    Anything that resolves outside the root is rejected, so a test case cannot
    pull arbitrary files off the machine into a prompt.
    """
    path = Path(raw).expanduser()
    if not path.is_absolute():
        path = (base or PROJECT_ROOT) / path
    path = path.resolve()

    root = PROJECT_ROOT.resolve()
    if path != root and root not in path.parents:
        raise PathOutsideProject(f"{path} is outside the project root {root}")
    return path


def as_project_relative(path: str | os.PathLike[str]) -> str:
    """Render *path* relative to the project root with forward slashes."""
    resolved = Path(path).resolve()
    try:
        return resolved.relative_to(PROJECT_ROOT.resolve()).as_posix()
    except ValueError:
        return resolved.as_posix()
