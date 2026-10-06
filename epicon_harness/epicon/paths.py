"""Project layout resolution.

Every data directory is resolved from a single root so that the batch processor,
the CLI and the GUI all read and write the same tree:

    <root>/lean         Lean 4 sources: the static oracle referenced by test cases
    <root>/manifests    Batch definitions
    <root>/templates    Canonical test case / run log schemas
    <root>/test_cases   Test case configurations
    <root>/results      Session logs (SRS 1.2 three-tier hierarchy)
    <root>/.journals    In-flight turn journals (SRS REQ-RUN-015)

``results/`` is the root output directory; the runner creates
``results/{domain}/{CaseID}/`` beneath it. Journals are scratch state for crash
recovery, kept outside ``results/`` so that a partially written session never
looks like a finished one.

The root is the directory that contains the ``epicon`` package
(``epicon_harness/``). It is an absolute path derived from this file, so a parent
repository that also has ``templates/`` cannot be selected by walking upward.
"""

from __future__ import annotations

import os
from pathlib import Path

from .errors import PathOutsideProject

# epicon/paths.py -> epicon/ -> epicon_harness/
PROJECT_ROOT = Path(__file__).resolve().parent.parent

#: The repository that contains the harness, one level above :data:`PROJECT_ROOT`.
#:
#: This is the *only* sanctioned step outside the harness, and it exists for a
#: single purpose: the Lean oracle manifest and the Lean sources it names are
#: maintained at the repository root, not inside ``epicon_harness/``. Reads go
#: through :func:`resolve_oracle_path`; nothing is ever written here, and every
#: other path still resolves through :func:`resolve_data_path`.
REPOSITORY_ROOT = PROJECT_ROOT.parent

#: Repository-relative location of the oracle manifest.
ORACLE_MANIFEST_RELPATH = "manifests/oracle_manifest.json"

#: Override for tests and for checkouts that keep the manifest elsewhere.
ORACLE_MANIFEST_ENV = "EPICON_ORACLE_MANIFEST"

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


def oracle_manifest_path() -> Path:
    """Absolute path of the repository's oracle manifest.

    The file is not guaranteed to exist; callers degrade gracefully so the
    harness still runs in a checkout without it.
    """
    override = os.environ.get(ORACLE_MANIFEST_ENV)
    if override:
        return Path(override).expanduser().resolve()
    return (REPOSITORY_ROOT / ORACLE_MANIFEST_RELPATH).resolve()


def resolve_oracle_path(raw: str | os.PathLike[str], base: Path | None = None) -> Path:
    """Resolve an oracle-side path, confined to the repository root.

    The oracle manifest names Lean sources relative to the repository root
    (``lean/oracles/abstract_algebra/AA-01.lean``), which sits one level above
    the harness. Resolution is still bounded: anything climbing past the
    repository root is rejected, so a tampered manifest cannot reach arbitrary
    files on the machine.
    """
    path = Path(raw).expanduser()
    if not path.is_absolute():
        path = (base or REPOSITORY_ROOT) / path
    path = path.resolve()

    root = REPOSITORY_ROOT.resolve()
    if path != root and root not in path.parents:
        raise PathOutsideProject(f"{path} is outside the repository root {root}")
    return path


def as_project_relative(path: str | os.PathLike[str]) -> str:
    """Render *path* relative to the project root with forward slashes."""
    resolved = Path(path).resolve()
    try:
        return resolved.relative_to(PROJECT_ROOT.resolve()).as_posix()
    except ValueError:
        return resolved.as_posix()
