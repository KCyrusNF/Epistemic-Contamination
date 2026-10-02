"""GUI entry point: ``python -m epicon gui`` or ``python -m epicon.gui.app``."""

from __future__ import annotations

import sys
from pathlib import Path

from .. import paths
from .main_window import MainWindow
from .qt import QtWidgets


def build_application(argv: list[str] | None = None) -> QtWidgets.QApplication:
    app = QtWidgets.QApplication.instance() or QtWidgets.QApplication(argv or sys.argv)
    app.setApplicationName("Epistemic Contamination Assistant")
    app.setOrganizationName("Epistemic Contamination")
    app.setApplicationVersion(_version())
    return app


def _version() -> str:
    from .. import __version__

    return __version__


def main(
    results_dir: Path | None = None,
    test_cases_dir: Path | None = None,
    logs_dir: Path | None = None,
    argv: list[str] | None = None,
) -> int:
    paths.ensure_dirs()
    app = build_application(argv)
    window = MainWindow(
        results_dir=results_dir or logs_dir,
        test_cases_dir=test_cases_dir,
    )
    window.show()
    return app.exec()


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
