"""PySide6/PyQt6 assistant GUI.

Importing this package pulls in Qt, so the batch processor never imports it at
module scope — the CLI does it lazily inside the ``gui`` command.
"""

from __future__ import annotations

__all__ = ["MainWindow", "SessionPanel", "TranscriptView", "ViewOptions", "main"]


def __getattr__(name: str):  # pragma: no cover - thin lazy re-export
    if name == "main":
        from .app import main

        return main
    if name == "MainWindow":
        from .main_window import MainWindow

        return MainWindow
    if name == "SessionPanel":
        from .session_panel import SessionPanel

        return SessionPanel
    if name in ("TranscriptView", "ViewOptions"):
        from . import transcript_view

        return getattr(transcript_view, name)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
