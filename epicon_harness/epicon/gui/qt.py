"""Qt binding shim.

PySide6 is preferred; PyQt6 is accepted as a drop-in so the GUI runs on whichever
binding is installed. Only the differences the GUI actually touches are papered
over (signal/slot names and the optional WebEngine module).
"""

from __future__ import annotations

from typing import Any

from ..errors import MissingDependency

QT_BINDING: str

try:  # pragma: no cover - environment dependent
    from PySide6 import QtCore, QtGui, QtWidgets

    QT_BINDING = "PySide6"
    Signal = QtCore.Signal
    Slot = QtCore.Slot
except ImportError:  # pragma: no cover
    try:
        from PyQt6 import QtCore, QtGui, QtWidgets

        QT_BINDING = "PyQt6"
        Signal = QtCore.pyqtSignal
        Slot = QtCore.pyqtSlot
    except ImportError as exc:
        raise MissingDependency("PySide6", "the assistant GUI") from exc


def load_webengine() -> tuple[Any, Any] | tuple[None, None]:
    """Return ``(QWebEngineView, QWebEngineSettings)`` or ``(None, None)``.

    WebEngine carries MathJax, which is what renders LaTeX. When it is missing
    the GUI falls back to a plain rich-text widget.
    """
    try:  # pragma: no cover - environment dependent
        if QT_BINDING == "PySide6":
            from PySide6.QtWebEngineCore import QWebEngineSettings
            from PySide6.QtWebEngineWidgets import QWebEngineView
        else:
            from PyQt6.QtWebEngineCore import QWebEngineSettings
            from PyQt6.QtWebEngineWidgets import QWebEngineView
        return QWebEngineView, QWebEngineSettings
    except ImportError:
        return None, None


__all__ = ["QT_BINDING", "QtCore", "QtGui", "QtWidgets", "Signal", "Slot", "load_webengine"]
