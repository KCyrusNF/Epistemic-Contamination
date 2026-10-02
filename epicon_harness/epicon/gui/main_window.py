"""Main window of the assistant GUI.

Left: the session navigator. Right: the rendered multi-turn conversation.
The toolbar controls what the transcript includes and drives the Excel export.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

from .. import paths, storage
from ..export import export_sessions
from ..models import RunLog, total_usage
from .qt import QtCore, QtGui, QtWidgets, Slot
from .session_panel import SessionEntry, SessionPanel
from .transcript_view import TranscriptView, ViewOptions


class MainWindow(QtWidgets.QMainWindow):
    """Browse run logs, read the conversations, export to Excel."""

    def __init__(
        self,
        results_dir: Path | None = None,
        test_cases_dir: Path | None = None,
        parent: QtWidgets.QWidget | None = None,
    ) -> None:
        super().__init__(parent)
        self.results_dir = results_dir or paths.RESULTS_DIR
        self.test_cases_dir = test_cases_dir or paths.TEST_CASES_DIR
        self._entries: list[SessionEntry] = []

        self.setWindowTitle("Epistemic Contamination — Evaluation Assistant")
        self.resize(1480, 940)

        self.panel = SessionPanel(self)
        self.transcript = TranscriptView(self)
        self.panel.sessionSelected.connect(self._on_session_selected)

        splitter = QtWidgets.QSplitter(QtCore.Qt.Orientation.Horizontal, self)
        splitter.addWidget(self.panel)
        splitter.addWidget(self.transcript)
        splitter.setStretchFactor(0, 0)
        splitter.setStretchFactor(1, 1)
        splitter.setSizes([360, 1120])
        splitter.setChildrenCollapsible(False)
        self.setCentralWidget(splitter)

        self._build_actions()
        self._build_toolbar()
        self._build_menus()

        self.status_message = QtWidgets.QLabel("", self)
        self.backend_label = QtWidgets.QLabel(self.transcript.backend_description(), self)
        self.backend_label.setStyleSheet("color: #6b7280;")
        self.statusBar().addWidget(self.status_message, 1)
        self.statusBar().addPermanentWidget(self.backend_label)

        self.reload()

    # -- actions ------------------------------------------------------------ #
    def _build_actions(self) -> None:
        style = self.style()

        def icon(pixmap: QtWidgets.QStyle.StandardPixmap) -> QtGui.QIcon:
            return style.standardIcon(pixmap)

        self.action_reload = QtGui.QAction(
            icon(QtWidgets.QStyle.StandardPixmap.SP_BrowserReload), "&Reload", self
        )
        self.action_reload.setShortcut(QtGui.QKeySequence.StandardKey.Refresh)
        self.action_reload.setToolTip("Re-read run logs and test cases from disk (F5)")
        self.action_reload.triggered.connect(self.reload)

        self.action_export_all = QtGui.QAction(
            icon(QtWidgets.QStyle.StandardPixmap.SP_DialogSaveButton),
            "Export &all to Excel…",
            self,
        )
        self.action_export_all.setShortcut("Ctrl+E")
        self.action_export_all.triggered.connect(lambda: self._export(scope="filtered"))

        self.action_export_current = QtGui.QAction("Export &current session…", self)
        self.action_export_current.setShortcut("Ctrl+Shift+E")
        self.action_export_current.triggered.connect(lambda: self._export(scope="current"))

        self.action_focus_filter = QtGui.QAction("&Find session", self)
        self.action_focus_filter.setShortcut(QtGui.QKeySequence.StandardKey.Find)
        self.action_focus_filter.triggered.connect(self.panel.search.setFocus)

        self.action_next = QtGui.QAction("&Next session", self)
        self.action_next.setShortcut("Alt+Down")
        self.action_next.triggered.connect(lambda: self.panel.step(1))

        self.action_previous = QtGui.QAction("&Previous session", self)
        self.action_previous.setShortcut("Alt+Up")
        self.action_previous.triggered.connect(lambda: self.panel.step(-1))

        self.action_copy_output = QtGui.QAction("&Copy model outputs", self)
        self.action_copy_output.setShortcut("Ctrl+Shift+C")
        self.action_copy_output.triggered.connect(self._copy_outputs)

        self.action_open_log = QtGui.QAction("Open run &log file", self)
        self.action_open_log.triggered.connect(self._open_log_file)

        self.action_open_logs_dir = QtGui.QAction("Open results &folder", self)
        self.action_open_logs_dir.triggered.connect(
            lambda: self._reveal(self.results_dir)
        )

        self.action_quit = QtGui.QAction("&Quit", self)
        self.action_quit.setShortcut(QtGui.QKeySequence.StandardKey.Quit)
        self.action_quit.triggered.connect(self.close)

        # View toggles, each bound to a ViewOptions field.
        self._toggles: dict[str, QtGui.QAction] = {}
        for field_name, label, default in (
            ("show_prompts", "Show &prompts", True),
            ("show_expected", "Show Lean &ground truth", True),
            ("show_purpose", "Show turn &purpose", True),
            ("show_references", "Show re&ferences", False),
            ("show_reasoning", "Show &thinking content", True),
            ("show_system_instruction", "Show &system instruction", False),
            ("show_metadata", "Show &metadata chips", True),
            ("render_markdown", "Render &Markdown + LaTeX", True),
        ):
            action = QtGui.QAction(label, self, checkable=True)
            action.setChecked(default)
            action.toggled.connect(self._on_toggle_changed)
            self._toggles[field_name] = action

    def _build_toolbar(self) -> None:
        toolbar = self.addToolBar("Main")
        toolbar.setMovable(False)
        toolbar.setToolButtonStyle(QtCore.Qt.ToolButtonStyle.ToolButtonTextBesideIcon)
        toolbar.addAction(self.action_reload)
        toolbar.addSeparator()
        toolbar.addAction(self.action_export_all)
        toolbar.addSeparator()
        for field_name in ("show_prompts", "show_expected", "show_reasoning"):
            toolbar.addAction(self._toggles[field_name])

    def _build_menus(self) -> None:
        file_menu = self.menuBar().addMenu("&File")
        file_menu.addAction(self.action_reload)
        file_menu.addSeparator()
        file_menu.addAction(self.action_export_all)
        file_menu.addAction(self.action_export_current)
        file_menu.addSeparator()
        file_menu.addAction(self.action_open_log)
        file_menu.addAction(self.action_open_logs_dir)
        file_menu.addSeparator()
        file_menu.addAction(self.action_quit)

        view_menu = self.menuBar().addMenu("&View")
        for action in self._toggles.values():
            view_menu.addAction(action)
        view_menu.addSeparator()
        view_menu.addAction(self.action_focus_filter)
        view_menu.addAction(self.action_previous)
        view_menu.addAction(self.action_next)
        view_menu.addSeparator()
        view_menu.addAction(self.action_copy_output)

        help_menu = self.menuBar().addMenu("&Help")
        about = QtGui.QAction("&About", self)
        about.triggered.connect(self._about)
        help_menu.addAction(about)

    # -- data --------------------------------------------------------------- #
    @Slot()
    def reload(self) -> None:
        QtWidgets.QApplication.setOverrideCursor(QtCore.Qt.CursorShape.WaitCursor)
        try:
            logs, failures = storage.load_results(self.results_dir)
            index = storage.TestCaseIndex.load(self.test_cases_dir)
            self._entries = [
                SessionEntry(log, index.for_log(log), location) for log, location in logs
            ]
            self.panel.set_sessions(self._entries)
        finally:
            QtWidgets.QApplication.restoreOverrideCursor()

        if self.panel.current_entry() is None:
            self.panel.select_first()

        usage = total_usage([entry.log for entry in self._entries])
        summary = (
            f"{len(self._entries)} session(s) from {self.results_dir} · "
            f"{len(index)} test case(s) · "
            f"{usage.output_tokens:,} output tokens"
        )
        if failures:
            summary += f" · {len(failures)} unreadable log(s)"
            self.status_message.setToolTip(
                "\n".join(f"{path}: {error}" for path, error in failures[:12])
            )
        else:
            self.status_message.setToolTip("")
        self.status_message.setText(summary)

    @Slot(object)
    def _on_session_selected(self, entry: SessionEntry | None) -> None:
        if entry is None:
            self.transcript.show_session(None, None)
            return
        self.transcript.show_session(entry.log, entry.case)
        self.action_open_log.setEnabled(bool(entry.log.log_path))

    @Slot(bool)
    def _on_toggle_changed(self, _checked: bool) -> None:
        options = ViewOptions(
            **{name: action.isChecked() for name, action in self._toggles.items()}
        )
        self.transcript.set_options(options)

    # -- export ------------------------------------------------------------- #
    def _export(self, *, scope: str) -> None:
        if scope == "current":
            entry = self.panel.current_entry()
            sessions = [(entry.log, entry.case)] if entry else []
            suggestion = f"{entry.log.case_id}_R{entry.log.run_index}.xlsx" if entry else ""
        else:
            visible = self.panel.visible_entries() or self._entries
            sessions = [(item.log, item.case) for item in visible]
            suggestion = "evaluation_export.xlsx"

        if not sessions:
            QtWidgets.QMessageBox.information(
                self, "Nothing to export", "There are no sessions in the current view."
            )
            return

        target, _filter = QtWidgets.QFileDialog.getSaveFileName(
            self,
            "Export evaluation data",
            str(paths.PROJECT_ROOT / suggestion),
            "Excel workbook (*.xlsx)",
        )
        if not target:
            return

        QtWidgets.QApplication.setOverrideCursor(QtCore.Qt.CursorShape.WaitCursor)
        try:
            result = export_sessions(sessions, target)
        except Exception as exc:
            QtWidgets.QApplication.restoreOverrideCursor()
            QtWidgets.QMessageBox.critical(self, "Export failed", str(exc))
            return
        QtWidgets.QApplication.restoreOverrideCursor()

        box = QtWidgets.QMessageBox(self)
        box.setWindowTitle("Export complete")
        box.setText(
            f"Wrote {result.run_count} session(s) across {result.group_count} sheet(s) "
            f"({result.turn_count} turn-row(s)) to:\n{result.path}"
        )
        open_button = box.addButton("Open file", QtWidgets.QMessageBox.ButtonRole.AcceptRole)
        box.addButton("Close", QtWidgets.QMessageBox.ButtonRole.RejectRole)
        box.exec()
        if box.clickedButton() is open_button:
            self._reveal(result.path)

    # -- misc --------------------------------------------------------------- #
    def _copy_outputs(self) -> None:
        text = self.transcript.current_text()
        if text:
            QtWidgets.QApplication.clipboard().setText(text)
            self.statusBar().showMessage("Model outputs copied to clipboard.", 3000)

    def _open_log_file(self) -> None:
        entry = self.panel.current_entry()
        if entry and entry.log.log_path:
            self._reveal(paths.PROJECT_ROOT / entry.log.log_path)

    @staticmethod
    def _reveal(target: Path) -> None:
        target = Path(target)
        if not target.exists():
            return
        if sys.platform.startswith("win"):
            import os

            os.startfile(str(target))
        elif sys.platform == "darwin":
            subprocess.Popen(["open", str(target)])
        else:
            subprocess.Popen(["xdg-open", str(target)])

    def _about(self) -> None:
        from .. import __version__

        QtWidgets.QMessageBox.about(
            self,
            "About",
            f"<b>Epistemic Contamination — Evaluation Assistant</b> {__version__}"
            f"<p>Reads run logs from <code>{self.results_dir}</code> and pairs them with test "
            f"cases from <code>{self.test_cases_dir}</code>.</p>"
            f"<p>Rendering backend: {self.transcript.backend_description()}</p>",
        )

    @staticmethod
    def entries_to_sessions(entries: list[SessionEntry]) -> list[tuple[RunLog, object]]:
        return [(entry.log, entry.case) for entry in entries]
