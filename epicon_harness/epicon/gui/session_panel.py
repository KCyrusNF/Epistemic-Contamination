"""Side panel: hierarchical navigation ``Model -> Domain -> Case ID -> Run Index``.

REQ-GUI-001. Leaf nodes are individual sessions; parent nodes only group them.
"""

from __future__ import annotations

from dataclasses import dataclass

from ..models import RunLog, TestCase
from ..storage import ResultLocation
from .qt import QtCore, QtGui, QtWidgets, Signal

_STATUS_COLOURS = {
    "completed": "#16a34a",
    "COMPLETED": "#16a34a",
    "failed": "#dc2626",
    "FAILED": "#dc2626",
    "partial": "#d97706",
    "skipped": "#6b7280",
    "running": "#2563eb",
}


@dataclass
class SessionEntry:
    """One run log plus the test case and results-path location it came from."""

    log: RunLog
    case: TestCase | None
    location: ResultLocation | None = None

    @property
    def model_id(self) -> str:
        if self.location:
            return self.location.model_id
        return self.log.model_id or "unknown model"

    @property
    def domain(self) -> str:
        if self.location:
            return self.location.domain
        return self.log.test_case.normalised_domain or self.log.domain

    @property
    def run_index(self) -> int:
        if self.location:
            return self.location.run_index
        return self.log.run_index

    @property
    def label(self) -> str:
        return f"Run {self.run_index}"

    def search_blob(self) -> str:
        log = self.log
        parts = [
            log.case_id,
            log.test_case.case_title,
            self.domain,
            log.run_id,
            log.model_metadata.provider,
            self.model_id,
            log.status,
            str(self.run_index),
        ]
        return " ".join(parts).casefold()


def _status_icon(status: str, size: int = 10) -> QtGui.QIcon:
    colour = QtGui.QColor(_STATUS_COLOURS.get(status, "#9ca3af"))
    pixmap = QtGui.QPixmap(size * 2, size * 2)
    pixmap.fill(QtCore.Qt.GlobalColor.transparent)
    painter = QtGui.QPainter(pixmap)
    painter.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing)
    painter.setBrush(QtGui.QBrush(colour))
    painter.setPen(QtCore.Qt.PenStyle.NoPen)
    painter.drawEllipse(2, 2, size * 2 - 4, size * 2 - 4)
    painter.end()
    return QtGui.QIcon(pixmap)


class SessionPanel(QtWidgets.QWidget):
    """Filterable tree of sessions; emits the selected entry."""

    sessionSelected = Signal(object)  # SessionEntry | None

    ENTRY_ROLE = int(QtCore.Qt.ItemDataRole.UserRole) + 1

    def __init__(self, parent: QtWidgets.QWidget | None = None) -> None:
        super().__init__(parent)
        self._entries: list[SessionEntry] = []

        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(8, 8, 4, 8)
        layout.setSpacing(6)

        self.search = QtWidgets.QLineEdit(self)
        self.search.setPlaceholderText("Filter (model, domain, case, run)…")
        self.search.setClearButtonEnabled(True)
        self.search.textChanged.connect(self._apply_filter)
        layout.addWidget(self.search)

        self.tree = QtWidgets.QTreeWidget(self)
        self.tree.setHeaderHidden(True)
        self.tree.setUniformRowHeights(True)
        self.tree.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.SingleSelection)
        self.tree.currentItemChanged.connect(self._on_current_changed)
        layout.addWidget(self.tree, stretch=1)

        self.count_label = QtWidgets.QLabel("", self)
        self.count_label.setStyleSheet("color: #6b7280; font-size: 11px;")
        layout.addWidget(self.count_label)

    def set_sessions(self, entries: list[SessionEntry]) -> None:
        self._entries = entries
        previous = self.current_entry()
        self._rebuild()
        if previous is not None:
            self.select_run(previous.log.run_id)

    def _rebuild(self) -> None:
        self.tree.blockSignals(True)
        self.tree.clear()

        # Model -> Domain -> Case ID -> Run Index
        nested: dict[str, dict[str, dict[str, list[SessionEntry]]]] = {}
        for entry in self._entries:
            nested.setdefault(entry.model_id, {}).setdefault(entry.domain, {}).setdefault(
                entry.log.case_id, []
            ).append(entry)

        for model_id in sorted(nested):
            model_item = QtWidgets.QTreeWidgetItem(self.tree)
            model_item.setText(0, model_id)
            font = model_item.font(0)
            font.setBold(True)
            model_item.setFont(0, font)
            model_item.setExpanded(True)

            for domain in sorted(nested[model_id]):
                domain_item = QtWidgets.QTreeWidgetItem(model_item)
                domain_item.setText(0, domain)
                domain_item.setExpanded(True)

                for case_id in sorted(nested[model_id][domain]):
                    runs = sorted(
                        nested[model_id][domain][case_id],
                        key=lambda item: item.run_index,
                    )
                    case_item = QtWidgets.QTreeWidgetItem(domain_item)
                    title = runs[0].log.test_case.case_title
                    case_item.setText(0, f"{case_id}" + (f"  ·  {title}" if title else ""))
                    case_item.setIcon(
                        0, _status_icon(_worst_status([entry.log.status for entry in runs]))
                    )
                    case_item.setExpanded(len(self._entries) <= 24)

                    for entry in runs:
                        leaf = QtWidgets.QTreeWidgetItem(case_item)
                        leaf.setText(0, entry.label)
                        leaf.setIcon(0, _status_icon(entry.log.status))
                        leaf.setToolTip(
                            0,
                            f"{entry.log.case_id}\n{entry.model_id}\n"
                            f"{entry.log.status} · run {entry.run_index}\n"
                            f"{entry.log.log_path or ''}",
                        )
                        leaf.setData(0, self.ENTRY_ROLE, entry)

        self.tree.blockSignals(False)
        self._apply_filter(self.search.text())

    def _apply_filter(self, text: str) -> None:
        needle = (text or "").strip().casefold()
        visible = 0

        def walk(item: QtWidgets.QTreeWidgetItem) -> int:
            entry = item.data(0, self.ENTRY_ROLE)
            if entry is not None:
                hidden = bool(needle) and needle not in entry.search_blob()
                item.setHidden(hidden)
                return 0 if hidden else 1
            matches = 0
            for index in range(item.childCount()):
                matches += walk(item.child(index))
            item.setHidden(matches == 0)
            if matches and needle:
                item.setExpanded(True)
            return matches

        for index in range(self.tree.topLevelItemCount()):
            visible += walk(self.tree.topLevelItem(index))

        total = len(self._entries)
        self.count_label.setText(
            f"{visible} of {total} session(s)" if needle else f"{total} session(s)"
        )

    def _on_current_changed(
        self, current: QtWidgets.QTreeWidgetItem | None, _previous: object
    ) -> None:
        self.sessionSelected.emit(self._entry_of(current))

    @staticmethod
    def _entry_of(item: QtWidgets.QTreeWidgetItem | None) -> SessionEntry | None:
        if item is None:
            return None
        return item.data(0, SessionPanel.ENTRY_ROLE)

    def current_entry(self) -> SessionEntry | None:
        return self._entry_of(self.tree.currentItem())

    def visible_entries(self) -> list[SessionEntry]:
        result: list[SessionEntry] = []

        def walk(item: QtWidgets.QTreeWidgetItem) -> None:
            if item.isHidden():
                return
            entry = item.data(0, SessionPanel.ENTRY_ROLE)
            if entry is not None:
                result.append(entry)
                return
            for index in range(item.childCount()):
                walk(item.child(index))

        for index in range(self.tree.topLevelItemCount()):
            walk(self.tree.topLevelItem(index))
        return result

    def select_run(self, run_id: str) -> bool:
        def walk(item: QtWidgets.QTreeWidgetItem) -> bool:
            entry = item.data(0, SessionPanel.ENTRY_ROLE)
            if entry is not None and entry.log.run_id == run_id:
                parent = item.parent()
                while parent is not None:
                    parent.setExpanded(True)
                    parent = parent.parent()
                self.tree.setCurrentItem(item)
                return True
            for index in range(item.childCount()):
                if walk(item.child(index)):
                    return True
            return False

        for index in range(self.tree.topLevelItemCount()):
            if walk(self.tree.topLevelItem(index)):
                return True
        return False

    def select_first(self) -> None:
        for entry in self.visible_entries():
            if self.select_run(entry.log.run_id):
                return

    def step(self, delta: int) -> None:
        entries = self.visible_entries()
        if not entries:
            return
        current = self.current_entry()
        if current is None:
            self.select_run(entries[0].log.run_id)
            return
        run_ids = [entry.log.run_id for entry in entries]
        try:
            position = run_ids.index(current.log.run_id)
        except ValueError:
            position = 0
        self.select_run(run_ids[max(0, min(len(run_ids) - 1, position + delta))])


def _worst_status(statuses: list[str]) -> str:
    lowered = {status.lower() for status in statuses}
    for status in ("failed", "partial", "running", "skipped"):
        if status in lowered:
            return status
    return "completed" if statuses else "skipped"
