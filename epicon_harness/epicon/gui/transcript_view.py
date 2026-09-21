"""Turn inspector: prompt / Lean oracle on the left, raw completion on the right.

REQ-GUI-002/003/004. One turn is shown at a time. ``thinking_content`` lives in a
collapsible ``<details>`` so the auditor can ignore it until they need it. MathJax
still typesets the ``$$…$$`` these prompts mandate.
"""

from __future__ import annotations

import html
from dataclasses import dataclass

from .. import paths
from ..models import ConversationTurn, RunLog, TestCase, Turn
from .qt import QtCore, QtWidgets, load_webengine
from .render import build_document, markdown_to_html, mathjax_source, plain_to_html


@dataclass
class ViewOptions:
    show_system_instruction: bool = False
    show_prompts: bool = True
    show_expected: bool = True
    show_purpose: bool = True
    show_references: bool = False
    show_reasoning: bool = True
    show_reviews: bool = False
    show_metadata: bool = True
    render_markdown: bool = True


def _block(css_class: str, label: str, body_html: str) -> str:
    return (
        f'<div class="block {css_class}"><div class="label">{html.escape(label)}</div>'
        f'<div class="body">{body_html}</div></div>'
    )


def _empty(message: str) -> str:
    return f'<p class="empty">{html.escape(message)}</p>'


def _chip(text: str, css_class: str = "") -> str:
    classes = f"chip {css_class}".strip()
    return f'<span class="{classes}">{html.escape(text)}</span>'


class TranscriptRenderer:
    """HTML for the session header and a single-turn split inspector."""

    def __init__(self, options: ViewOptions | None = None) -> None:
        self.options = options or ViewOptions()

    def _body(self, text: str) -> str:
        if not (text or "").strip():
            return _empty("(empty)")
        return markdown_to_html(text) if self.options.render_markdown else plain_to_html(text)

    def _inline(self, text: str) -> str:
        if not self.options.render_markdown:
            return html.escape(text)
        rendered = markdown_to_html(text).strip()
        if rendered.startswith("<p>") and rendered.endswith("</p>"):
            inner = rendered[3:-4]
            if "<p>" not in inner:
                return inner
        return rendered

    def header(self, log: RunLog, case: TestCase | None) -> str:
        model = log.model_metadata
        chips = [
            _chip(log.status, f"status-{log.status.lower()}"),
            _chip(model.label or "unknown model"),
            _chip(f"run {log.run_index}"),
            _chip(f"{log.answered_turns}/{log.evaluation_summary.total_turns} answered"),
        ]
        if log.test_case.domain:
            chips.append(_chip(log.test_case.domain))
        if self.options.show_metadata:
            chips.append(_chip(f"temp {model.temperature}"))
            if model.max_tokens is not None:
                chips.append(_chip(f"max_tokens {model.max_tokens}"))
            if model.thinking_budget_allocated:
                chips.append(_chip(f"think budget {model.thinking_budget_allocated}"))
            usage = log.usage_totals
            chips.append(_chip(f"in {usage.input_tokens} / out {usage.output_tokens}"))
            if usage.cached_tokens:
                chips.append(_chip(f"cached {usage.cached_tokens}"))

        title = log.test_case.case_title or log.case_id
        subtitle = [log.case_id, log.run_id]
        if log.test_case.lean_file:
            subtitle.append(log.test_case.lean_file)

        pieces = [
            '<div class="session-header">',
            f"<h1>{html.escape(title)}</h1>",
            f'<div class="meta">{html.escape(" · ".join(subtitle))}</div>',
            f'<div class="meta">{" ".join(chips)}</div>',
            "</div>",
        ]
        if self.options.show_system_instruction and case and case.system_prompt:
            pieces.append(_block("system", "System instruction", self._body(case.system_prompt)))
        return "".join(pieces)

    def inspector(self, turn: ConversationTurn, spec_turn: Turn | None, case: TestCase | None) -> str:
        purpose = spec_turn.purpose if spec_turn else ""
        oracle = turn.oracle_theorem_ref or (
            case.oracle_theorem_for(turn.turn_id) if case else None
        )
        ground = turn.evaluation.expected_answer_lean
        if ground is None and spec_turn and spec_turn.expected_answer:
            ground = spec_turn.expected_answer.value
        answer_type = turn.evaluation.expected_answer_type or (
            spec_turn.expected_answer.answer_type
            if spec_turn and spec_turn.expected_answer
            else ""
        )
        undetermined = turn.evaluation.is_undetermined

        left = [
            f'<div class="pane-title">Turn {turn.turn_id}'
            + (f" · {html.escape(turn.turn_type)}" if turn.turn_type else "")
            + "</div>",
        ]
        if purpose and self.options.show_purpose:
            left.append(f'<div class="purpose">{html.escape(purpose)}</div>')
        if self.options.show_prompts:
            left.append(_block("user", "Ingested prompt", self._body(turn.prompt.content)))
        left.append(
            _block(
                "oracle",
                "Lean theorem reference",
                html.escape(oracle) if oracle else _empty("No oracle theorem paired with this turn."),
            )
        )
        ground_class = "expected undetermined" if undetermined else "expected"
        left.append(
            _block(
                ground_class,
                f"Lean ground truth ({answer_type})" if answer_type else "Lean ground truth",
                self._body(ground) if ground else _empty("No target value."),
            )
        )

        usage = turn.response.usage
        telemetry = [
            _chip(f"{turn.response.latency_ms} ms") if turn.response.latency_ms is not None else "",
            _chip(turn.response.finish_reason) if turn.response.finish_reason else "",
            _chip(f"in {usage.input_tokens}") if usage.input_tokens else "",
            _chip(f"out {usage.output_tokens}") if usage.output_tokens else "",
            _chip(f"cached {usage.cached_tokens}") if usage.cached_tokens else "",
        ]
        right = [
            '<div class="pane-title">Model completion</div>',
            f'<div class="meta">{" ".join(chip for chip in telemetry if chip)}</div>',
            _block(
                "output",
                "Raw completion",
                self._body(turn.response.content)
                if turn.response.content
                else _empty("Not executed."),
            ),
        ]
        if self.options.show_reasoning and turn.response.thinking_content:
            right.append(
                "<details class='thinking' open>"
                "<summary>Thinking content</summary>"
                f"{self._body(turn.response.thinking_content)}"
                "</details>"
            )
        elif self.options.show_reasoning:
            right.append(
                "<details class='thinking'><summary>Thinking content</summary>"
                f"{_empty('None recorded.')}</details>"
            )

        if self.options.show_references and spec_turn and spec_turn.references:
            left.append(_block("references", "References", _references_html(spec_turn)))

        return (
            '<div class="inspector">'
            f'<div class="pane left">{"".join(left)}</div>'
            f'<div class="pane right">{"".join(right)}</div>'
            "</div>"
        )

    def render(
        self,
        log: RunLog | None,
        case: TestCase | None = None,
        *,
        turn_id: int | None = None,
    ) -> str:
        if log is None:
            return build_document(
                '<div class="session-header"><h1>No session selected</h1>'
                '<div class="meta">Pick a run from the tree on the left.</div></div>',
                with_mathjax=False,
            )
        body = [self.header(log, case)]
        turn = log.turn(turn_id) if turn_id is not None else None
        if turn is None and log.conversation:
            turn = log.conversation[0]
        if turn is None:
            body.append(_empty("This run log contains no turns."))
        else:
            spec_turn = case.turn(turn.turn_id) if case else None
            body.append(self.inspector(turn, spec_turn, case))
        return build_document("".join(body))


def _references_html(spec_turn: Turn) -> str:
    items = []
    for reference in spec_turn.references or []:
        parts = [f"<b>{html.escape(reference.reference_id)}</b>"]
        if reference.citation:
            parts.append(html.escape(reference.citation))
        items.append(f"<li>{' — '.join(parts)}</li>")
    return f"<ul>{''.join(items)}</ul>" if items else _empty("No references.")


class TranscriptView(QtWidgets.QWidget):
    """Header + turn picker + split inspector."""

    def __init__(self, parent: QtWidgets.QWidget | None = None) -> None:
        super().__init__(parent)
        self.renderer = TranscriptRenderer()
        self._log: RunLog | None = None
        self._case: TestCase | None = None
        self._turn_id: int | None = None

        view_cls, settings_cls = load_webengine()
        self.uses_webengine = view_cls is not None

        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        bar = QtWidgets.QHBoxLayout()
        bar.setContentsMargins(12, 8, 12, 8)
        bar.addWidget(QtWidgets.QLabel("Turn", self))
        self.turn_box = QtWidgets.QComboBox(self)
        self.turn_box.currentIndexChanged.connect(self._on_turn_changed)
        bar.addWidget(self.turn_box, stretch=1)
        self.prev_btn = QtWidgets.QPushButton("←", self)
        self.prev_btn.clicked.connect(lambda: self.step_turn(-1))
        self.next_btn = QtWidgets.QPushButton("→", self)
        self.next_btn.clicked.connect(lambda: self.step_turn(1))
        bar.addWidget(self.prev_btn)
        bar.addWidget(self.next_btn)
        layout.addLayout(bar)

        if view_cls is not None:
            self._view = view_cls(self)
            if settings_cls is not None:
                settings = self._view.settings()
                settings.setAttribute(settings_cls.WebAttribute.ShowScrollBars, True)
                settings.setAttribute(
                    settings_cls.WebAttribute.LocalContentCanAccessRemoteUrls, True
                )
                settings.setAttribute(
                    settings_cls.WebAttribute.LocalContentCanAccessFileUrls, True
                )
        else:
            self._view = QtWidgets.QTextBrowser(self)
            self._view.setOpenExternalLinks(True)
            self._view.setLineWrapMode(QtWidgets.QTextEdit.LineWrapMode.WidgetWidth)
        layout.addWidget(self._view, stretch=1)

    @property
    def options(self) -> ViewOptions:
        return self.renderer.options

    def set_options(self, options: ViewOptions) -> None:
        self.renderer.options = options
        self.refresh()

    def show_session(self, log: RunLog | None, case: TestCase | None = None) -> None:
        self._log, self._case = log, case
        self._populate_turns()
        self.refresh()

    def _populate_turns(self) -> None:
        self.turn_box.blockSignals(True)
        self.turn_box.clear()
        if self._log is None:
            self._turn_id = None
            self.turn_box.blockSignals(False)
            return
        for turn in self._log.conversation:
            label = f"{turn.turn_id}  ·  {turn.turn_type}" if turn.turn_type else str(turn.turn_id)
            self.turn_box.addItem(label, turn.turn_id)
        self._turn_id = self._log.conversation[0].turn_id if self._log.conversation else None
        self.turn_box.blockSignals(False)

    def _on_turn_changed(self, index: int) -> None:
        if index < 0:
            return
        self._turn_id = self.turn_box.itemData(index)
        self.refresh()

    def step_turn(self, delta: int) -> None:
        index = self.turn_box.currentIndex() + delta
        if 0 <= index < self.turn_box.count():
            self.turn_box.setCurrentIndex(index)

    def refresh(self) -> None:
        document = self.renderer.render(self._log, self._case, turn_id=self._turn_id)
        if self.uses_webengine:
            base = QtCore.QUrl.fromLocalFile(f"{paths.PROJECT_ROOT}/")
            self._view.setHtml(document, base)
        else:
            self._view.setHtml(document)

    def backend_description(self) -> str:
        if not self.uses_webengine:
            return "QTextBrowser (LaTeX shown as source — install PySide6-Addons for MathJax)"
        _url, is_local = mathjax_source()
        return f"QtWebEngine + MathJax ({'local bundle' if is_local else 'CDN'})"

    def current_text(self) -> str:
        if self._log is None:
            return ""
        return "\n\n".join(
            f"### Turn {turn.turn_id}\n{turn.response.content}"
            for turn in self._log.conversation
        )
