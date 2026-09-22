"""Markdown + LaTeX rendering for model outputs.

Model answers in this project mix prose, Lean code fences and mathematics, so the
renderer has to keep all three intact:

1. The source is tokenised so that fenced blocks and inline code are recognised
   *before* math is, and never rewritten.
2. Math spans (``$$…$$``, ``\\[…\\]``, ``\\(…\\)`` and single ``$…$``) are swapped
   for opaque placeholders, so the Markdown converter cannot mangle ``_``, ``*``
   or ``\\`` inside them.
3. Markdown is converted to HTML, then the placeholders are restored with their
   delimiters and HTML-escaped bodies, ready for MathJax.

MathJax is loaded from ``assets/mathjax/tex-mml-chtml.js`` when vendored locally,
otherwise from the CDN; :func:`mathjax_source` reports which one is in use so the
GUI can tell the user when LaTeX needs a network connection.
"""

from __future__ import annotations

import html
import re
from pathlib import Path

from .. import paths

MATHJAX_CDN = "https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"
_LOCAL_MATHJAX_CANDIDATES = (
    paths.PROJECT_ROOT / "assets" / "mathjax" / "tex-mml-chtml.js",
    Path(__file__).resolve().parent / "assets" / "mathjax" / "tex-mml-chtml.js",
)

# Opaque to Markdown (no special characters) and vanishingly unlikely in prose.
_PLACEHOLDER = "@@EPICONMATH{index}ENDMATH@@"

# Order matters: code constructs are matched first so `$` inside them is literal.
_TOKEN_PATTERN = re.compile(
    r"""
    (?P<fence>^[ \t]*(?P<ticks>`{3,}|~{3,})[^\n]*\n.*?^[ \t]*(?P=ticks)[ \t]*$)
  | (?P<inline_code>`+[^`\n]*?`+)
  | (?P<display_dollar>\$\$.+?\$\$)
  | (?P<display_bracket>\\\[.+?\\\])
  | (?P<inline_paren>\\\(.+?\\\))
  | (?P<inline_dollar>(?<![\\$])\$(?!\s)(?:[^$\n\\]|\\.)+?(?<!\s)\$(?!\$))
    """,
    re.DOTALL | re.MULTILINE | re.VERBOSE,
)

_MATH_GROUPS = ("display_dollar", "display_bracket", "inline_paren", "inline_dollar")
#: Only these delimiters can produce a centred block, and only when alone on a line.
_DISPLAY_GROUPS = frozenset({"display_dollar", "display_bracket"})
#: Delimiter width per group, used to recover the expression body.
_DELIMITER_WIDTHS = {
    "display_dollar": 2,
    "display_bracket": 2,
    "inline_paren": 2,
    "inline_dollar": 1,
}


def mathjax_source() -> tuple[str, bool]:
    """``(url, is_local)`` for the MathJax bundle."""
    for candidate in _LOCAL_MATHJAX_CANDIDATES:
        if candidate.is_file():
            return candidate.resolve().as_uri(), True
    return MATHJAX_CDN, False


def _stands_alone(text: str, start: int, end: int) -> bool:
    """Whether the span at ``[start:end)`` is the only content on its line."""
    line_start = text.rfind("\n", 0, start) + 1
    if text[line_start:start].strip():
        return False
    line_end = text.find("\n", end)
    tail = text[end:] if line_end == -1 else text[end:line_end]
    return not tail.strip()


def _extract_math(text: str) -> tuple[str, list[tuple[str, bool]]]:
    """Replace math with placeholders, recording ``(span, is_display)`` for each.

    Display vs inline is decided by *position*, not by the delimiter: these test
    cases mandate ``$$…$$`` for every expression, including mid-sentence ones, so
    treating every ``$$`` as a centred block would break each prompt into
    fragments. Only a span alone on its line is rendered as display math.
    """
    spans: list[tuple[str, bool]] = []

    def substitute(match: re.Match[str]) -> str:
        if match.group("fence") is not None or match.group("inline_code") is not None:
            # Code is reproduced verbatim: a `$` in there is a dollar sign.
            return match.group(0)
        for group in _MATH_GROUPS:
            value = match.group(group)
            if value is not None:
                display = group in _DISPLAY_GROUPS and _stands_alone(
                    text, match.start(group), match.end(group)
                )
                width = _DELIMITER_WIDTHS[group]
                spans.append((value[width:-width], display))
                return _PLACEHOLDER.format(index=len(spans) - 1)
        return match.group(0)

    return _TOKEN_PATTERN.sub(substitute, text), spans


def _restore_math(html_text: str, spans: list[tuple[str, bool]]) -> str:
    """Re-insert each expression with canonical delimiters.

    The source delimiters are discarded and rewritten as ``\\(…\\)`` or ``\\[…\\]``
    so that MathJax typesets what this module decided: a ``$$…$$`` written
    mid-sentence would otherwise be forced into a centred block by MathJax's own
    delimiter configuration, regardless of the CSS class.
    """
    for index, (body, is_display) in enumerate(spans):
        placeholder = _PLACEHOLDER.format(index=index)
        # MathJax reads the text content, so the body must be HTML-escaped while
        # the delimiters stay literal.
        escaped = html.escape(body, quote=False)
        opener, closer = ("\\[", "\\]") if is_display else ("\\(", "\\)")
        css_class = "math-display" if is_display else "math-inline"
        html_text = html_text.replace(
            placeholder, f'<span class="{css_class}">{opener}{escaped}{closer}</span>'
        )
    return html_text


def markdown_to_html(text: str) -> str:
    """Convert Markdown (with embedded LaTeX) to an HTML fragment."""
    if not text:
        return ""

    protected, spans = _extract_math(text)

    try:
        import markdown

        body = markdown.markdown(
            protected,
            extensions=["fenced_code", "tables", "sane_lists", "codehilite", "admonition"],
            extension_configs={"codehilite": {"guess_lang": False, "noclasses": True}},
            output_format="html",
        )
    except ImportError:
        # Degrade to preformatted text rather than failing to show the output.
        body = f"<pre class='plain'>{html.escape(protected)}</pre>"

    return _restore_math(body, spans)


def plain_to_html(text: str) -> str:
    """Escape *text* and preserve its line breaks, for prompts and raw blocks."""
    return f"<pre class='plain'>{html.escape(text or '')}</pre>"


STYLESHEET = """
:root { color-scheme: light dark; }
body {
  margin: 0;
  padding: 18px 22px 64px;
  background: #ffffff;
  color: #1b1f23;
  font-family: "Segoe UI", -apple-system, "Helvetica Neue", Arial, sans-serif;
  font-size: 14px;
  line-height: 1.62;
}
h1, h2, h3, h4 { line-height: 1.3; margin: 1.2em 0 0.5em; }
h1 { font-size: 1.55em; } h2 { font-size: 1.32em; } h3 { font-size: 1.14em; }
p { margin: 0.65em 0; }
a { color: #0b62c4; }
code, pre { font-family: "Cascadia Mono", Consolas, "SF Mono", monospace; font-size: 0.92em; }
code { background: #f1f3f5; padding: 0.12em 0.34em; border-radius: 4px; }
pre {
  background: #f6f8fa; border: 1px solid #e2e6ea; border-radius: 8px;
  padding: 12px 14px; overflow-x: auto; white-space: pre-wrap; word-wrap: break-word;
}
pre code { background: none; padding: 0; }
pre.plain { white-space: pre-wrap; font-family: inherit; font-size: 1em; background: none;
            border: none; padding: 0; margin: 0; }
blockquote { margin: 0.7em 0; padding: 0.2em 1em; border-left: 3px solid #d3d8de; color: #4b5563; }
table { border-collapse: collapse; margin: 0.8em 0; }
th, td { border: 1px solid #dfe3e8; padding: 6px 10px; text-align: left; }
th { background: #f3f5f7; }
hr { border: none; border-top: 1px solid #e5e7eb; margin: 1.4em 0; }

/* session header */
.session-header { border-bottom: 2px solid #e5e7eb; padding-bottom: 12px; margin-bottom: 4px; }
.session-header h1 { margin: 0 0 6px; }
.meta { color: #57606a; font-size: 12.5px; }
/* Not scoped to .meta: the same pill is used in turn headers. */
.chip {
  display: inline-block; background: #eef1f4; border-radius: 999px;
  padding: 2px 10px; margin: 2px 6px 2px 0; white-space: nowrap;
  font-weight: 400; color: #3d444d;
}
.chip.status-completed { background: #dcfce7; color: #14532d; }
.chip.status-failed    { background: #fee2e2; color: #7f1d1d; }
.chip.status-partial   { background: #fef3c7; color: #78350f; }
.chip.status-skipped   { background: #e5e7eb; color: #374151; }
.chip.verdict-correct   { background: #dcfce7; color: #14532d; font-weight: 600; }
.chip.verdict-incorrect { background: #fee2e2; color: #7f1d1d; font-weight: 600; }
.chip.verdict-unscored  { background: #e5e7eb; color: #374151; }

/* turns */
.turn { border-top: 1px solid #eceff2; padding-top: 18px; margin-top: 22px; }
.turn-title { font-weight: 600; font-size: 13px; letter-spacing: 0.02em;
              text-transform: uppercase; color: #57606a; margin-bottom: 10px; }
.turn-chips { margin-left: 10px; text-transform: none; letter-spacing: 0; }
.purpose { color: #6b7280; font-size: 12.5px; font-style: italic; margin: -4px 0 10px; }
.review { border-left: 3px solid #6366f1; padding: 2px 0 2px 14px; margin: 14px 0; }
.review-head { font-weight: 600; }
.review ul { margin: 0.4em 0; padding-left: 1.2em; }
.block { margin: 12px 0 18px; }
.block > .label {
  font-size: 11.5px; font-weight: 700; letter-spacing: 0.06em; text-transform: uppercase;
  color: #6b7280; margin-bottom: 6px;
}
.block > .body {
  border-left: 3px solid #d7dce2; padding: 2px 0 2px 14px;
}
.block.user > .body      { border-left-color: #9ca3af; }
.block.output > .body    { border-left-color: #2563eb; }
.block.expected > .body  { border-left-color: #16a34a; }
.block.reasoning > .body { border-left-color: #a855f7; color: #4b5563; }
.block.error > .body     { border-left-color: #dc2626; color: #991b1b; }
.block.system > .body    { border-left-color: #f59e0b; }
.block.flags > .body     { border-left-color: #f97316; }
.block.notes > .body     { border-left-color: #0ea5e9; }
.block.comments > .body  { border-left-color: #94a3b8; color: #4b5563; }
.block.references > .body { border-left-color: #64748b; font-size: 12.5px; }
.block.oracle > .body    { border-left-color: #0ea5e9; font-family: "Cascadia Mono", Consolas, monospace; }
.block.expected.undetermined > .body { background: #fff8e1; }
.inspector {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 18px;
  align-items: start;
  margin-top: 12px;
}
.pane { min-width: 0; }
.pane-title { font-weight: 700; font-size: 14px; margin: 0 0 8px; }
.pane.left { padding-right: 8px; border-right: 1px solid #eceff2; }
details.thinking {
  margin: 12px 0 18px;
  border: 1px solid #e2e6ea;
  border-radius: 8px;
  padding: 8px 12px;
}
details.thinking > summary {
  cursor: pointer;
  font-size: 11.5px;
  font-weight: 700;
  letter-spacing: 0.06em;
  text-transform: uppercase;
  color: #6b7280;
}
@media (max-width: 900px) {
  .inspector { grid-template-columns: 1fr; }
  .pane.left { border-right: none; padding-right: 0; }
}
.empty { color: #9ca3af; font-style: italic; }
.math-display { display: block; margin: 0.4em 0; overflow-x: auto; }

@media (prefers-color-scheme: dark) {
  body { background: #101418; color: #e6edf3; }
  a { color: #6cb6ff; }
  code { background: #1c2128; }
  pre { background: #161b22; border-color: #262c34; }
  th { background: #1c2128; }
  th, td { border-color: #2d333b; }
  .meta, .turn-title, .block > .label { color: #8b949e; }
  .chip { background: #21262d; color: #c9d1d9; }
  .session-header, .turn, .pane.left { border-color: #262c34; }
  details.thinking { border-color: #262c34; }
  .block.expected.undetermined > .body { background: #3a2e14; }
  blockquote { border-left-color: #30363d; color: #9da7b3; }
}
"""

# Only canonical delimiters are recognised: _restore_math has already decided
# display vs inline and rewritten every expression accordingly, so `$$` and `$`
# must not be reinterpreted here (a stray `$` in prose is then just a dollar sign).
_MATHJAX_CONFIG = """
window.MathJax = {
  tex: {
    inlineMath: [['\\\\(', '\\\\)']],
    displayMath: [['\\\\[', '\\\\]']],
    processEscapes: true,
    processEnvironments: true,
    tags: 'ams'
  },
  options: {
    skipHtmlTags: ['script', 'noscript', 'style', 'textarea', 'pre', 'code'],
    ignoreHtmlClass: 'no-mathjax'
  },
  svg: { fontCache: 'global' }
};
"""


def build_document(body_html: str, *, with_mathjax: bool = True) -> str:
    """Wrap an HTML fragment in a complete document with styles and MathJax."""
    mathjax = ""
    if with_mathjax:
        url, _is_local = mathjax_source()
        mathjax = (
            f"<script>{_MATHJAX_CONFIG}</script>\n"
            f'<script id="MathJax-script" async src="{url}"></script>'
        )

    return (
        "<!DOCTYPE html>\n<html><head><meta charset='utf-8'>"
        "<meta name='viewport' content='width=device-width, initial-scale=1'>"
        f"<style>{STYLESHEET}</style>{mathjax}</head>"
        f"<body>{body_html}</body></html>"
    )
