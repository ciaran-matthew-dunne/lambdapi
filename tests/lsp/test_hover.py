"""Hover tests."""

import unittest

from .base import LSPTestCase, requires_stdlib


def _hover_text(result):
    """Extract the hover markdown/text from a hover response."""
    if result is None:
        return None
    contents = result.get("contents")
    if contents is None:
        return None
    if isinstance(contents, dict):
        return contents.get("value", "")
    if isinstance(contents, list):
        return "\n".join(
            c.get("value", c) if isinstance(c, dict) else str(c)
            for c in contents)
    return str(contents)


class TestHoverBasic(LSPTestCase):
    """Hover works on uses of a symbol (the RangeMap tracks uses)."""

    def test_hover_on_use_of_symbol(self):
        uri, _text, src, _diags = self.open_fixture("simple.lp")
        # Use of `zero` in `rule double zero ↪ zero;` — its type is Nat.
        line, col = src.find(r"rule double zero", "zero")
        result = self.server.hover(uri, line, col)
        text = _hover_text(result)
        self.assertIsNotNone(text, "hover on use of zero should not be null")
        # In either plain or rich mode, the type string "Nat" should appear.
        self.assertIn("Nat", text)

    def test_hover_on_blank_position_returns_null(self):
        uri, _text, _src, _diags = self.open_fixture("simple.lp")
        # Col 8 of "constant symbol Nat : TYPE;" is the space between
        # `constant` and `symbol` — no token there.
        result = self.server.hover(uri, 0, 8)
        self.assertIsNone(result,
            f"hover on whitespace should be null; got {result!r}")


class TestHoverPlainString(LSPTestCase):
    """Upstream-compatible hover: [contents] is a plain string carrying
    the type of the hovered symbol. Guards against accidental markdown
    divergence that VSCode/Emacs clients haven't had to handle."""

    def test_contents_is_plain_string(self):
        uri, _text, src, _ = self.open_fixture("simple.lp")
        line, col = src.find(r"rule double zero", "zero")
        result = self.server.hover(uri, line, col)
        self.assertIsNotNone(result)
        contents = result.get("contents")
        self.assertIsInstance(contents, str,
            f"contents must be a plain string; "
            f"got {type(contents).__name__}: {contents!r}")


class TestHoverTacticKeyword(LSPTestCase):
    """Inside a proof, hovering a tactic keyword shows the tactic's
    documentation; outside a proof, tactic names are not special."""

    PROOF = (
        "constant symbol Nat : TYPE;\n"
        "constant symbol zero : Nat;\n"
        "symbol triv : Nat → Nat ≔\n"
        "begin\n"
        "  assume n;\n"
        "  refine n;\n"
        "end;\n"
    )

    def test_hover_on_tactic_keyword_in_proof(self):
        uri, _src, _ = self.open_text("prf.lp", self.PROOF)
        # Line 5 is "  refine n;" — cols 2..7 are `refine`.
        text = _hover_text(self.server.hover(uri, 5, 3))
        self.assertIsNotNone(text,
            "hover on a tactic keyword inside a proof should document it")
        self.assertIn("goal", text,
            f"tactic documentation should describe the tactic; got {text!r}")

    def test_hover_on_hypothesis_in_proof(self):
        """After `assume n`, hovering the use of `n` should show its
        type (hypotheses are proof-local: not symbols, not in the
        identifier RangeMap)."""
        uri, _src, _ = self.open_text("prf.lp", self.PROOF)
        # Line 5 is "  refine n;" — col 9 is `n`.
        text = _hover_text(self.server.hover(uri, 5, 9))
        self.assertIsNotNone(text,
            "hover on a hypothesis should show its type")
        self.assertIn("Nat", text,
            f"hypothesis `n` has type Nat; got {text!r}")


class TestHoverCommandKeywords(LSPTestCase):
    """Command keywords and symbol modifiers are documented on hover,
    anywhere in a document."""

    def test_hover_on_symbol_command(self):
        uri, _text, src, _ = self.open_fixture("simple.lp")
        line, col = src.find(r"constant symbol Nat", "symbol")
        text = _hover_text(self.server.hover(uri, line, col))
        self.assertIsNotNone(text, "hover on `symbol` should document it")
        self.assertIn("Declares or defines", text)

    def test_hover_on_constant_modifier(self):
        uri, _text, src, _ = self.open_fixture("simple.lp")
        line, col = src.find(r"constant symbol Nat", "constant")
        text = _hover_text(self.server.hover(uri, line, col))
        self.assertIsNotNone(text, "hover on `constant` should document it")
        self.assertIn("modifier", text)

    def test_hover_on_rule_command(self):
        uri, _text, src, _ = self.open_fixture("simple.lp")
        line, col = src.find(r"^rule double", "rule")
        text = _hover_text(self.server.hover(uri, line, col))
        self.assertIsNotNone(text, "hover on `rule` should document it")
        self.assertIn("rewriting", text)


class TestHoverUncheckedRegion(LSPTestCase):
    """Hover falls back to the in-scope symbol table for text the
    checker never reached (e.g. past a parse error), where the
    RangeMap has no entries."""

    TEXT = (
        "constant symbol Nat : TYPE;\n"
        "constant symbol zero : Nat;\n"
        "symbol ;\n"                     # parse error: no name
        "symbol later : Nat;\n"          # never parsed / checked
    )

    def test_hover_after_parse_error_uses_symbol_table(self):
        uri, _src, diags = self.open_text("hov_err.lp", self.TEXT)
        self.assertTrue(self.errors(diags),
            "fixture should produce a parse error")
        # `Nat` on the last line is past the error: not in the RangeMap,
        # but in scope from the checked prefix.
        col = self.TEXT.splitlines()[3].index("Nat")
        text = _hover_text(self.server.hover(uri, 3, col))
        self.assertIsNotNone(text,
            "hover should fall back to the in-scope symbol table")
        self.assertIn("TYPE", text)


class TestHoverStdlib(LSPTestCase):

    @requires_stdlib
    def test_hover_on_stdlib_symbol(self):
        uri, _text, src, _ = self.open_fixture("imports.lp")
        line, col = src.find(r"symbol double :", r"ℕ")
        text = _hover_text(self.server.hover(uri, line, col))
        self.assertIsNotNone(text,
            "hover on stdlib type should return content, got null")


if __name__ == "__main__":
    unittest.main()
