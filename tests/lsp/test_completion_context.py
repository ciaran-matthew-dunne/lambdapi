"""Context-aware completion: module paths, qualified names, argument
keywords. The context is detected lexically from the line before the
cursor, so it also works while the text does not parse."""

import unittest

from .base import LSPTestCase, requires_stdlib


def _complete(srv, uri, line, character, context=None):
    params = {"textDocument": {"uri": uri},
              "position": {"line": line, "character": character}}
    if context is not None:
        params["context"] = context
    return srv.request("textDocument/completion", params)


def _labels(r):
    return {i["label"] for i in (r or {}).get("items", [])}


class TestRequirePathCompletion(LSPTestCase):
    """After `require`/`open`, complete module paths from the library
    mappings, replacing the typed partial path via a textEdit."""

    def test_require_offers_local_modules(self):
        uri, _src, _ = self.open_text("req1.lp", "require test.\n")
        r = _complete(self.server, uri, 0, 13)
        by_label = {i["label"]: i for i in r.get("items", [])}
        self.assertIn("test.simple", by_label,
            f"local module should be offered; got "
            f"{sorted(by_label)[:10]}")
        item = by_label["test.simple"]
        self.assertEqual(item.get("kind"), 9)      # Module
        te = item.get("textEdit")
        self.assertIsNotNone(te, "path items need a textEdit: '.' is "
            "not a word character, a label would insert after the dot")
        self.assertEqual(te["newText"], "test.simple")
        self.assertEqual(te["range"]["start"],
                         {"line": 0, "character": 8})
        self.assertEqual(te["range"]["end"],
                         {"line": 0, "character": 13})

    def test_require_open_offers_paths_only(self):
        uri, _src, _ = self.open_text("req2.lp", "require open test.\n")
        labels = _labels(_complete(self.server, uri, 0, 18))
        self.assertIn("test.simple", labels)
        self.assertNotIn("symbol", labels,
            "a path position should not offer command keywords")

    def test_open_offers_paths(self):
        uri, _src, _ = self.open_text("req3.lp", "open test.\n")
        self.assertIn("test.simple",
                      _labels(_complete(self.server, uri, 0, 10)))

    def test_partial_path_filters(self):
        uri, _src, _ = self.open_text("req4.lp", "require test.sim\n")
        labels = _labels(_complete(self.server, uri, 0, 16))
        self.assertIn("test.simple", labels)
        self.assertNotIn("test.proof", labels,
            "candidates should be filtered by the typed prefix")

    @requires_stdlib
    def test_require_offers_stdlib(self):
        uri, _src, _ = self.open_text("req5.lp", "require Stdlib.\n")
        self.assertIn("Stdlib.Nat",
                      _labels(_complete(self.server, uri, 0, 15)))


class TestQualifiedCompletion(LSPTestCase):
    """After `M.` in term position, complete the non-private symbols
    of the (required) module M, resolving `require as` aliases, plus
    the next segments of loaded module paths."""

    def test_qualified_offers_module_symbols(self):
        uri, _src, _ = self.open_text("qual1.lp",
            "require test.simple;\n"
            "symbol z : test.simple.\n")
        r = _complete(self.server, uri, 1, 23)
        labels = _labels(r)
        for name in ("Nat", "zero", "succ", "double"):
            self.assertIn(name, labels,
                f"{name!r} of test.simple should be offered; "
                f"got {sorted(labels)[:10]}")

    def test_qualified_resolve_attaches_type(self):
        uri, _src, _ = self.open_text("qual2.lp",
            "require test.simple;\n"
            "symbol z : test.simple.\n")
        r = _complete(self.server, uri, 1, 23)
        item = next(i for i in r.get("items", [])
                    if i["label"] == "succ")
        resolved = self.server.resolve_completion(item)
        self.assertIn("Nat", resolved.get("detail", ""),
            f"resolved detail should carry the type; got {resolved!r}")

    def test_alias_resolves(self):
        uri, _src, _ = self.open_text("qual3.lp",
            "require test.simple as S;\n"
            "symbol z : S.\n")
        self.assertIn("Nat", _labels(_complete(self.server, uri, 1, 13)))

    def test_private_symbols_excluded(self):
        uri, _src, _ = self.open_text("qual4.lp",
            "require test.modifiers;\n"
            "symbol z : test.modifiers.\n")
        labels = _labels(_complete(self.server, uri, 1, 26))
        self.assertIn("inj", labels)
        self.assertNotIn("priv", labels,
            "private symbols must not be offered outside their module")

    def test_intermediate_segment_offered(self):
        """`test.` in term position: `test` is not itself a module,
        but loaded paths extend it — offer the next segment."""
        uri, _src, _ = self.open_text("qual5.lp",
            "require test.simple;\n"
            "symbol z : test.\n")
        r = _complete(self.server, uri, 1, 16)
        by_label = {i["label"]: i for i in r.get("items", [])}
        self.assertIn("simple", by_label,
            f"next path segment should be offered; "
            f"got {sorted(by_label)[:10]}")
        self.assertEqual(by_label["simple"].get("kind"), 9)  # Module


class TestDotTrigger(LSPTestCase):
    """A "."-triggered request outside the dot-aware contexts must
    return no items (e.g. after a number), while normal invocation at
    the same position still completes."""

    def test_dot_trigger_outside_context_is_quiet(self):
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        r = _complete(self.server, uri, 5, 0,
                      context={"triggerKind": 2, "triggerCharacter": "."})
        self.assertEqual(r.get("items"), [],
            "dot-trigger outside path/qualified contexts must be quiet")

    def test_invoked_at_same_position_completes(self):
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        r = _complete(self.server, uri, 5, 0,
                      context={"triggerKind": 1})
        self.assertIn("double", _labels(r))


class TestArgumentContexts(LSPTestCase):
    """Focused completions in argument positions: notation kinds,
    associativity sides, flag names and switches; hypotheses ranked
    first in hypothesis-taking tactic arguments."""

    def test_notation_arguments(self):
        uri, _src, _ = self.open_text("arg1.lp",
            "constant symbol Nat : TYPE;\nnotation Nat \n")
        labels = _labels(_complete(self.server, uri, 1, 13))
        for kw in ("infix", "prefix", "postfix", "quantifier"):
            self.assertIn(kw, labels,
                f"{kw!r} should be offered after `notation <id>`")
        self.assertNotIn("Nat", labels,
            "the notation-argument list should not offer symbols")

    def test_associativity_sides(self):
        uri, _src, _ = self.open_text("arg2.lp",
            "constant symbol Nat : TYPE;\nnotation Nat infix \n")
        labels = _labels(_complete(self.server, uri, 1, 19))
        self.assertIn("left", labels)
        self.assertIn("right", labels)
        self.assertNotIn("infix", labels)

    def test_flag_names(self):
        uri, _src, _ = self.open_text("arg3.lp", 'flag "\n')
        labels = _labels(_complete(self.server, uri, 0, 6))
        self.assertIn("print_implicits", labels,
            f"registered flags should be offered; got {sorted(labels)}")
        self.assertIn("eta_equality", labels)

    def test_flag_switch(self):
        uri, _src, _ = self.open_text("arg4.lp",
            'flag "print_implicits" \n')
        labels = _labels(_complete(self.server, uri, 0, 23))
        self.assertEqual(labels, {"on", "off"},
            f"after the flag string, only on/off; got {sorted(labels)}")

    def test_hypotheses_ranked_first_in_tactic_args(self):
        proof = (
            "constant symbol Nat : TYPE;\n"
            "symbol triv : Nat → Nat ≔\n"
            "begin\n"
            "  assume n;\n"
            "  apply n;\n"
            "end;\n"
        )
        uri, _src, _ = self.open_text("arg5.lp", proof)
        # Cursor after "  apply " (line 4, col 8).
        r = _complete(self.server, uri, 4, 8)
        n_item = next(i for i in r.get("items", [])
                      if i["label"] == "n")
        self.assertTrue(n_item.get("sortText", "").startswith("0"),
            f"hypothesis should rank first after `apply`; got {n_item!r}")

    def test_no_keywords_in_tactic_args(self):
        """The argument of a tactic is a term position: offering
        `have` (or any keyword) after `apply ` would be invalid."""
        proof = (
            "constant symbol Nat : TYPE;\n"
            "symbol triv : Nat → Nat ≔\n"
            "begin\n"
            "  assume n;\n"
            "  apply n;\n"
            "end;\n"
        )
        uri, _src, _ = self.open_text("arg6.lp", proof)
        labels = _labels(_complete(self.server, uri, 4, 8))
        for kw in ("have", "apply", "admitted", "print"):
            self.assertNotIn(kw, labels,
                f"{kw!r} is not valid in a tactic argument")
        self.assertIn("n", labels)
        self.assertIn("triv", labels,
            "in-scope symbols are valid tactic arguments")


if __name__ == "__main__":
    unittest.main()
