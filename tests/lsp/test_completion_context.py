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


if __name__ == "__main__":
    unittest.main()
