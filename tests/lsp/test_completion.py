"""Completion tests: symbols, proof-context tactic keywords, hypotheses,
and lazy detail via completionItem/resolve."""

import re
import unittest

from .base import LSPTestCase, REPO_ROOT


def _completion_request(srv, uri, line, character):
    return srv.request("textDocument/completion", {
        "textDocument": {"uri": uri},
        "position": {"line": line, "character": character},
    })


class TestCompletion(LSPTestCase):

    def test_in_scope_symbols_listed(self):
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        r = _completion_request(self.server, uri, 5, 0)
        items = r.get("items", [])
        labels = [i["label"] for i in items]
        for expected in ("Nat", "zero", "succ", "double"):
            self.assertIn(expected, labels,
                f"{expected!r} should appear in completion list")

    def test_symbol_items_omit_detail_but_carry_resolve_data(self):
        """Symbol detail is computed on [completionItem/resolve], not in
        the initial response. The initial response carries a [data] field
        pointing back at the symbol so resolve can look it up."""
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        r = _completion_request(self.server, uri, 5, 0)
        by_label = {i["label"]: i for i in r.get("items", [])}
        succ = by_label.get("succ")
        self.assertIsNotNone(succ)
        self.assertNotIn("detail", succ,
            f"detail should be attached lazily via resolve; got {succ!r}")
        data = succ.get("data")
        self.assertIsInstance(data, dict,
            f"symbol item needs a [data] field for resolve; got {succ!r}")
        # [data] is opaque to the client (the server reads it back on
        # resolve); only pin down what resolve relies on.
        self.assertEqual(data.get("kind"), "symbol")
        self.assertEqual(data.get("uri"), uri)

    def test_resolve_attaches_type_detail(self):
        """completionItem/resolve on a symbol item returns the same item
        with [detail] populated."""
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        r = _completion_request(self.server, uri, 5, 0)
        succ = next(i for i in r.get("items", []) if i["label"] == "succ")
        resolved = self.server.resolve_completion(succ)
        self.assertIsNotNone(resolved)
        self.assertIn("Nat", resolved.get("detail", ""),
            f"resolved detail should mention Nat; got {resolved!r}")

    def test_symbol_kinds_reflect_computation(self):
        """A symbol that computes (has a definition or rewrite rules) is
        Function (3); everything else — constructors, axioms, type
        formers — is Constant (21). The type's shape is deliberately
        not consulted: a type can normalize to a product without being
        one syntactically."""
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        r = _completion_request(self.server, uri, 5, 0)
        kinds = {i["label"]: i["kind"] for i in r.get("items", [])}
        self.assertEqual(kinds.get("double"), 3,  # has rewrite rules
            f"computing symbol should be Function (3); "
            f"got {kinds.get('double')}")
        for label in ("Nat", "zero", "succ"):     # no definition, no rules
            self.assertEqual(kinds.get(label), 21,
                f"non-computing symbol {label!r} should be Constant (21); "
                f"got {kinds.get(label)}")

    def test_no_ghost_symbols_in_completions(self):
        """Internal ghost symbols (unification-rule machinery such as
        `≡` and `;`) must not be offered as completions."""
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        r = _completion_request(self.server, uri, 5, 0)
        labels = {i["label"] for i in r.get("items", [])}
        leaked = {"≡", ";", "coerce"} & labels
        self.assertFalse(leaked,
            f"ghost symbols leaked into completions: {leaked}")

    def test_no_tactic_completions_outside_proof(self):
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        r = _completion_request(self.server, uri, 0, 0)
        labels = [i["label"] for i in r.get("items", [])]
        self.assertNotIn("refine", labels)
        self.assertNotIn("rewrite", labels)


class TestCompletionInProof(LSPTestCase):
    """Inside a begin..end block, tactic keywords + hypotheses appear."""

    PROOF = (
        "constant symbol Nat : TYPE;\n"
        "constant symbol zero : Nat;\n"
        "symbol triv : Nat \u2192 Nat \u2254\n"
        "begin\n"
        "  assume n;\n"
        "  refine n;\n"
        "end;\n"
    )

    def test_tactic_completions_in_proof(self):
        uri, _src, _ = self.open_text("prf.lp", self.PROOF)
        # Line 5 is "  refine n;" — cursor at col 0 is inside the proof.
        r = _completion_request(self.server, uri, 5, 0)
        labels = [i["label"] for i in r.get("items", [])]
        for kw in ("refine", "reflexivity", "apply", "assume",
                   "eval", "fail"):
            self.assertIn(kw, labels,
                f"{kw!r} should be offered inside a proof; got {labels[:8]}")

    def test_tactic_completions_carry_documentation(self):
        """Tactic items carry [documentation] so clients can show what
        the tactic does in the completion docs panel."""
        uri, _src, _ = self.open_text("prf.lp", self.PROOF)
        r = _completion_request(self.server, uri, 5, 0)
        refine = next(i for i in r.get("items", [])
                      if i["label"] == "refine")
        doc = refine.get("documentation", "")
        self.assertIn("goal", doc,
            f"refine's documentation should describe the tactic; "
            f"got {doc!r}")

    def test_hypothesis_completions_in_proof(self):
        """After `assume n`, the hypothesis `n` should appear as a
        completion with CompletionItemKind.Variable (6) and its type."""
        uri, _src, _ = self.open_text("prf.lp", self.PROOF)
        # Line 5 (`  refine n;`), col 0: after `assume n;` on line 4.
        r = _completion_request(self.server, uri, 5, 0)
        by_label = {i["label"]: i for i in r.get("items", [])}
        self.assertIn("n", by_label,
            f"hypothesis 'n' should appear; got {sorted(by_label)[:20]}")
        n_item = by_label["n"]
        self.assertEqual(n_item["kind"], 6,
            f"hypothesis kind should be Variable (6); got {n_item['kind']}")
        self.assertIn("Nat", n_item.get("detail", ""),
            f"hypothesis detail should carry its type; got {n_item!r}")


class TestSnippetSupport(LSPTestCase):
    """Tactic completions carry TextMate-style [insertText] /
    [insertTextFormat=2] when the client advertises snippetSupport,
    and omit them otherwise."""

    advertise_snippet_support = True

    PROOF = TestCompletionInProof.PROOF

    def test_tactic_with_arg_emits_snippet(self):
        uri, _src, _ = self.open_text("prf.lp", self.PROOF)
        r = _completion_request(self.server, uri, 5, 0)
        apply_item = next(i for i in r.get("items", [])
                          if i["label"] == "apply")
        self.assertEqual(apply_item.get("insertTextFormat"), 2,
            f"snippet format expected; got {apply_item!r}")
        self.assertIn("${1:", apply_item.get("insertText", ""),
            f"insertText should contain a tab-stop; got {apply_item!r}")


class TestMarkdownDocumentation(LSPTestCase):
    """When the client advertises markdown [documentationFormat],
    tactic docs are sent as MarkupContent so backticks render as
    code spans; otherwise they stay plain strings."""

    advertise_markdown_docs = True

    def test_tactic_documentation_is_markup_content(self):
        uri, _src, _ = self.open_text("prf.lp", TestCompletionInProof.PROOF)
        r = _completion_request(self.server, uri, 5, 0)
        refine = next(i for i in r.get("items", [])
                      if i["label"] == "refine")
        doc = refine.get("documentation")
        self.assertIsInstance(doc, dict,
            f"markdown-capable client should get MarkupContent; got {doc!r}")
        self.assertEqual(doc.get("kind"), "markdown")
        self.assertIn("`refine t`", doc.get("value", ""),
            "documentation should carry markdown code spans")


class TestNoSnippetSupport(LSPTestCase):
    """With snippetSupport off, tactic items have no [insertText]."""

    advertise_snippet_support = False

    def test_tactic_lacks_insertText(self):
        uri, _src, _ = self.open_text("prf.lp", TestCompletionInProof.PROOF)
        r = _completion_request(self.server, uri, 5, 0)
        apply_item = next(i for i in r.get("items", [])
                          if i["label"] == "apply")
        self.assertNotIn("insertText", apply_item,
            f"expected no insertText without snippetSupport; got {apply_item!r}")
        self.assertNotIn("insertTextFormat", apply_item)


class TestCompletionMidEdit(LSPTestCase):
    """Typing a partial tactic name breaks the parse of the enclosing
    command; proof-context completions must survive via the nodes of
    the last successful parse, and resync on the next clean parse."""

    BROKEN = (
        "constant symbol Nat : TYPE;\n"
        "constant symbol zero : Nat;\n"
        "symbol triv : Nat → Nat ≔\n"
        "begin\n"
        "  assume n;\n"
        "  re\n"                      # mid-word edit: parse error
        "  refine n;\n"
        "end;\n"
    )

    def test_proof_context_survives_broken_parse(self):
        uri, _src, _ = self.open_text("mid.lp", TestCompletionInProof.PROOF)
        self.server.did_change(uri, self.BROKEN, 2)
        notifs = self.server.drain_notifications(timeout=5.0)
        diags = self.server.extract_diagnostics(notifs, uri=uri)
        self.assertTrue(self.errors(diags),
            "the mid-word text should fail to parse")
        # Cursor right after the "re" being typed (line 5, col 4).
        r = _completion_request(self.server, uri, 5, 4)
        labels = {i["label"] for i in r.get("items", [])}
        self.assertIn("refine", labels,
            f"tactics must survive a mid-word edit; got {sorted(labels)[:10]}")
        self.assertIn("n", labels,
            "hypotheses must survive a mid-word edit")
        self.assertIn("zero", labels,
            "symbols checked before the breakage must still be offered")

    def test_context_resyncs_after_clean_parse(self):
        uri, _src, _ = self.open_text("mid2.lp", TestCompletionInProof.PROOF)
        self.server.did_change(uri, self.BROKEN, 2)
        self.server.drain_notifications(timeout=5.0)
        # Replace the proof by a plain definition: the text parses
        # again, so the retained proof context must be dropped.
        flat = (
            "constant symbol Nat : TYPE;\n"
            "constant symbol zero : Nat;\n"
            "symbol triv : Nat → Nat ≔ λ n, n;\n"
        )
        self.server.did_change(uri, flat, 3)
        self.server.drain_notifications(timeout=5.0)
        r = _completion_request(self.server, uri, 2, 0)
        labels = {i["label"] for i in r.get("items", [])}
        self.assertNotIn("refine", labels,
            "stale proof context must clear after a clean parse")


class TestTacticDocSync(LSPTestCase):
    """The completion list must cover every tactic documented in the
    manual. Extracts the ``name`` section headings from the tactic doc
    pages and checks each is offered inside a proof — catching drift
    when a tactic is added to the docs but not to the LSP."""

    DOC_FILES = ("tactics.rst", "tacticals.rst", "equality.rst")

    @classmethod
    def documented_tactics(cls):
        heading = re.compile(r"^``([a-z_0-9]+)(?: <[^>]+>)?``$")
        underline = re.compile(r"^[-~^\"'=+#*]{3,}$")
        names = set()
        for fname in cls.DOC_FILES:
            lines = (REPO_ROOT / "doc" / fname).read_text().splitlines()
            for i in range(len(lines) - 1):
                m = heading.match(lines[i].strip())
                if m and underline.match(lines[i + 1].strip()):
                    names.add(m.group(1))
        return names

    def test_documented_tactics_are_offered(self):
        documented = self.documented_tactics()
        self.assertGreaterEqual(len(documented), 20,
            f"suspiciously few tactic headings extracted from "
            f"{self.DOC_FILES}: {sorted(documented)}")
        uri, _src, _ = self.open_text("sync.lp", TestCompletionInProof.PROOF)
        r = _completion_request(self.server, uri, 5, 0)
        labels = {i["label"] for i in r.get("items", [])}
        missing = documented - labels
        self.assertFalse(missing,
            f"tactics documented in doc/*.rst but not offered as "
            f"completions: {sorted(missing)}")


if __name__ == "__main__":
    unittest.main()
