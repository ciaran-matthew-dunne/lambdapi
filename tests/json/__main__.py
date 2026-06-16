"""Integration tests for `lambdapi check --json`.

These tests drive the built binary and assert over the NDJSON output:
- well-formed records (one JSON object per line)
- schema invariants (every record has [kind] and [ts])
- exit-code / stream discipline (stdout = NDJSON, stderr empty, exit code
  tracks presence of errors)
- batch semantics (one failing file does not sink the rest)

Run with `make test_json` or `python3 -m tests.json`.
"""

import json
import os
import subprocess
import sys
import unittest


def _lambdapi_binary():
    explicit = os.environ.get("LAMBDAPI_BIN")
    if explicit:
        return explicit
    # Prefer the freshly-built binary in _build; fall back to PATH.
    here = os.path.dirname(__file__)
    repo_root = os.path.abspath(os.path.join(here, "..", ".."))
    candidate = os.path.join(
        repo_root, "_build", "install", "default", "bin", "lambdapi")
    return candidate if os.path.isfile(candidate) else "lambdapi"


LAMBDAPI = _lambdapi_binary()
REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))


def run(args, cwd=REPO_ROOT):
    """Run the binary, return (exit_code, stdout, stderr)."""
    proc = subprocess.run(
        [LAMBDAPI] + args,
        cwd=cwd, capture_output=True, text=True, timeout=60)
    return proc.returncode, proc.stdout, proc.stderr


def parse_ndjson(blob):
    """Parse NDJSON. Every non-empty line must be a JSON object; any parse
    failure fails the test (strict contract)."""
    records = []
    for i, line in enumerate(blob.splitlines(), start=1):
        if not line.strip():
            continue
        try:
            records.append(json.loads(line))
        except json.JSONDecodeError as e:
            raise AssertionError(
                f"stdout line {i} is not valid JSON: {line!r} ({e})")
    return records


def kinds(records):
    return [r.get("kind") for r in records]


def first(records, kind):
    return next((r for r in records if r.get("kind") == kind), None)


def by_kind(records, kind):
    return [r for r in records if r.get("kind") == kind]


class TestSchemaVersion(unittest.TestCase):

    def test_version_prints_single_line(self):
        code, out, err = run(["json-schema-version"])
        self.assertEqual(code, 0, f"unexpected exit {code}; stderr={err!r}")
        self.assertEqual(err, "",
            f"json-schema-version should print nothing on stderr; got {err!r}")
        # One line, semver-shaped. Be permissive on exact value — the test
        # guards the contract, not the current number.
        lines = [ln for ln in out.splitlines() if ln.strip()]
        self.assertEqual(len(lines), 1,
            f"expected a single line; got {lines!r}")
        parts = lines[0].split(".")
        self.assertEqual(len(parts), 3,
            f"expected semver MAJOR.MINOR.PATCH; got {lines[0]!r}")
        for p in parts:
            self.assertTrue(p.isdigit(),
                f"semver component not numeric: {p!r} in {lines[0]!r}")


class TestJsonOutputShape(unittest.TestCase):
    """Invariants that every --json run must satisfy."""

    def _assert_common_invariants(self, records):
        self.assertGreater(len(records), 0, "no records at all")
        for r in records:
            self.assertIn("kind", r, f"record missing [kind]: {r!r}")
            self.assertIn("ts", r, f"record missing [ts]: {r!r}")
            self.assertIsInstance(r["ts"], str)
            # ISO 8601 UTC with 'Z' suffix. We don't parse it back — just
            # guard the shape so a regression (e.g. emitting a Unix epoch
            # int) is caught.
            self.assertTrue(r["ts"].endswith("Z"),
                f"ts not ISO 8601 UTC: {r['ts']!r}")
        # Must end with a summary.
        self.assertEqual(records[-1]["kind"], "summary",
            f"last record should be [summary]; got {kinds(records)[-5:]!r}")

    def test_ok_file_is_clean_ok(self):
        code, out, err = run(["check", "--json", "tests/OK/215.lp"])
        self.assertEqual(err, "",
            f"stderr should be empty in JSON mode; got {err!r}")
        records = parse_ndjson(out)
        self._assert_common_invariants(records)
        # Shape: file_start, ..., file_end(ok), summary.
        self.assertEqual(records[0]["kind"], "file_start")
        self.assertEqual(records[0]["file"], "tests/OK/215.lp")
        ends = by_kind(records, "file_end")
        self.assertEqual(len(ends), 1)
        self.assertEqual(ends[0]["status"], "ok")
        self.assertIsInstance(ends[0]["elapsed_ms"], int)
        self.assertGreaterEqual(ends[0]["elapsed_ms"], 0)
        summary = records[-1]
        self.assertEqual(summary["files_checked"], 1)
        self.assertEqual(summary["files_ok"], 1)
        self.assertEqual(summary["files_failed"], 0)
        self.assertEqual(summary["schema_version"].count("."), 2,
            f"summary.schema_version should be semver; "
            f"got {summary['schema_version']!r}")
        self.assertEqual(code, 0,
            f"expected exit 0 for OK file; got {code}")

    def test_ko_file_emits_diagnostic_and_exits_nonzero(self):
        code, out, err = run(["check", "--json", "tests/KO/59.lp"])
        self.assertEqual(err, "",
            f"stderr should be empty in JSON mode; got {err!r}")
        records = parse_ndjson(out)
        self._assert_common_invariants(records)
        diags = by_kind(records, "diagnostic")
        errors = [d for d in diags if d["severity"] == "error"]
        self.assertGreaterEqual(len(errors), 1,
            f"expected >=1 error diagnostic; got {diags!r}")
        ends = by_kind(records, "file_end")
        self.assertEqual(len(ends), 1)
        self.assertEqual(ends[0]["status"], "error")
        summary = records[-1]
        self.assertEqual(summary["files_checked"], 1)
        self.assertEqual(summary["files_ok"], 0)
        self.assertEqual(summary["files_failed"], 1)
        self.assertEqual(code, 1,
            f"expected exit 1 for KO file; got {code}")


class TestDiagnosticShape(unittest.TestCase):
    """Diagnostics include the structured [range] we promise."""

    def test_error_diagnostic_has_file_and_range(self):
        _code, out, _err = run(["check", "--json", "tests/KO/59.lp"])
        records = parse_ndjson(out)
        err = next(d for d in by_kind(records, "diagnostic")
                   if d["severity"] == "error")
        self.assertIn("file", err, f"error diag missing [file]: {err!r}")
        self.assertIn("range", err, f"error diag missing [range]: {err!r}")
        rng = err["range"]
        for side in ("start", "end"):
            self.assertIn(side, rng, f"range missing [{side}]: {rng!r}")
            pt = rng[side]
            self.assertIn("line", pt)
            self.assertIn("col", pt)
            self.assertIsInstance(pt["line"], int)
            self.assertIsInstance(pt["col"], int)
            # Lines are 1-indexed (CLI convention); col is 0-indexed.
            self.assertGreaterEqual(pt["line"], 1,
                f"line should be >=1 (1-indexed); got {pt['line']}")
            self.assertGreaterEqual(pt["col"], 0)


class TestBatchContinuation(unittest.TestCase):
    """One failing file must not abort the rest of the batch — that's the
    whole point of structured output vs the text mode's fail-fast."""

    def test_batch_ok_ko_ok_continues_and_reports_all(self):
        code, out, err = run([
            "check", "--json",
            "tests/OK/215.lp", "tests/KO/59.lp", "tests/OK/215.lp",
        ])
        self.assertEqual(err, "")
        records = parse_ndjson(out)
        starts = by_kind(records, "file_start")
        ends = by_kind(records, "file_end")
        self.assertEqual(len(starts), 3,
            f"expected 3 file_start; got {len(starts)}")
        self.assertEqual(len(ends), 3,
            f"expected 3 file_end; got {len(ends)}")
        statuses = [e["status"] for e in ends]
        self.assertEqual(statuses, ["ok", "error", "ok"],
            f"expected ok,error,ok; got {statuses}")
        summary = records[-1]
        self.assertEqual(summary["files_checked"], 3)
        self.assertEqual(summary["files_ok"], 2)
        self.assertEqual(summary["files_failed"], 1)
        self.assertEqual(code, 1,
            "any failure in the batch must surface as exit 1")


class TestNoWarnings(unittest.TestCase):
    """--json --no-warnings must not emit warning diagnostics, but must
    still emit file_start/file_end/summary."""

    def test_no_warnings_suppresses_only_warning_diagnostics(self):
        _code, out, _err = run([
            "check", "--json", "--no-warnings", "tests/OK/215.lp"])
        records = parse_ndjson(out)
        warnings = [d for d in by_kind(records, "diagnostic")
                    if d["severity"] == "warning"]
        self.assertEqual(warnings, [],
            f"--no-warnings should drop warning diagnostics; got {warnings!r}")
        # But structure is preserved.
        self.assertEqual(
            kinds(records), ["file_start", "file_end", "summary"],
            f"record skeleton wrong; got {kinds(records)!r}")


class TestTextModeUnchanged(unittest.TestCase):
    """A sanity check that omitting --json keeps the old text-mode
    behaviour: banners on stdout, warnings on stderr, no JSON anywhere."""

    def test_text_mode_produces_no_json_on_stdout(self):
        code, out, _err = run(["check", "tests/OK/215.lp"])
        self.assertEqual(code, 0)
        # Whatever stdout contains, it's not NDJSON — no line should parse
        # as an object with a [kind] field.
        for line in out.splitlines():
            line = line.strip()
            if not line.startswith("{"):
                continue
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            self.assertNotIn("kind", obj,
                f"text mode leaked JSON record on stdout: {line!r}")


if __name__ == "__main__":
    # Ensure tests can find each other as a package.
    here = os.path.dirname(__file__)
    repo_root = os.path.abspath(os.path.join(here, "..", ".."))
    if repo_root not in sys.path:
        sys.path.insert(0, repo_root)
    unittest.main(verbosity=2)
