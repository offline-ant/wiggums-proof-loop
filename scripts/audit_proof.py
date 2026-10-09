#!/usr/bin/env python3
"""Compare committed Lean proof sources, never working-tree files.

Before: transitive local import closure of --entry (unrelated monorepo proofs are
not deletions). After: that closure PLUS every retained .lean source under its
source root, except lakefile.lean and ComparatorChallenges/. Those exceptions
are packaging/challenge material, not submitted proof. Imported exceptions are
still counted. External dependencies are listed, not counted on either side.

The header grammar follows Lean 4.34.1 Parser/Module/Syntax.lean: optional module,
optional prelude, then repeated [public] [meta] import [all] MODULE. Module names
in this small auditor must be ordinary ASCII dotted identifiers; unfamiliar
syntax fails closed, rather than silently dropping an import. This is a source
size audit, NOT a substitute for Lean kernel/statement/axiom verification.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import unittest

MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*|[^\s]")
CHAR = re.compile(r"'(?:\\(?:u\{[0-9A-Fa-f]+\}|x[0-9A-Fa-f]{2}|.)|[^'\\\n])'")
COMMANDS = set("namespace section noncomputable open set_option private protected public "
               "def abbrev theorem lemma example instance inductive coinductive structure "
               "class axiom opaque constant constants variable variables universe universes "
               "attribute syntax macro elab initialize builtin_initialize notation infix "
               "infixl infixr prefix postfix export end mutual scoped local deriving "
               "register_option declare_syntax_cat recommended_spelling".split())
RESERVED = COMMANDS | {"module", "prelude", "import", "meta", "all"}
PROTECTED = ["OAI/Computability/UniqueGames/Model.lean",
             "ComparatorChallenges/UniqueGamesTheorem.lean",
             "ComparatorChallenges/UniqueGamesTheorem.json", "lean-toolchain"]


def mask_lean(text):
    """Return comment-masked text and comment/literal-masked text, preserving lines.

    Nested block comments, line comments, escaped ordinary strings, character
    literals and quoted identifiers are distinguished. Literal contents are
    preserved in size counts, but cannot manufacture import directives.
    """
    clean, code = list(text), list(text)

    def blank(a, start, end):
        for j in range(start, end):
            if a[j] not in "\r\n":
                a[j] = " "

    i = 0
    while i < len(text):
        start = i
        if text.startswith("/-", i):
            depth, i = 1, i + 2
            while depth and i < len(text):
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise ValueError("Unterminated block comment")
            blank(clean, start, i)
            blank(code, start, i)
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
            blank(clean, start, i)
            blank(code, start, i)
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            if i >= len(text):
                raise ValueError("Unterminated string")
            i += 1
            blank(code, start, i)
        elif text[i] == "«":
            end = text.find("»", i + 1)
            if end < 0:
                raise ValueError("Unterminated quoted identifier")
            i = end + 1  # Comments inside quoted identifiers are not comments.
        elif text[i] == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")):
            match = CHAR.match(text, i)
            if match:
                i = match.end()
                blank(code, start, i)
            else:
                i += 1
        else:
            i += 1
    return "".join(clean), "".join(code)


def imports_from_code(code):
    tokens = [m.group() for m in TOKEN.finditer(code.lstrip("\ufeff"))]
    i, imports = 0, []
    module_system = bool(tokens and tokens[0] == "module")
    i += int(module_system)
    if i < len(tokens) and tokens[i] == "prelude":
        i += 1
    while i < len(tokens):
        start = i
        public = i < len(tokens) and tokens[i] == "public"
        i += int(public)
        meta = i < len(tokens) and tokens[i] == "meta"
        i += int(meta)
        if i == len(tokens) or tokens[i] != "import":
            i = start
            break
        i += 1
        all_data = i < len(tokens) and tokens[i] == "all"
        i += int(all_data)
        if (public or meta or all_data) and not module_system:
            raise ValueError("Module-system import modifiers without `module`")
        if public and all_data:
            raise ValueError("Invalid public import all")
        if i == len(tokens) or not MODULE.fullmatch(tokens[i]) or tokens[i] in RESERVED:
            raise ValueError("Missing or unsupported import module identifier")
        imports.append(tokens[i])
        i += 1
    if "import" in tokens[i:]:
        raise ValueError("Import outside parsed header: unsupported syntax or malformed source")
    if i < len(tokens) and tokens[i] not in COMMANDS | {"#", "@"}:
        raise ValueError("Unsupported header continuation: " + repr(tokens[i:i + 4]))
    return imports


class Revision:
    def __init__(self, repo, rev, root):
        self.repo = str(repo)
        self.rev = self.git("rev-parse", "--verify", rev + "^{commit}").decode().strip()
        self.root = root.strip("/")
        self.prefix = self.root + "/" if self.root else ""
        self.blobs = {}
        for record in self.git("ls-tree", "-r", "-z", self.rev).split(b"\0"):
            if not record:
                continue
            metadata, filename = record.split(b"\t", 1)
            mode, kind, oid = metadata.decode().split()
            filename = filename.decode("utf-8")
            if filename.startswith(self.prefix):
                self.blobs[filename[len(self.prefix):]] = (mode, kind, oid)
        self.cache = {}
        self.parsed = {}

    def git(self, *args):
        return subprocess.check_output(["git", "-C", self.repo, *args])

    def read(self, path):
        if path not in self.blobs:
            raise ValueError(f"Missing committed file: {self.rev}:{self.prefix}{path}")
        mode, kind, oid = self.blobs[path]
        if kind != "blob" or mode not in {"100644", "100755"}:
            raise ValueError("Source must be a regular committed file: " + path)
        if path not in self.cache:
            self.cache[path] = self.git("cat-file", "blob", oid)
        return self.cache[path]

    def parse(self, path):
        if path not in self.parsed:
            data = self.read(path)
            try:
                text = data.decode("utf-8")
                clean, code = mask_lean(text)
                imports = imports_from_code(code)
            except ValueError as error:
                raise ValueError(f"{self.rev}:{path}: {error}") from error
            self.parsed[path] = {
                "path": path, "git_path": self.prefix + path,
                "blob": self.blobs[path][2], "sha256": hashlib.sha256(data).hexdigest(),
                "imports": imports,
                "metrics": {"bytes": len(data), "physical_lines": len(text.splitlines()),
                            "nonblank_noncomment_lines": sum(bool(x.strip()) for x in clean.splitlines()),
                            "approximate_lexical_tokens": len(re.findall(r"\w+|[^\w\s]", clean))}}
        return self.parsed[path]

    def closure(self, seeds):
        seen, external, pending = set(), set(), list(seeds)
        while pending:
            path = pending.pop()
            if path in seen:
                continue
            seen.add(path)
            for module in self.parse(path)["imports"]:
                local_path = module.replace(".", "/") + ".lean"
                if local_path in self.blobs:
                    pending.append(local_path)  # Includes local reexports outside OAI.
                elif module == "OAI" or module.startswith("OAI."):
                    raise ValueError(f"Missing local import {module} in {path}")
                else:
                    external.add(module)
        return seen, external

    def manifest(self, entry, include_retained):
        entry_path = entry.replace(".", "/") + ".lean"
        closure, external = self.closure([entry_path])
        retained = {p for p in self.blobs if p.endswith(".lean") and p != "lakefile.lean"
                    and not p.startswith("ComparatorChallenges/")} if include_retained else set()
        included, all_external = self.closure(closure | retained)
        files = [self.parse(p) for p in sorted(included)]
        return {"revision": self.rev, "source_root": self.root,
                "closure_files": sorted(closure), "retained_off_closure": sorted(included - closure),
                "external_imports": sorted(external | all_external), "files": files,
                "totals": {"files": len(files), **{k: sum(f["metrics"][k] for f in files)
                           for k in ["bytes", "physical_lines", "nonblank_noncomment_lines",
                                     "approximate_lexical_tokens"]}}}


def compare(before, after, entry):
    original = before.manifest(entry, include_retained=False)
    current = after.manifest(entry, include_retained=True)
    a = {f["path"]: f for f in original["files"]}
    b = {f["path"]: f for f in current["files"]}
    both = a.keys() & b.keys()
    changes = {"added": sorted(b.keys() - a.keys()), "removed": sorted(a.keys() - b.keys()),
               "changed": sorted(p for p in both if a[p]["sha256"] != b[p]["sha256"]),
               "unchanged": sorted(p for p in both if a[p]["sha256"] == b[p]["sha256"])}
    protected = {}
    for path in PROTECTED:
        old, new = before.read(path), after.read(path)
        protected[path] = {"identical": old == new, "sha256": hashlib.sha256(new).hexdigest()}
        if old != new:
            raise ValueError("Protected file changed: " + path)
    old_packages = {p["name"]: p for p in json.loads(before.read("lake-manifest.json"))["packages"]}
    packages = []
    for p in json.loads(after.read("lake-manifest.json"))["packages"]:
        old = old_packages.get(p["name"])
        keys = ("type", "url", "rev", "subDir")
        if old is None or any(old.get(k) != p.get(k) for k in keys):
            raise ValueError("Retained dependency differs: " + p["name"])
        packages.append({"name": p["name"], **{k: p.get(k) for k in keys}})
    savings = {k: {"removed": original["totals"][k] - current["totals"][k],
                   "percent": 100 * (original["totals"][k] - current["totals"][k]) / original["totals"][k]}
               for k in original["totals"]}
    return {"format": 1, "entry": entry, "method": __doc__, "original": original,
            "current": current, "savings": savings, "changes": changes,
            "protected": protected, "retained_dependency_pins": packages}


class SelfTests(unittest.TestCase):
    def test_nested_comments_and_literals(self):
        text = 'import /- a /- import OAI.Bad -/ b -/ OAI.Real\n' \
               'def s := "-- /- import OAI.Fake -/ \\"" -- comment\n' \
               'def c := \'"\'\ndef «/-name-/» := 1\n'
        clean, code = mask_lean(text)
        self.assertEqual(imports_from_code(code), ["OAI.Real"])
        self.assertIn('"-- /- import OAI.Fake', clean)
        self.assertIn('«/-name-/»', clean)
        self.assertNotIn('-- comment', clean)
        self.assertEqual(text.count('\n'), clean.count('\n'))

    def test_reexports_and_multiline(self):
        code = 'module\nprelude\npublic meta import\n OAI.A\nimport all OAI.B\nimport Mathlib\npublic section\n'
        self.assertEqual(imports_from_code(code), ['OAI.A', 'OAI.B', 'Mathlib'])

    def test_closure_and_retained_helpers(self):
        sources = {
            'OAI/Main.lean': 'module\npublic import OAI.Wrapper\n',
            'OAI/Wrapper.lean': 'import Helper.Outside\n',
            'Helper/Outside.lean': 'import Mathlib\n',
            'OAI/Orphan.lean': 'def helper := 1\n',
            'lakefile.lean': 'import Lake\n',
            'ComparatorChallenges/Test.lean': 'axiom excluded : False\n'}
        class FixtureRevision(Revision):
            def __init__(self):
                self.rev, self.root, self.prefix = 'fixture', '', ''
                self.parsed = {}
                self.blobs = {p: ('100644', 'blob', 'fixture') for p in sources}

            def read(self, path):
                return sources[path].encode()

        revision = FixtureRevision()
        before = revision.manifest('OAI.Main', include_retained=False)
        after = revision.manifest('OAI.Main', include_retained=True)
        self.assertEqual(before['totals']['files'], 3)
        self.assertEqual(after['totals']['files'], 4)
        self.assertEqual(after['retained_off_closure'], ['OAI/Orphan.lean'])
        self.assertEqual(after['external_imports'], ['Mathlib'])
        sources['OAI/Main.lean'] = 'import OAI.Missing\n'
        revision.parsed = {}
        with self.assertRaisesRegex(ValueError, 'Missing local import'):
            revision.manifest('OAI.Main', include_retained=False)

    def test_fail_closed(self):
        for text in ['import', 'import namespace', 'import OAI.A OAI.B',
                     'import OAI.«A»', 'namespace X\nimport OAI.A',
                     'public import OAI.A', 'module\npublic import all OAI.A']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                imports_from_code(text)
        for text in ['/- unclosed', '"unclosed', '«unclosed']:
            with self.assertRaises(ValueError):
                mask_lean(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--before-repo')
    parser.add_argument('--before-rev')
    parser.add_argument('--before-root', default='')
    parser.add_argument('--after-repo')
    parser.add_argument('--after-rev')
    parser.add_argument('--after-root', default='')
    parser.add_argument('--entry', default='OAI.Computability.UniqueGames.Main')
    parser.add_argument('--output', type=Path, help='Directory for audit.json and exact source manifests')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        result = unittest.TextTestRunner().run(unittest.defaultTestLoader.loadTestsFromTestCase(SelfTests))
        raise SystemExit(0 if result.wasSuccessful() else 1)
    for name in ('before_repo', 'before_rev', 'after_repo', 'after_rev', 'output'):
        if not getattr(args, name):
            parser.error('--' + name.replace('_', '-') + ' is required')
    report = compare(Revision(args.before_repo, args.before_rev, args.before_root),
                     Revision(args.after_repo, args.after_rev, args.after_root), args.entry)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'audit.json').write_text(json.dumps(report, indent=2) + '\n')
    for key in ('original', 'current'):
        (args.output / (key + '-source-files.txt')).write_text(
            ''.join(f['path'] + '\n' for f in report[key]['files']))
    print(json.dumps({key: report[key]['totals'] for key in ('original', 'current')}, indent=2))
    print(json.dumps({'savings': report['savings'], 'changes': {k: len(v) for k, v in report['changes'].items()},
                      'retained_off_closure': report['current']['retained_off_closure'],
                      'protected_files_identical': True, 'retained_dependency_pins_equal': True}, indent=2))


if __name__ == '__main__':
    main()
