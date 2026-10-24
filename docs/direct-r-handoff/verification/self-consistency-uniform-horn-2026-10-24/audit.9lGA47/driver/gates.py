#!/usr/bin/env python3
"""Fail-closed structural gates for the independent uniform-Horn audit."""
import argparse
import hashlib
import pathlib
import re
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sexps(text):
    # The current Dune files contain plain atoms and comments only. Reject
    # unsupported string syntax instead of silently misparsing future edits.
    require('"' not in text, "quoted Dune syntax needs explicit review")
    tokens = re.findall(r"[()]|[^\s()]+", re.sub(r";[^\n]*", "", text))
    stack, forms = [], []
    for token in tokens:
        if token == "(":
            value = []
            (stack[-1] if stack else forms).append(value)
            stack.append(value)
        elif token == ")":
            require(bool(stack), "unmatched Dune close parenthesis")
            stack.pop()
        else:
            require(bool(stack), "Dune atom outside a form")
            stack[-1].append(token)
    require(not stack, "unclosed Dune form")
    return forms


def additive_dune(before, after, additions, audit, alias):
    old, current = sexps(before), sexps(after)
    require(len(set(additions)) == len(additions), "duplicate new module in scope")
    theories = [x for x in current if x and x[0] == "rocq.theory"]
    require(len(theories) == 1, "expected exactly one Rocq theory")
    fields = [x for x in theories[0][1:] if isinstance(x, list) and x[0] == "modules"]
    require(len(fields) == 1, "expected exactly one module list")
    field = fields[0]
    for module in additions + [audit]:
        require(field.count(module) == 1, "missing/duplicate new registration: " + module)
        field.remove(module)
    added_alias = ["alias", ["name", alias], ["deps", audit + ".vo"]]
    require(current.count(added_alias) == 1, "missing/changed/duplicate audit alias")
    current.remove(added_alias)
    require(current == old, "Dune change exceeds reviewed module/alias additions")


def additive_import(before, after, audit):
    added = "From PTSrk.SelfConsistency Require Import " + audit + ".\n"
    require(after.count(added) == 1, "missing/duplicate full-audit import")
    require(after.replace(added, "", 1) == before, "preceding full-audit body changed")


def declaration_names(text, module):
    names = re.findall(r"(?m)^\s*(?:Theorem|Lemma|Example|Corollary|Fact|Proposition)\s+([A-Za-z0-9_']+)", text)
    require(len(names) == len(set(names)), "duplicate proof declaration in " + module)
    return [module + "." + module + "." + name for name in names]


def declaration_coverage(source_texts, audit_text):
    expected = sorted(name for module, text in source_texts for name in declaration_names(text, module))
    require(bool(expected), "empty proof declaration inventory")
    checked = sorted(re.findall(r"(?m)^\s*Check\s+([A-Za-z0-9_'.]+)\.$", audit_text))
    printed = sorted(re.findall(r"(?m)^\s*Print Assumptions\s+([A-Za-z0-9_'.]+)\.$", audit_text))
    require(expected == checked, "Check inventory differs from public proof declarations")
    require(expected == printed, "Print Assumptions inventory differs from public proof declarations")
    return expected


def inventory(text):
    marker = "CONTEXT SUMMARY\n"
    require(text.count(marker) == 1, "kernel log must have exactly one context summary")
    result = text[text.index(marker):]
    for label in ("Constants/Inductives relying on type-in-type",
                  "Constants/Inductives relying on unsafe (co)fixpoints",
                  "Inductives whose positivity is assumed"):
        require("* " + label + ": <none>\n" in result, "unsafe/incomplete kernel summary: " + label)
    return result


def exact_inventory(pristine, current):
    require(inventory(pristine) == inventory(current), "full kernel inventory differs from pristine")


def closed_reports(log, expected):
    actual = len(re.findall(r"(?m)^Closed under the global context$", log))
    require(expected > 0 and actual == expected,
            "closed report count: expected %d, found %d" % (expected, actual))
    require(not re.search(r"(?m)^\s*(?:Axioms|Assumptions):", log), "non-closed printed assumptions")
    return actual


def main():
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command", required=True)
    reg = commands.add_parser("registration")
    reg.add_argument("baseline"); reg.add_argument("root"); reg.add_argument("audit"); reg.add_argument("alias")
    reg.add_argument("modules", nargs="+")
    decl = commands.add_parser("declarations")
    decl.add_argument("root"); decl.add_argument("audit"); decl.add_argument("modules", nargs="+")
    inv = commands.add_parser("inventory")
    inv.add_argument("pristine"); inv.add_argument("current")
    report = commands.add_parser("reports")
    report.add_argument("root"); report.add_argument("build"); report.add_argument("log")
    args = parser.parse_args()
    if args.command == "registration":
        base, root = pathlib.Path(args.baseline), pathlib.Path(args.root)
        directory = root / "theories/self_consistency"
        additive_dune((base / "self-consistency-dune.snapshot").read_text(),
                      (directory / "dune").read_text(), args.modules, args.audit, args.alias)
        additive_import((base / "self-consistency-Audit.v.snapshot").read_text(),
                        (directory / "Audit.v").read_text(), args.audit)
        require((base / "combinatory-dune.snapshot").read_bytes() ==
                (root / "theories/CombinatoryLogic-rk/dune").read_bytes(),
                "concurrent combinatory registration changed; explicit review required")
        print("PASS: precisely additive self-consistency registrations; combinatory unchanged")
    elif args.command == "declarations":
        directory = pathlib.Path(args.root) / "theories/self_consistency"
        names = declaration_coverage([(m, (directory / (m + ".v")).read_text()) for m in args.modules],
                                     (directory / (args.audit + ".v")).read_text())
        print("\n".join(names))
    elif args.command == "inventory":
        exact_inventory(pathlib.Path(args.pristine).read_text(), pathlib.Path(args.current).read_text())
        print("PASS: exact complete pristine inventory, all unsafe categories absent")
    else:
        root, build = pathlib.Path(args.root), pathlib.Path(args.build) / "default"
        objects = sorted((build / "theories").rglob("*.vo"))
        require(bool(objects), "empty fresh compiled dependency closure")
        expected = 0
        for obj in objects:
            relative = obj.relative_to(build).with_suffix(".v")
            live, snapshot = root / relative, build / relative
            require(live.is_file() and snapshot.is_file(), "missing source for " + str(relative))
            require(live.read_bytes() == snapshot.read_bytes(), "fresh object source differs: " + str(relative))
            expected += len(re.findall(r"(?m)^\s*Print Assumptions\s", snapshot.read_text()))
            print(hashlib.sha256(snapshot.read_bytes()).hexdigest() + "  " + str(relative))
        actual = closed_reports(pathlib.Path(args.log).read_text(), expected)
        print("Compiled closure modules: %d; exact closed reports: %d" % (len(objects), actual))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        sys.exit(1)
