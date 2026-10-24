"""Untrusted independent textual cross-check, not part of the Rocq theorem.

Parse both concrete sources, expand their definitions independently, and
compare binder sorts, ordered premises, and conclusions of every named axiom.
"""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4] / "theories" / "CombinatoryLogic-rk"


class Parser:
    def __init__(self, source, primitives, definitions, variables, coq=False):
        self.tokens = re.findall(r"[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[()[\];,]", source)
        self.pos = 0
        self.primitives = primitives
        self.definitions = definitions
        self.variables = variables
        self.coq = coq

    def pop(self):
        t = self.tokens[self.pos]
        self.pos += 1
        return t

    def expression(self):
        t = self.pop()
        if t == "(":
            x = self.expression()
            assert self.pop() == ")"
            return x
        if t == "[":
            result = []
            while self.tokens[self.pos] != "]":
                result.append(self.expression())
                if self.tokens[self.pos] != "]":
                    assert self.pop() == ";"
            self.pop()
            return result
        if t in self.variables:
            return self.variables[t]
        if t.isdigit():
            return int(t)
        if t in self.primitives:
            name, arity = self.primitives[t]
            args = [self.expression() for _ in range(arity)]
            if name == "rule":
                return dict(sorts=args[0], premises=args[1], conclusion=args[2])
            if name == "sort":
                return t.lower()
            if name == "variable":
                return ["variable", args[0]]
            return [name, args]
        params, body = self.definitions[t]
        args = [self.expression() for _ in params]
        return Parser(body, self.primitives, self.definitions,
                      dict(zip(params, args)), self.coq).whole()

    def whole(self):
        result = self.expression()
        assert self.pos == len(self.tokens), self.tokens[self.pos:]
        return result


arity = {
    "z": 0, "s": 1, "u": 1, "v": 1, "app": 2, "pi": 2,
    "lam": 2, "nil": 0, "cons": 3,
    "le": 2, "lt": 2, "max": 3, "lift": 3, "sub": 4,
    "red": 2, "stel": 4, "prefix": 3, "form": 6, "ax": 2, "h": 2,
}
native = {name: (name, n) for name, n in arity.items()}
coq = {
    "EZ": ("z", 0), "ES": ("s", 1), "EU": ("u", 1), "EV": ("v", 1),
    "EApp": ("app", 2), "EPi": ("pi", 2), "ELam": ("lam", 2),
    "ENil": ("nil", 0), "ECons": ("cons", 3), "EVar": ("variable", 1),
    "mkPositiveRule": ("rule", 3), "NAT": ("sort", 0),
    "TM": ("sort", 0), "TEL": ("sort", 0),
}
for name in ["le", "lt", "max", "lift", "sub", "red",
             "stel", "prefix", "form", "ax", "h"]:
    coq["a" + name[0].upper() + name[1:]] = (name, arity[name])

mm0 = re.sub(r"--[^\n]*", "", (ROOT / "CombinatoryPTS-rk.mm0").read_text())
native_definitions = {}
native_axioms = {}
for declaration in mm0.split(";"):
    declaration = declaration.strip()
    if not declaration.startswith(("def ", "axiom ")):
        continue
    kind, name = declaration.split()[:2]
    head = declaration[:declaration.index("$")]
    groups = re.findall(r"\(([^:]+):\s*(\w+)\)", head)
    names, sorts = [], []
    for variables, sort in groups:
        names.extend(variables.split())
        sorts.extend([sort] * len(variables.split()))
    bodies = re.findall(r"\$([^$]+)\$", declaration)
    if kind == "def":
        # Nullary definition names contain a trailing colon in MM0.
        native_definitions[name.rstrip(":")] = (names, bodies[0])
    else:
        variable_map = {v: ["variable", i] for i, v in enumerate(names)}
        formulas = [Parser(b, native, native_definitions, variable_map).whole()
                    for b in bodies]
        native_axioms[name] = dict(sorts=sorts, premises=formulas[:-1],
                                  conclusion=formulas[-1])

rocq = (ROOT / "MM0FiniteAxioms.v").read_text()
rocq = re.sub(r"\(\*.*?\*\)", "", rocq, flags=re.S)
definitions = {}
for m in re.finditer(r"(?:Local )?Definition\s+(\w+)(.*?)\s*:=\s*(.*?)\.",
                     rocq, re.S):
    name, head, body = m.groups()
    if name in ("axiom_rule", "selected_rules", "void_denial", "void_value", "all_axioms"):
        continue
    if name in coq:
        continue
    # Only x0..x9, numerical abbreviations and fixed telescope builders.
    assert ":" not in head, (name, head)
    definitions[name] = (head.split(), body)
body = rocq.split("Definition axiom_rule", 1)[1].split("end.", 1)[0]
body = body.split("match a with", 1)[1]
rocq_axioms = {}
for case in re.split(r"\|\s+A_", body)[1:]:
    name, expression = case.split("=>", 1)
    rocq_axioms[name.strip()] = Parser(expression, coq, definitions, {}, True).whole()

assert list(native_axioms) == list(rocq_axioms), (
    list(native_axioms), list(rocq_axioms))
assert len(native_axioms) == 55
for name in native_axioms:
    if native_axioms[name] != rocq_axioms[name]:
        print("MISMATCH", name)
        print("MM0:", json.dumps(native_axioms[name]))
        print("Rocq:", json.dumps(rocq_axioms[name]))
        raise SystemExit(1)
print("PASS: all 55 literal named axioms match exactly after definition expansion.")
print("Checked binder sorts/order, premise order and every constructor occurrence.")
print("This textual test is untrusted; Rocq separately checks expression sorting.")
