# Fixed-rank structural resource graphs — 22 October 2026

## Contracts and boundaries

Three new modules (548 lines) extend the existing library without changing
the ORIGINAL PTS calculus, shared annotated assembler/checker, fixed carrier
or generation guard. The checker certifies literal `Typing.typ` conclusions;
it does not replace the target judgment. Neither arithmetic interpretation
nor the set model is imported.

- `ResourcePaths`: independent executable binary-tree lookup; injective
  structural path codes; append-only left-spine prefix; two-sided subresource
  extension; composition, joining and exact external size bounds. In
  particular, successful lookup gives
  `code_size value + code_size (path_code path) <= S (code_size tree)`.
- `InternalResources`: actual closed PTS terms for rank-6 prefix/extension
  relations, reflexivity, transitivity, joining and generation preservation.
  The relations transport rank-4 predicates closed under local pair growth
  with generated siblings. Transitivity is derived by composition, not an
  assumed closure rule. Independent root/left/right lookup has rank 7 and
  exact motive rank 5. Step, generation-extraction and lookup-to-extension
  theorem types have rank 8; the root theorem type has rank 7.
- `ResourceRealization`: an executable external witness generator erases
  exactly to independent lookup and returns an originally typed PTS proof
  for every successful standard lookup. Every standard prefix/extension
  also has a realization; those two existence theorems are not claimed as
  extracted executable algorithms.

The unchanged carrier has rank 2 and `Good_1(x)` rank 4. Generation extraction
uses explicit positive padding: `I = Good_1(atom NZero)` is an inhabited
rank-4 type, so `I -> Good_1(x)` has exact rank 5 and eliminates back by
application to its existing inhabitant. Lookup-to-extension uses the rank-5
motive `P(value) -> P(root)`. No cumulativity, eta, new axioms or primitives
are used. Definitions do not assume acceptance, normalization or consistency.

These are not converse/parametricity theorems for arbitrary Church-relation
inhabitants. Internal arbitrary-input lookup functionality/no-junk, witnessed
path composition, size/capacity comparison, the full resource envelope and
standard admission remain open. Extension transports rank-4 constructor-closed
predicates, not arbitrary rank-7 lookup claims. Concrete join steps have explicit
path/witness updates. All-budget soundness and internal consistency remain open.

## Reproduce the fresh audit

From the repository root:

```sh
bash docs/direct-r-handoff/verification/self-consistency-resources-2026-10-22/AUDIT.sh
```

The script records every expanded command, exit status, version and raw log;
uses fresh absolute build directories; compiles dependencies separately from
the public assumption-report module; recursively kernel-checks the result;
and compares the complete context inventory with independently rebuilt
pristine upstream `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.

Successful run: **17:36:43–17:43:35 UTC**, every stage exit **0**.

- Raw logs: `_build/self-consistency-resources-audit.X6R16B`.
- Fresh Dune directory: `/tmp/pts-rk-resources-fresh.6MyMwd`.
- Pristine checkout: `/tmp/pts-rk-resources-pristine.fTbPzV`.
- Pristine build: 17:36:44–47; pristine kernel check: 17:36:47–53.
- Fresh dependencies: 17:36:53–17:38:36.
- Separate public audit: 17:38:36–40; **166/166 closed reports**
  (127 previous plus 39 new: 13 paths, 21 internal resources, 5 realizations).
- Recursive kernel check: 17:38:40–17:43:35, **295 seconds**.
  The existing 300-second timeout was unchanged and did not fire.
- Inventory equality, original-source comparison, before/after source
  stability and safety scan all pass. Complete recursive inventories match
  exactly: only unchanged upstream
  `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`,
  no type-in-type, unsafe (co)fixpoints or assumed positivity.

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. Logical-loadpath remapping warnings remain in the raw kernel
logs; they are not omitted from the evidence or treated as failed checks.
No full repository CI run is claimed.

All ten prior proof modules, original kernel and shared infrastructure also
match the preceding checkpoint's manifest (audit/Dune necessarily changed):

```sh
shasum -a 256 -c <(rg -v 'self_consistency/(Audit.v|dune)$' _build/self-consistency-guards-audit.fLkaOG/sources-after.log)
```

Exit 0; raw output:
`_build/self-consistency-resources-progress/prior-source-stability.log`.

## Incremental compiler record

Pinned environment for these commands:

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Raw `attempt-NN.log` files are in
`_build/self-consistency-resources-progress`. Each invocation starts with
`opam exec -- dune build -j 2`; target paths below are under
`theories/self_consistency/`.

- 01, `ResourcePaths.vo InternalResources.vo`, exit 1: the native size-bound
  empty-path proof needed substitution/reduction before `lia`. Internal basic
  laws compiled.
- 02, same targets, exit 1: prefix transitivity required the actual closure
  constructor in `eauto`, not bare assumption.
- 03, `ResourcePaths.vo`, exit 0.
- 04, `ResourcePaths.vo InternalResources.vo`, exit 1: explicit `named` types
  were missing from the selected-term arguments of `observed`.
- 05, `InternalResources.vo`, exit 0, including lookup generation/transport.
- 06, `ResourceRealization.vo`, exit 1: missing `bool` annotation on `side`.
- 07, same target, exit 1: semicolon/destruct branch tactic expected four
  goals; parenthesized the per-branch tactic.
- 08, same target, exit 1: redundant final `exact` after `auto` solved the IH.
- 09, same target, exit 0.
- 10, same target after standard prefix/extension realization, exit 1:
  unresolved path existential; specified the path and witness arguments.
- 11, same target, exit 0.
- 12, `@theories/self_consistency/audit` (full alias), exit 0,
  166 closed reports. The subsequent fresh audit above is authoritative.

No proof contract, safety check or verification limit was weakened. No
compilation was deliberately terminated and no timeout occurred in this turn.

## Roadmap and PDF

```sh
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift theories/self_consistency/DIRECT_ROADMAP.pdf _build/self-consistency-resources-progress/pdf
```

Both builds/inspections exit 0. Initial build:
`/tmp/pts-rk-consistency-note.aFY8G2`; final after exact-rank/option-result
and constructor-closure wording corrections:
`/tmp/pts-rk-consistency-note.Mv8Vt6`.
Raw logs: `note-build-01.log`, `note-build-02.log`, `pdf-inspection.log`,
`pdf-inspection-final.log` in the progress directory. Final PDF: **11 nonempty
pages, four links**, required text/mathematics/primary reference and all-page
rendering pass. Changed pages 7–8 were visually reviewed before the final
minor wording corrections; final inspection/rendering also passes.
No overfull/underfull boxes, undefined references or missing glyph diagnostics.
Two pre-existing hyperref bookmark warnings about inline math/subscript remain
(also present in the preceding guarded-pilot build); these do not affect the
rendered formulas. The build validator was not weakened.

## Source hashes and working-tree state

SHA-256, relative to `theories/self_consistency`:

```text
b756dc75df1e9ce3fc00b9fb047dec232abeb53dcb5de5051f5fe018806cfc70  ResourcePaths.v
17fe2548dfdee8d06e52b8a9862cc5f75ce733ca186caecf24e2d9b58d83ca7a  InternalResources.v
3514dce95f730b93f5c74136195b6b95f66fbeee6311ec269cc319751aabea6c  ResourceRealization.v
c6c48cfaf72aedae4a4a62fc494c65a43751569e636f7d3192b71dfa53f1cea1  Audit.v
8775c94c444a07ad352b9ec5fa298eb8c54b7904f8b08fa39c08fb1bf0c9b91a  dune
377a9af5a9457739157a0985f4a5a2586db50014405a0142cdfc1752b66b3f41  DIRECT_ROADMAP.tex
73b184f83cbbaed1197e3144f0b9f7425d2d50c88c21137c3f513d7bd4e981ca  DIRECT_ROADMAP.pdf
```

HEAD remains `6a8dc984fb59a9b3743503cd405ffe59a31d1978` on `main`.
No staging, commit, push or deletion in this continuation; broad unrelated
user work is preserved. Generated caches, raw logs and renderings remain
ignored. The durable handoff records the next mathematical gate, rather than
treating a successful structural audit as completion of internal consistency.

Final shell syntax and scoped whitespace checks both exit 0:

```sh
bash -n docs/direct-r-handoff/verification/self-consistency-resources-2026-10-22/AUDIT.sh theories/self_consistency/build-note.sh
git diff --check -- README.md docs/DirectR-CI.md docs/direct-r-handoff/STATE.md docs/direct-r-handoff/BUILD.md docs/direct-r-handoff/DECISIONS.md theories/self_consistency
```

The separate trailing-whitespace scan of all three new proof files and this
verification directory has no matches (`rg` exit 1). Final source/PDF hashes
still match those above; `git diff --cached --stat` is empty.
