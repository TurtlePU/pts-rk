# Exact HOAS faithfulness: independent proof evidence

This directory records the replacement of the first-order Church-syntax
faithfulness proof by genuine binder-preserving HOAS. The historical
first-order source is preserved by the sibling
`previous-first-order/sources.patch` and its source hashes.

The proof targets the original annotated `PTSrk.Syntax.Term nat n` and
original beta conversion at a fixed source scope. A source binder becomes
an actual target lambda. Variable environments are represented by injective
maps into target variables; their invariant is proved through `transpose`
and `weak`. Product domains and lambda annotations remain explicit inputs
to distinct constructor handlers. No source typing premise is introduced.

Fresh build directory, created with `mktemp -d`:

```
/tmp/pts-rk-hoas-faithful.FnhT1R
```

Reproducible commands from the repository root:

```
bash docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/faithful/BUILD.sh 01
bash docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/faithful/BUILD.sh 02
bash docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/faithful/BUILD.sh 03
bash docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/faithful/BUILD.sh 04
bash docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/faithful/BUILD.sh 05
bash docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/faithful/BUILD.sh 06
bash docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/faithful/BUILD.sh 07
bash docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/faithful/CHECK.sh
```

Each script sets the pinned OPAM root/switch and executable path explicitly;
the complete effective command and exit status are retained. No timeout was
treated as success. `status.tsv` is the machine-readable attempt ledger.

Attempts 01–04 retain successive proof-development errors: dependent
finite-index injection, a shadowed sort-label name, incompletely inferred
fold induction parameters, and incompletely inferred canonical handler
indices. The generic structural `ast_fold_injective` proof had already
compiled by attempt 04. Attempts 05–06 failed in the concurrently developed
dependency `ChurchSyntax.v`, respectively at its carrier-variable and
quotation typing proofs; they did not reach this module.

`CHECK.sh` records tool/package versions and the final source hash, then
performs recursive `rocq check -silent -o` on the built module. Exact final
build/check results are recorded below.

Attempt 07 succeeded (exit 0), after the dependency's typing proofs were
completed. All six faithfulness theorem reports are `Closed under the global
context`: `ast_fold_injective`, `body_injective`, `quote_injective`,
`quote_indices_injective`, `quote_conversion_injective`, and
`quote_conversion_iff`. The six dependency theorem reports were also closed.

Recursive `rocq check -silent -o` succeeded (exit 0). Its context contains
only the already-known upstream `functional_extensionality_dep`; no
type-in-type, unsafe fixpoints, or assumed positivity occur. This is an
imported-library context summary, not an axiom dependency of the six closed
faithfulness theorems. The pinned versions recorded by `CHECK.sh` are Rocq
9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2, Dune 3.23.1.
The final proof source SHA-256 is
`e06c57c5c246ea7d708142e50c318e31d6570888c4d861d8f6127a2d8ef380bc`.

The semantic boundary is deliberate: this is exact faithfulness of
target-typed **raw HOAS**, not intrinsically source-typed PHOAS or a general
dependent unquoter. The conversion theorem recovers literal source syntax;
it does not identify distinct beta-equivalent source terms.
