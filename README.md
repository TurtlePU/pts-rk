# PTS-rk

Rocq formalization of a rank-based pure type system, direct interpretations of
Tarski–Mostowski–Robinson arithmetic R, set semantics, and normalization bounds.

The original calculus has annotated, scoped terms, sort axioms
`U_i : U_0`, and product rank `max (a + 1) b`. The interpretations use its
original typing judgment, without adding term constructors or changing rules.

## Developments

All project Rocq sources are under [theories](theories/README.md). Physical
directory names and Rocq library names are deliberately independent.

[Expositions of the finished developments](docs/developments/README.md)
provide LaTeX–Markdown sources and compiled PDFs explaining their
infrastructure, theorem statements, key proof arguments and limitations.

| Directory | Rocq library | Main results and boundary |
| --- | --- | --- |
| [theories](theories/README.md) | `PTSrk` | Syntax, typing, confluence, preservation, strong normalization |
| [Interpretation_of_R](theories/Interpretation_of_R/README.md) | `Interpretation_of_R` | Shared annotated builders, checker, logic, telescopes, finite certificates |
| [relational](theories/Interpretation_of_R/relational/README.md) | `Interpretation_of_R.relational` | Theorem 4: all axioms, deduction preservation, ground correctness, nonfaithfulness |
| [functional](theories/Interpretation_of_R/functional/README.md) | `Interpretation_of_R.functional` | Theorem 7 and effective original-PTS witnesses, including `Kernel.Theorem5Target` |
| [ZFC_model](theories/ZFC_model/README.md) | `PTSrkModel` | Original typing soundness with explicit set-theoretic parameters; material BZC reduction remains open |
| [NormalizationComplexity](theories/NormalizationComplexity/README.md) | `PTSrk.NormalizationComplexity` | Costed TOWER upper bound, fixed-rank ELEMENTARY bound, linear rank-bound traversal, STLC reduction preserving and reflecting conversion |
| [CombinatoryLogic-rk](theories/CombinatoryLogic-rk/README.md) | `PTSrk.Combinatory` | Sound 65-shape Hilbert catalogue, proof-code extraction, finite-basis obstruction; source completeness remains open |
| [self_interpreter](theories/self_interpreter/README.md) | `PTSrk.SelfInterpreter` | Shared algebra folds, tag-free dependent unquotation, faithful compatibility codes and numeral-free combinatory CPS; rank-only dependent algebra remains open |
| [self_consistency](theories/self_consistency/README.md) | `PTSrk.SelfConsistency` | Native certificate adequacy/compression, fixed-rank resource histories, capacity and relational preservation; all-budget bounded soundness remains open |

The checked STLC reduction supports the paper's lower-bound argument using an
external hardness theorem; that theorem and machine-level TOWER-completeness
are not themselves formalized here. The set-model
[foundation audit](theories/ZFC_model/BZC_AUDIT.md) distinguishes supplied-model
soundness from an interpretation inside BZC + GCH + V_(omega+omega).

## Build and audit

Use OCaml 4.14.2, Dune 3.23.1, Rocq 9.2.0, Stdlib 9.1.0, and
Equations 1.3.2+9.2. See [toolchain and CI instructions](docs/DirectR-CI.md)
for the exact opam setup. In that environment, from the repository root:

```sh
dune build
dune build @theories/Interpretation_of_R/relational/audit
dune build @theories/Interpretation_of_R/functional/audit
dune build @theories/ZFC_model/audit
dune build @theories/NormalizationComplexity/audit
dune build @theories/CombinatoryLogic-rk/audit
dune build @theories/self_interpreter/audit
dune build @theories/self_consistency/audit
```

Audits print public theorem types and/or transitive assumptions on compilation.
Use a new absolute `--build-dir` to obtain fresh output rather than cached
success. The full local CI check also validates the workflow and compiles an
isolated pristine upstream snapshot:

```sh
bash tools/check-local-ci.sh
```

This runs the staged build on the host; it does not emulate GitHub's Ubuntu
runner or its setup/upload actions. Logs and resolved toolchain versions are
retained by the driver. See [tools](tools/README.md) for smaller checks.

## Reading and contributing

- [Paper and slides](latex/README.md), the
  [harmonized arithmetic manuscript](PTS_rk_interprets_Tarski_Mostowski_Robinson_arithmetic_R_harmonized.tex),
  and the estimator prototype [rank.agda](rank.agda).
- [Documentation index](docs/README.md), [live state](docs/direct-r-handoff/STATE.md),
  and [decisions](docs/direct-r-handoff/DECISIONS.md).
- [Self-interpretation research note](PTS-rk_self_interpreter.tex) and
  [compiled PDF](PTS-rk_self_interpreter.pdf).
- [AGENTS.md](AGENTS.md) for proof integrity, verification, and continuity rules.
- [Vendored dependencies](vendor/README.md), with their own license/provenance.

Historical handoff attachments and verification logs retain their recorded
paths. Current arithmetic and set-model paths begin with `theories/`;
their Rocq import namespaces have not changed.
