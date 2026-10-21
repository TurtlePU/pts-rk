# Internal consistency of PTS-rk — research and formalization plan

This directory prepares a future internal consistency development. It currently
contains documentation, not a Rocq proof of internal consistency.

- [Self-contained research note and plan](README.tex), in the repository's
  LaTeX–Markdown dialect, and its [compiled PDF](README.pdf).
- [Reproducible document build](build-note.sh): run
  `bash theories/self_consistency/build-note.sh` from the repository root.
- [Source provenance and verification](EVIDENCE.md).

The note isolates the draft's specified predicate-only consistency sentence,
its tower-witnessed elementary-arithmetic soundness obligation, and the precise
boundary between existing Rocq metatheorems and internal proofs. It compares
a direct interpretation of Pakhomov's higher-order theory with a direct,
resource-relativized PHOAS route, including what fragment-uniform interpreters
would add.

Planned namespace: `PTSrk.SelfConsistency`. No Dune theory or audit alias is
registered before there are actual proof modules. The first proposed modules
are `ExplicitPTS.v`, `CertificateCoding.v`, and `NormalBottom.v`; the detailed
dependency order and acceptance criteria are in the note. All future PTS
endpoints must use the original `Syntax.Term nat`, `Typing.typ`, and
`Ranks.RankSorts`. Keep external Pakhomov results visibly outside the checked
dependency graph until their proofs or concrete proof certificates are supplied.

No CPS formalization is part of this plan. The original kernel, arithmetic
interpretations, set models, normalization and self-interpreter developments
remain separate libraries.
