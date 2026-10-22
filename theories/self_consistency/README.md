# Internal consistency of PTS-rk — research and formalization plan

This directory prepares a future internal consistency development. It currently
contains documentation, not a Rocq proof of internal consistency.

- [Recommended direct roadmap](DIRECT_ROADMAP.tex) and its [PDF](DIRECT_ROADMAP.pdf):
  proof-local relational soundness inside original PTS-rk, with no H or EA
  proof-theory intermediary. This supersedes the earlier priority order,
  not the earlier note's record of its particular finite-ordinal target.
- [Self-contained research note and plan](README.tex), in the repository's
  LaTeX–Markdown dialect, and its [compiled PDF](README.pdf).
- [Reproducible document build](build-note.sh): run
  `bash theories/self_consistency/build-note.sh` from the repository root.
- [Source provenance and verification](EVIDENCE.md).

The direct route targets one fixed-rank term refuting independently accepted
contradiction certificates under independently specified resource guards.
A continuation-encoded resource domain gives the final negative consistency
statement without a uniform budget selector. Standard raw-code admission,
arbitrary-input soundness and any comparison to the old sentence are explicit
obligations. The combinatory development currently supplies external Agda
soundness in graded finite syntactic carriers, not yet internal PTS soundness
or fixed finite first-order models.

Build the new roadmap with
`bash theories/self_consistency/build-note.sh DIRECT_ROADMAP`.
The no-argument command continues to build the earlier summary.

The earlier summary isolates the draft's specified predicate-only consistency sentence,
its tower-witnessed elementary-arithmetic soundness obligation, and the precise
boundary between existing Rocq metatheorems and internal proofs. It compares
a direct interpretation of Pakhomov's higher-order theory with a direct,
resource-relativized PHOAS route, including what fragment-uniform interpreters
would add.

The continuation now supplies a fixed closure application head for each
quotation-budget fragment; see
[the interpreter note](../../PTS-rk_self_interpreter.tex). The code carries
its specialized normal runner. This simplifies the evaluation interface,
but internal accepted-proof reification and budget quantification remain
open. No internal consistency proof is claimed by that interface theorem.

The shared `Algebra` interface now also supports tag-free full-dependent
evaluation (`UnifiedAlgebra`) and actual alternative folds on STLC and
finite-dictionary combinatory codes. The latter include a typed CPS algebra
and require no numeral conversion. These simplify code representation and
evaluation, not the acceptance-soundness obligation: the full dependent
signature still varies by plan, and the Hilbert bridge does not yet supply
native source completeness or internal dependent unquotation. See the
updated interpreter note and `self_interpreter/OBLIGATIONS.md`.

Planned namespace: `PTSrk.SelfConsistency`. No Dune theory or audit alias is
registered before there are actual proof modules. The direct roadmap begins
with `NativeProofCodes`, `CertificateAdequacy`, `RankCompression`, and guarded
finite-table correctness; the earlier `ExplicitPTS`/EA modules belong to
the historical alternative route. All future PTS
endpoints must use the original `Syntax.Term nat`, `Typing.typ`, and
`Ranks.RankSorts`. Keep external Pakhomov results visibly outside the checked
dependency graph until their proofs or concrete proof certificates are supplied.

No CPS formalization is part of this plan. The original kernel, arithmetic
interpretations, set models, normalization and self-interpreter developments
remain separate libraries.
