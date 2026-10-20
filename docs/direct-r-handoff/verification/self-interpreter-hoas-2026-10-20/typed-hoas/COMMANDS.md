# Derivation-directed source-typed PHOAS prequotation

Working directory: `/Users/akuklev/air/pts-rk`.
The existing task-specific absolute build directory is
`/tmp/pts-rk-brown-palsberg.KOiQg5/build`; it was first allocated fresh for
the preceding BrownPalsberg module and reused during these development
attempts. No unrelated source files or kernel rules were changed.

For each two-digit attempt `NN`, the exact build command was:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-brown-palsberg.KOiQg5/build --display=short --no-buffer theories/self_interpreter/TypedHOAS.vo > docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/typed-hoas/attempt-NN.log 2>&1
build_status=$?
printf '%s\n' "$build_status" > docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/typed-hoas/attempt-NN.exit
tail -n 48 docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/typed-hoas/attempt-NN.log
exit "$build_status"
```

The first command used a 40-line tail and attempt 03 used 45 lines;
the compiler command and complete redirected log were unchanged.

| Attempt | Exit | First result/error |
| --- | --- | --- |
| 01 | 0 | Executable prequote and original generic typing compiled. |
| 02 | 1 | Simple-type codomain code was not definitionally the shifted code. |
| 03 | 0 | Strong recovery and actual polymorphic identity-handler specialization compiled. |
| 04 | 1 | Concurrent Dune registration preceded creation of TypedHOASAlgebra.v. No compiler ran. |
| 05 | 1 | Source-variable lifting equality needed an explicit convertible goal. |
| 06 | 0 | Actual simultaneous-substitution naturality and recovery compiled. |
| 07 | 1 | Arithmetic tactic could not infer the lambda-child budget after aggressive unfolding. |
| 08 | 1 | Application budget required the same explicit definitional conversion. |
| 09 | 0 | Final bounded typing theorem compiled; seven closed assumption reports. |

No timeout, compiler interruption, suppressed error or skipped proof occurred.
All failed logs and numeric statuses are retained unchanged.

## Recursive kernel check

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-brown-palsberg.KOiQg5/build/default/theories PTSrk -Q /tmp/pts-rk-brown-palsberg.KOiQg5/build/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-brown-palsberg.KOiQg5/build/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.TypedHOAS > docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/typed-hoas/kernel.log 2>&1
```

Exit 0, recorded in kernel.exit. Recursive checking was enabled; no admission
or no-recursion option was used. This also checks the imported BrownPalsberg
module. The loaded-context inventory contains only the existing upstream
`functional_extensionality_dep`, and no unsafe fixpoints, assumed positivity
or type-in-type. All seven printed public TypedHOAS theorem reports are
closed; the new substitution proof does not use functional extensionality.
The parent task performs the fresh aggregate audit, pristine comparison,
full CI and documentation build separately.

Pinned versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1. The task's exact version and package output is
in the sibling `../hoas/versions.log` and `../hoas/packages.log`.

## Checked scope and remaining obligation

- `prequote` consumes the existing independent ChurchSTLC derivation data
  in Type. It retains original source annotations and uses actual target
  binders/variables, source-type-indexed case operations, and an externally
  indexed family of object-language type functions.
- `prequote_typed` proves ORIGINAL RankSorts typing. The bounded variant
  `prequote_bounded_typed` needs family laws only at ranks at most
  `rank_budget d = max(order A, ExecutableQuotation.quote_budget d)` and case
  laws only where `order(A -> B)` is at most that budget. The result-order
  component is essential for lambda annotations.
- `identity_abs` and `identity_app` are the actual closed polymorphic indexed
  BrownPalsberg handlers applied to source typecodes. Their strong recovery
  is proved, not an algebra assumption. `identity_interpretation_recovers`
  recovers exact source syntax, not just a source normal form.
- `prequote_substitution` is an exact equation for the actual simultaneous
  replacement of parameters. `substitution_identity_recovers` therefore
  proves recovery of an instantiated existing quotation, not merely of a
  regenerated quote. Its explicit premises specify the replacement of
  family/case parameters by the actual identity interpretation and preserve
  source variables under the given renaming.
- Original typing of those concrete identity cases and of the resulting
  interpreted source is supplied separately by TypedHOASAlgebra. Normality
  and exact source-syntax fidelity for neutral VARIABLE palettes are proved
  separately by TypedHOASFaithful, not asserted by this module.

This is a checked prequotation/algebra interface, NOT a closed finite PHOAS
package or full dependent self-interpreter. Although ranks are bounded,
BoundedCasesTyped still quantifies over all simple-type shapes in those
ranks; infinitely many shapes can share a rank. A finite-context normal
implementation must either specialize finitely many polymorphic rank-pair
handlers and adapt the normality/erasure proof, or restrict the variable
palette to the actual finite source occurrences. The finite telescope and
closed decoder are not constructed by these theorems. Full dependent
substitution/conversion coherence remains a further separate obligation.

Final source SHA-256, also in source.sha256:
`754b6f91557124637932e93c6e1d37ad9b55a4c4032228f88b8388e6489ac41a`.

The safety scan of TypedHOAS.v and BrownPalsberg.v produced no matches
(safety-scan.exit is 1, the normal rg no-match status). The command was:

```sh
rg -n 'Admitted|\badmit\b|^Axiom|^Parameter|Unset Guard|Unset Universe|Type in Type|unsafe' theories/self_interpreter/TypedHOAS.v theories/self_interpreter/BrownPalsberg.v
```

Sources are frozen at this checkpoint. No Git commit or push was performed
by this subtask; the existing dirty worktree was preserved.
