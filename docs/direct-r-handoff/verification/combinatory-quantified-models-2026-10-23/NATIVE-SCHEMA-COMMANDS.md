# Native boundary, literal axioms, and source deduction soundness

All commands ran from the repository root on 2026-10-23. This worker changed
only the three new Rocq files below and this verification material. No source
PTS rule, native theorem, Dune registration, shared handoff or index was changed
by this worker. The root agent integrates registration and the fresh audit.

## Frozen sources and public reports

- FiniteNativeModelBoundary.v: 8 closed reports.
  SHA-256 f949b247f29647ae424f7011fd57954a84ea25f590c43673daa23b3b47bb48f0.
- MM0FiniteAxioms.v: 8 closed reports.
  SHA-256 1d0f0b02444d7da52c32adb7cf682b54cf708adfb0215f64bff4fdac3e128fe1.
- MM0SyntaxSoundness.v: 10 closed reports.
  SHA-256 27146534703167a7411483587883d5ffb68c2de8610b162db72956d3c10d4308.

Total: 26 new closed reports. Working logs and isolated objects:
/tmp/pts-rk-native-model-boundary.iBL2hu. Only logs/ledgers are archived;
temporary .vo/.glob/.aux files stay outside the repository.

## Exact isolated compilation

Rocq reports version 9.2, compiled with OCaml 4.14.2. The old dependency
closure is the previous fresh audit at /tmp/pts-rk-consistent-horn.2l5WGN/default.
The other worker's frozen new dependencies are at
/tmp/pts-rk-finite-internal.6wfWep: final MM0FiniteSignature, FiniteModelRealization,
and FiniteModelSoundness. Isolated checking is not relabelled a fresh rebuild
of those dependencies.

For each attempt, MODULE is the exact file base name listed in its attempt
ledger below, LOG its named log. Copied the current source to the temporary
directory before compiling:

```sh
cp theories/CombinatoryLogic-rk/MODULE.v /tmp/pts-rk-native-model-boundary.iBL2hu/MODULE.v
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq compile \
 -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories PTSrk \
 -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
 -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
 -Q /tmp/pts-rk-finite-internal.6wfWep PTSrk.Combinatory \
 -Q /tmp/pts-rk-native-model-boundary.iBL2hu PTSrk.Combinatory \
 /tmp/pts-rk-native-model-boundary.iBL2hu/MODULE.v > LOG 2>&1
```

Native-boundary attempts did not need and omitted the finite-internal -Q line.
All other arguments were as displayed.

### FiniteNativeModelBoundary

- attempt-01.log, exit 1: dependent elimination renamed the index binder;
  used explicit patterns. Removed unused ListNotations and its prefix warnings.
- attempt-02.log, exit 1: equality elimination required no-confusion;
  replaced it by an elementary option-valued projection and injection.
- attempt-03.log, exit 0: six reports; deprecated Local Notation advisory.
- attempt-04.log, exit 0: six reports, no diagnostics; Local Abbreviation.
- attempt-05.log, exit 0: final eight reports, no diagnostics; added the
  fixed-arity finite-tests theorem without global native-soundness premises.

An initial patch orchestration failed before writing any file because of a
JavaScript Unicode escape; corrected using literal Unicode. It was not a
Rocq compiler failure.

### MM0FiniteAxioms

- axioms-01.log, exit 1: cbn with a restricted unfolding list did not expose
  membership for tauto; changed to explicit unfolding plus simplification.
- axioms-02.log, exit 0: six reports, all 55 axioms well sorted.
- axioms-03.log, exit 0: final eight reports; added exact selected-name
  satisfaction and universal semantic Void-denial correspondence.
- axioms-04.log, exit 0: same final source, rebuilt against the other worker's
  frozen signature-09 object. Earlier objects used signature-07 and are
  superseded, not mixed with the final dependency closure.

### MM0SyntaxSoundness

- syntax-01.log, exit 1: redundant proof command after auto closed the goal.
- syntax-02.log, exit 1: projected atom fields not simplified before induction.
- syntax-03.log, exit 1: recursive substitution valuation needed its explicit
  shifted substitution argument.
- syntax-04.log, exit 1: projected expression list not simplified before induction.
- syntax-05.log, exit 1: premature rewriting of Forall_map changed the induction
  hypothesis away from the desired goal.
- syntax-06.log, exit 0: six reports for substitution and source-model soundness.
- syntax-07.log, exit 0: nine reports, adding the genuine structural ground-proof
  compiler and original-PTS proof-term compilation.
- syntax-08.log, exit 0: final ten reports, adding rejection of actual closed
  source Void derivations by every selected-axiom model.

Syntax attempts retain the upstream Vector.t advisory. It is not suppressed.
No warning-free claim is made for this module.

## Exact final recursive kernel check

```sh
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq check -silent -o \
 -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories PTSrk \
 -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
 -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
 -Q /tmp/pts-rk-finite-internal.6wfWep PTSrk.Combinatory \
 -Q /tmp/pts-rk-native-model-boundary.iBL2hu PTSrk.Combinatory \
 PTSrk.Combinatory.FiniteNativeModelBoundary \
 PTSrk.Combinatory.MM0FiniteAxioms \
 PTSrk.Combinatory.MM0SyntaxSoundness \
 > /tmp/pts-rk-native-model-boundary.iBL2hu/final-kernel.log 2>&1
```

Exit 0, full recursive closure, no skip/admit flags. Inventory: inherited
Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep only;
no type-in-type, unsafe fixpoints or assumed positivity.
The earlier boundary-only kernel.log also passed. Earlier axioms-kernel.log
passed with no axioms at all, before the final signature recompilation.
The final three-root check supersedes both for integration evidence.

Scoped git diff --check passes. The root agent supplies the fresh integrated
build and pristine complete-inventory comparison.

## Independent literal-source cross-check

```sh
python3 docs/direct-r-handoff/verification/combinatory-quantified-models-2026-10-23/crosscheck-mm0.py
```

Exit 0: all 55 named literal axioms match after separately parsing and expanding
the MM0 and Rocq definitions. Checks declaration order/sorts, ordered premises,
conclusion, and every constructor occurrence. crosscheck-01 through -04 all
passed; the final archived script locates the repository relative to itself.
The script is intentionally UNTRUSTED test evidence, not a kernel-verified
text parser. Rocq independently proves all transcription trees well sorted,
selection semantics exact, and substitution/deduction soundness for those trees.

## Mathematical boundary and independent review

The full native model no-go theorem requires one ungraded carrier, total
application, all native typing/beta soundness, semantic conversion/type
reduction, and Void denial. Directed reduction suffices: no antisymmetry,
extensionality or beta equality is required. Each arity yields distinct Church
selectors. The separate fixed-arity theorem requires only finitely many
selector-test typing/reduction facts and gives the lower bound k, not universal
infinity for every bounded fragment.

The reviewed FiniteModelRealization continuation conjunction is an honest
negative encoding of the externally enumerated finite clauses. Its inhabitance
iff theorem explicitly uses native external canonicity; it is not uniform
internal reflection. Each valid clause has an actual original-PTS term.

The reviewed projection model's omissions are essential: without f0, form and
ax are empty, so every catalogue-introduction axiom is vacuous; without sveq,
sub can be identity. Its 53/55 axiom count must not imply that full native
soundness is nearly established. All retained universal valuations genuinely
satisfy their clauses, and Void is nevertheless empty.
