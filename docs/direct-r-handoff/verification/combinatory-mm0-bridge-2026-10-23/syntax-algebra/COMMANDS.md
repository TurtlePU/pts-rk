# Concrete MM0 constructor algebra and finite-query reflection

2026-10-23. Worker changes only MM0GuardedSyntaxAlgebra.v,
MM0GuardedReflection.v and this evidence directory. Root integration owns
Dune, exposition, handoff and fresh whole-development verification.
No original PTS/Agda/MM0 source, shared proof dependency, git index or commit
was changed by this worker.

## Toolchain and exact commands

Rocq 9.2, compiled with OCaml 4.14.2; pinned opam switch pts-rk-ci.
Dependencies are the previous fresh 50-module audit objects at
/tmp/pts-rk-guarded-fragments.Hzzxi9/default. These isolated commands do not
claim to recompile that closure. New objects are at
/tmp/pts-rk-mm0-syntax-algebra.UuB45x.

For each algebra attempt, the current source was first copied using:

```sh
cp theories/CombinatoryLogic-rk/MM0GuardedSyntaxAlgebra.v \
  /tmp/pts-rk-mm0-syntax-algebra.UuB45x/MM0GuardedSyntaxAlgebra.v
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq compile -time \
  -Q /tmp/pts-rk-guarded-fragments.Hzzxi9/default/theories PTSrk \
  -Q /tmp/pts-rk-guarded-fragments.Hzzxi9/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-guarded-fragments.Hzzxi9/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-guarded-fragments.Hzzxi9/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-mm0-syntax-algebra.UuB45x PTSrk.Combinatory \
  /tmp/pts-rk-mm0-syntax-algebra.UuB45x/MM0GuardedSyntaxAlgebra.v \
  > docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23/syntax-algebra/attempt-NN.log 2>&1
```

Reflection attempts use the identical command, substituting
MM0GuardedReflection for MM0GuardedSyntaxAlgebra and reflection-NN.log for
attempt-NN.log. The module copy is made before each compile.

| Algebra attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | Empty nth_error needed case analysis on its index. |
| 02 | 1 | Diagnostic removal left the variable case open. |
| 03 | 1 | Show confirmed the empty-context variable case. |
| 04 | 1 | Recursive pair membership needed explicit induction hypotheses. |
| 05 | 1 | Active/decode proof needed explicit unfolding. |
| 06 | 1 | Closed-substitution rewriting affected both sides. |
| 07 | 0 | Initial 15 endpoints closed. |
| 08 | 1 | Bounds wrapper needed unfolding before Forall rewriting. |
| 09 | 1 | A dependent rewriting match failed in the guard proof. |
| 10 | 1 | Show localized the same rewrite; ordinary equality transport suffices. |
| 11 | 0 | Guard discharge and concrete compiler/certificates; 30 endpoints closed. |
| 12 | 0 | Final module, represented Void/source arguments and regressions; 39 closed. |

| Reflection attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | Dependent raw-atom rewriting needed explicit equality transport. |
| 02 | 1 | Grounding equivalence needed its final explicit arguments. |
| 03 | 1 | Broad simplification unfolded the Void subterm before rewriting. |
| 04 | 0 | Query reflection and conditional Void/certificate results; 12 closed. |
| 05 | 0 | Final exact source/table union coverage; 15 closed. |

All final 54 public assumption reports are closed. Regression proofs use
reflexivity; there are no unsafe evaluation casts.

Full recursive kernel verification (no skip/admit flags), exit 0:

```sh
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-guarded-fragments.Hzzxi9/default/theories PTSrk \
  -Q /tmp/pts-rk-guarded-fragments.Hzzxi9/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-guarded-fragments.Hzzxi9/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-guarded-fragments.Hzzxi9/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-mm0-syntax-algebra.UuB45x PTSrk.Combinatory \
  PTSrk.Combinatory.MM0GuardedSyntaxAlgebra PTSrk.Combinatory.MM0GuardedReflection \
  > docs/direct-r-handoff/verification/combinatory-mm0-bridge-2026-10-23/syntax-algebra/kernel.log 2>&1
```

Complete context inventory equals the recorded fresh pristine inventory:
only inherited functional_extensionality_dep, no type-in-type, unsafe
fixpoints or assumed positivity. Root will compare again in fresh integration.
Raw log bytes are retained as .raw.gz; readable logs have trailing whitespace
and excess final blank lines removed mechanically. No proof source is touched
by that log formatting step. Scoped source whitespace check passes.

Isolated-checkpoint SHA-256 (before the explicitly recorded rename below):

```
5b31c207108b1a605b34e0fef549cfc40410c60f348eef28adadd11bf00d761a  theories/CombinatoryLogic-rk/MM0GuardedSyntaxAlgebra.v
467d59eaae2b2dcc1b3b45f64846bc5138815ba52a42f871152e9c26ad6a1a0a  theories/CombinatoryLogic-rk/MM0GuardedReflection.v
```

The integrated audit subsequently found a safety-scanner false positive:
the structural predicate's identifier matched the proof-termination keyword.
At root's explicit request it was renamed to FitsSyntax at all ten
occurrences. No theorem name, guard, proof tactic or mathematical definition
changed; the original strong safety scanner was retained. Final algebra SHA:

```
28343fe48b2fe765c4de6adabc0db028fc34dbe6098dbebb60c2a990aa3705c9  theories/CombinatoryLogic-rk/MM0GuardedSyntaxAlgebra.v
```

The earlier isolated objects above remain evidence for the earlier identifier.
The renamed source is verified by fresh integrated audit attempt 03 in the
parent COMMANDS.md, not by reusing those isolated objects.

## Mathematical scope

The shared finite domain lists all closed first-order expressions of each
signature sort admitted by explicit node/depth bounds, plus one overflow
value. Each of NAT/TM/TEL uses its own copy. All nine constructors are total;
ill-sorted or over-budget outputs become overflow. Guarded positive rules
check every variable's declared sort and every instantiated argument's size
and depth. Negative constraints are unchanged. Void has its genuine decoded
expression when N >= 5 and d >= 3.

Every semantic valuation is covered by the guard/evaluation theorems.
No source typing, desired evaluator equation, normalization or consistency
enters admission. The previous structural representation premise is fully
discharged. Every bounded independent source proof compiles to a semantic
finite-Horn proof and an original PTS truth-type inhabitant. Every finite
accepted query reflects into an independent MM0 source proof and has active
arguments; source_union_exact gives the converse at computed whole-proof
bounds, with exact decoding excluding overflow identifications.

The constructor construction itself does not prove the full55 relation model
exists. Reflection isolates the remaining source-only premise explicitly:
SourceVoidExcluded names says no independent literal source derivation has
conclusion H(e, Pi(U(0), v(0))). With that premise, all selected guarded
axioms plus universal Void denial have a concrete finite model, the checker
accepts, and the generated original-PTS satisfaction certificate is typed.
Discharging that premise requires the separate native/source adequacy bridge.
There is no uniform internal reflection or internal consistency claim here.
