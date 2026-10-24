# Literal MM0 structural guards: isolated verification

2026-10-23. Worker owns only MM0GuardedQuantification.v and this directory.
The root agent registers the module and performs fresh integrated verification.
No native PTS rule, original MM0 text, shared handoff or existing proof source
was changed by this worker. No staging or commit was performed.

Final source SHA-256:

```
83f18a0f3ce0ba83fd9421bb942cacb6f3a7f7fc827e02b712d48d2d181596a7  theories/CombinatoryLogic-rk/MM0GuardedQuantification.v
```

Rocq 9.2, compiled with OCaml 4.14.2. Dependency objects are the previous
fresh audit at /tmp/pts-rk-quantified-models.uhpkYv/default. This isolated
compile does not claim to rebuild that closure. Temporary module objects
are outside the repository at /tmp/pts-rk-guarded-quantification.cAOXbM.

Each attempt first copied the current source into that temporary directory:

```sh
cp theories/CombinatoryLogic-rk/MM0GuardedQuantification.v \
  /tmp/pts-rk-guarded-quantification.cAOXbM/MM0GuardedQuantification.v
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq compile -time \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories PTSrk \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-guarded-quantification.cAOXbM PTSrk.Combinatory \
  /tmp/pts-rk-guarded-quantification.cAOXbM/MM0GuardedQuantification.v \
  > /tmp/pts-rk-guarded-quantification.cAOXbM/attempt-NN.log 2>&1
```

Attempts 01 and 02 omitted `-time`; all later attempts included it.

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | Required simplifying pair projections after guard case analysis. |
| 02 | 1 | Interrupted expensive implicit theorem application; no successful compilation claim. |
| 03 | 1 | `-time` located the same implicit application; interrupted after 34.683s at that command. |
| 04 | 0 | Replaced implicit application with explicit theorem arguments; initial 16 reports closed. |
| 05 | 1 | New source compiler used a mistaken old soundness theorem name. |
| 06 | 0 | Source compiler, its original-PTS typing, and semantic soundness compile; 23 reports closed. |
| 07 | 1 | New substitution agreement helper needed an explicit scope index. |
| 08 | 1 | The default-change lemma needed its explicit type argument. |
| 09 | 0 | Final module compiles in about 2.5s; all 29 reports closed. |

Namespace-remapping and upstream Vector.t advisories are retained, not
suppressed. There are no project proof holes or new axioms.

Recursive kernel verification (full transitive closure, no skip/admit flags):

```sh
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories PTSrk \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-guarded-quantification.cAOXbM PTSrk.Combinatory \
  PTSrk.Combinatory.MM0GuardedQuantification \
  > /tmp/pts-rk-guarded-quantification.cAOXbM/kernel.log 2>&1
```

Exit 0. Complete inventory contains only the inherited
Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep;
no type-in-type, unsafe fixpoints or assumed positivity. The root agent's
fresh integrated audit compares this inventory with pristine upstream.
Scoped `git diff --check` passes. The final module and copied source have
the same hash above.

## Exact scope

Expression depth is separate from PTS rank and proof height. The actual
numeric guards inspect all declared substitution values and all instantiated
premise/conclusion arguments. A source tree's complete resource support is
computed structurally, including every node in its proof tree. These guards
do not inspect derivability, typing, consistency or target agreement.

All semantic valuations are enumerated. An inactive positive instance is
compiled as the tautology H -> H; universal negative constraints remain
unchanged. Exact checker/model/certificate correspondence does not assert
that the full55 guarded literal theory has a finite model. Native adequacy
of its computational graph and catalogue predicates remains separate.

Source deduction translation has an explicit guard-representation premise.
`structural_guard_representation` reduces that premise to active status and
exact constructor decoding of bounded substituted values, not native typing
or the desired soundness conclusion. This worker does not instantiate a
finite truncated MM0 constructor algebra. The guarded native-Hilbert model
is developed independently by the root agent.

The generated finite satisfaction type has rank at most four, and accepted
candidates supply original-PTS inhabitants. Source proof trees are recursively
compiled into semantic Horn proof trees and then literal original-PTS terms.
These are external proof-producing translations, not one internal uniform
reflection theorem over arbitrary encoded fragments or proof inhabitants.
