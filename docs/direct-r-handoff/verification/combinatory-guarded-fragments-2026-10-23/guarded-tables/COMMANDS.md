# Executable guarded Hilbert tables

2026-10-23. Worker owns only GuardedHilbertTables.v and this verification
directory. Dune registration and fresh integrated audit belong to the root
agent. No native rules, prior proof sources, shared handoff, staging or commit
were changed by this worker.

Final SHA-256:

```
3978cb2c3a8691cfeb5dded0dc1bd386ea5b1135d4035e84a769b91c527bb6e4  theories/CombinatoryLogic-rk/GuardedHilbertTables.v
```

Pinned Rocq 9.2 / OCaml 4.14.2. The earlier dependency closure is the prior
fresh audit at /tmp/pts-rk-quantified-models.uhpkYv/default, supplemented by
the other workers' GuardedFiniteCarriers (28 reports) and final
GuardedBetaGraphs (36 reports). Final attempt 09 rebuilds against the latter
after its five regression additions; no stale beta-graph object is used in
the final recursive kernel check.

Each compile attempt first copied the current source into the isolated
directory. Exact command, with NN the attempt number:

```sh
cp theories/CombinatoryLogic-rk/GuardedHilbertTables.v \
  /tmp/pts-rk-guarded-tables.8mxXI2/GuardedHilbertTables.v
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq compile -time \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories PTSrk \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-guarded-carriers.mPsQdQ PTSrk.Combinatory \
  -Q /tmp/pts-rk-guarded-beta.LXnPKw PTSrk.Combinatory \
  -Q /tmp/pts-rk-guarded-tables.8mxXI2 PTSrk.Combinatory \
  /tmp/pts-rk-guarded-tables.8mxXI2/GuardedHilbertTables.v \
  > /tmp/pts-rk-guarded-tables.8mxXI2/attempt-NN.log 2>&1
```

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | Membership-case tactic needed constructor-equality identification. |
| 02 | 1 | Native reach soundness required existential parameter inference by eapply. |
| 03 | 1 | Application theorem needed its explicit domain type parameter. |
| 04 | 1 | Forall head elimination needed a supplied proof argument. |
| 05 | 1 | Satisfaction-witness definition needed its explicit closed term type. |
| 06 | 0 | Initial model, all-valuation semantic correspondence and native certificate; 31 reports. |
| 07 | 1 | Active-Void proof had already simplified prefix membership; removed redundant seq rewrite. |
| 08 | 0 | Added executable semantic rule test and active Void; 35 reports. |
| 09 | 0 | Final source, latest beta dependency, analytical nonempty typing; 36 closed reports, about 3.5s. |

No expensive saturation regression was run. Nonempty typing is proved
analytically for every size/depth bound at least one. Void is represented
by an actual non-overflow value whenever size >= 3 and depth >= 2, and its
semantic typing fibre is empty for every bound.

Full recursive kernel check, no dependency skip or admission flags:

```sh
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
/Users/akuklev/.local/share/pts-rk-ci/bin/opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories PTSrk \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-quantified-models.uhpkYv/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-guarded-carriers.mPsQdQ PTSrk.Combinatory \
  -Q /tmp/pts-rk-guarded-beta.LXnPKw PTSrk.Combinatory \
  -Q /tmp/pts-rk-guarded-tables.8mxXI2 PTSrk.Combinatory \
  PTSrk.Combinatory.GuardedHilbertTables \
  > /tmp/pts-rk-guarded-tables.8mxXI2/kernel.log 2>&1
```

Exit 0. Complete context inventory: inherited
Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep only;
no type-in-type, unsafe fixpoints or assumed positivity. Final source
whitespace check passes. The root agent supplies fresh integrated compilation
and comparison with pristine upstream.

## Mathematical boundary and review

Six independent constructor cases enumerate all closed/body/rank parameter
tuples in the explicit size/depth/prefix-alphabet domains, together with a
finite chosen list of concrete catalogue labels. Every retained clause is
proved to be an original HilbertGrounding.Rules instance. Guards inspect
displayed syntax and bounded beta paths/common reducts, never native typing,
derivability, consistency or final evaluator agreement.

Finite Horn saturation supplies exact fragment queries and unconditionally
excludes every original Void subject, not just listed tests. The semantic
rule graph has an executable Boolean test, proved equivalent to the literal
six-case bounded schema relation. Every arbitrary valuation in the fixed
finite carrier satisfies the guarded rules. Total application/product/
substitution use the shared overflow constructor algebra; a direct theorem
proves their application law under the explicit active-output guard.

The generated original-PTS satisfaction proof and its rank-at-most-four type
are unconditional, not conditional on a model-checker acceptance input.
An actual recursive deduction compiler sends independent finite Horn proof
trees to native PTS terms. This is an externally indexed proof-producing
translation, not uniform internal soundness over arbitrary Church inhabitants.

The carrier worker reviewed the initial source, requested a generic semantic
valuation theorem, and approved the added semantic_schema_correspondence /
rule_test / every_semantic_valuation interfaces. Its separate coverage module
handles enlargement and the union of these executable fragments; that result
is not silently assumed here. These are guarded native-Hilbert models, not
models of the unrestricted full55 MM0 computational graph theory or a proof
of unresolved original-PTS-to-catalogue completeness.
