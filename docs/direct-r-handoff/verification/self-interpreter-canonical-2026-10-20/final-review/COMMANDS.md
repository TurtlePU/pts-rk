# Independent canonical-interface review and final verification

Date: 2026-10-20. Starting HEAD:
`b6c81d1c24404835f5665b8bf4c263379dee5202`, with the four new canonical modules
and their Audit/Dune integration uncommitted. This audit changes no proof
source, existing library, index, branch or remote. It writes only local
diagnostic runners/logs and this concise report. Parent owns the exposition
and live handoff updates.

## Independent contract review

All four modules pass read-only mathematical/API review.

- `OpenCanonical` scans the maximum literal label and declaration node count
  across the original context, together with those of the source term.
  `budget_sound` applies the existing full-PTS syntax bound; no typing
  decision, oracle, supplied successful normalization or result premise is
  consumed by the executable function. Its correctness requires only an
  independent original well-formed context and original source typing.
  Terms, types and lambda annotations are the unchanged original syntax.
- The normalization correctness statement preserves the supplied original
  type and relates the actual greedy computation to the costed normalizer.
  Context-independent normal forms and conversion iff follow from confluence
  on independently typed inputs. Cross-context comparison is conversion of
  raw syntax of the same scope, not a semantic identification of differently
  declared variables. The charge theorem covers the normalization stage only;
  it excludes context scanning, serialization and an internal evaluator.
- `CanonicalSubstitution.normal_sub_typed` really establishes the original
  dependent `TypedSub` after normalizing entries: it converts their substituted
  lookup types as well. `hsubst_canonical_typed` uses original validity to
  obtain the exact sort of the substituted source type and types the normal
  result at the normalized dependent type, without cumulativity. Hereditary
  substitution and its composition are literal equalities with outer
  normalization; their premises are independent original typed substitutions.
- `CanonicalContexts` normalizes declarations under their original prefixes.
  Induction on the original Type-valued well-formedness witness retains each
  formation rank; it does not eliminate an existential Prop rank into data.
  Both identity typed substitutions are constructed with original conversion
  rules. Consequently context normalization preserves and reflects typing of
  the **same literal term and type**, including annotations. Original context
  beta reduction, declaration normality, idempotence and normal-form agreement
  are proved rather than supplied as transport assumptions.
- `CanonicalTypeIndex` separates faithful raw syntax quotation Q from
  J = quotation after open normalization. Both outputs are closed, normal,
  originally typed homogeneous raw-HOAS codes even on untyped raw inputs;
  that fact alone does not imply the input was normalized. On independently
  typed inputs in well-formed contexts, J identifies exactly source beta
  conversion and supports the proved hereditary substitution equations.
  The explicit convertible type pair separates Q and J, while a normal
  original open type plus a normal typed substitution creates a beta redex.
- These are executable **metalevel original-syntax** constructions. J is a
  code of a canonical type, not that type at its original universe. There is
  no object-language El, typed code reifier or full dependent PHOAS evaluator.
  The existing strong PHOAS decoder still covers the independent STLC source.

One comment-only issue was corrected by its owner before the freeze: ordinary
literal substitution is already associative, so the canonical composition
comment now says the equation *includes* intervening normalizations rather
than asserting that associativity is possible *only* with them. No theorem
was weakened. Module-level earlier compiler attempts are retained in the
other checkpoint reports; the final combined run below has no failure.

## Exact environment and commands

Raw local evidence:
`_build/self-interpreter-canonical-final-review.TPZ60J`.
Fresh absolute Dune directory: `/tmp/pts-rk-self-canonical-audit.JWgIgs`.
The literal `AUDIT.sh` and `CI.sh` runners, traced stdout/stderr, commands,
timestamps, exit codes, package inventories, stage logs and source manifests
are retained in the raw directory, not added as tracked source artifacts.

Pinned versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1 and opam 2.6.1 (`versions.log`).

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
bash _build/self-interpreter-canonical-final-review.TPZ60J/AUDIT.sh

export DIRECT_R_LOCAL_HOME=/Users/akuklev/.local/share/pts-rk-ci
export DIRECT_R_LOCAL_SWITCH=pts-rk-ci
export DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/self-interpreter-canonical-final-review.TPZ60J/staged
export DIRECT_R_JOBS=2
export DIRECT_R_STAGE_SECONDS=1200
bash _build/self-interpreter-canonical-final-review.TPZ60J/CI.sh
```

Principal fresh audit commands:

```sh
timeout 1200 opam exec -- dune build --build-dir=/tmp/pts-rk-self-canonical-audit.JWgIgs --display=short --no-buffer -j 2 @theories/self_interpreter/audit
timeout 1200 opam exec -- rocq check -silent -o -Q /tmp/pts-rk-self-canonical-audit.JWgIgs/default/theories PTSrk PTSrk.Ranks
timeout 1200 opam exec -- rocq check -silent -o -Q /tmp/pts-rk-self-canonical-audit.JWgIgs/default/theories PTSrk -Q /tmp/pts-rk-self-canonical-audit.JWgIgs/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-self-canonical-audit.JWgIgs/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.Audit
diff -u docs/direct-r-handoff/verification/self-interpreter-2026-10-20/baseline/upstream-kernel.log _build/self-interpreter-canonical-final-review.TPZ60J/core-kernel.log
git diff --exit-code ffa7131 -- theories/ZFC_model
git diff --exit-code ffa7131 -- theories/AbstractRewriting.v theories/Congruence.v theories/Confluence.v theories/Context.v theories/DefEq.v theories/Inversions.v theories/Preservation.v theories/Ranks.v theories/Reduction.v theories/SN.v theories/Syntax.v theories/Typing.v
git diff --exit-code ffa7131 -- 'theories/NormalizationComplexity/*.v'
bash -n tools/ci-check-direct-r.sh tools/build-self-interpreter-note.sh
```

## Observed results

Fresh audit: **PASS**, exit **0**, 10:49:40--10:50:33 UTC. All nine entries
in `status.tsv` have exit code 0. Fresh output contains **326 closed assumption
reports**: 228 module reports, 97 aggregate endpoint reports and one core
report. This is the preceding 264 plus 43 new module reports and 19 new
aggregate reports. Audit has exactly 97 `Check` and 97 `Print Assumptions`
declarations. The new module counts are 10 + 8 + 10 + 15.

Recursive checking passes with only the unchanged upstream
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep` in the
loaded-context inventory. Type-in-type, unsafe (co)fixpoints and assumed
positivity inventories are empty. The fresh original-core inventory is
byte-identical to the retained pristine upstream inventory at
`723cf2ec61c737ae82ba33d2e7db44f650122b0e`. Original core, frozen reference ZFC
and normalization-source comparisons are empty. Known loadpath-remapping
warnings are retained; no checks were disabled.

Full local CI: **PASS**, exit **0**, 10:49:41--10:50:16 UTC. The unchanged
`bash tools/check-local-ci.sh` passes actionlint and **226/226** stages,
including a fresh pristine upstream build. `staged/stages.tsv` has only
`PASS` / `0` rows; `staged/result.txt` reports `Last stage: complete`.
This root worktree includes unrelated local developments, unlike the separate
172-stage published snapshot. No stage was removed or weakened. Ordinary CI
can reuse its Dune cache; the independent fresh aggregate above supplies new
assumption output. These are local results, not remote CI claims.

No final audit/CI compiler error or timeout occurred. A source-safety scan
of the four new modules finds no admissions, new axioms/parameters, unchecked
casts or disabled guard/universe/positivity checks (rg exit 1, no matches).
It supplements rather than replaces the kernel checks.

## Frozen source identities

All 29 proof sources plus Dune were hashed before and after verification;
exact `cmp` exits 0. `source-sha256.txt` and `final-source-sha256.txt` retain
the complete inventory. Manifest SHA-256:
`201a89386e60134f8dd45e06fa04140925ea8b9ae7cc15b962cefbddb47edcf6`.
The changed/new endpoints are bound to these exact inputs:

```text
155c091012d3251a3ea083100caec60fef1d567fe86bcb6fe4b0d0b38ccc0889  theories/self_interpreter/OpenCanonical.v
0f3e33864857fe81c2eb114b0c08022ca3ffb11ec3439db91676a95546e3b858  theories/self_interpreter/CanonicalContexts.v
1a3e89fb34d28c816e5a95b423d252d373a3ad2ae7e51c68226a67445acf6ed4  theories/self_interpreter/CanonicalSubstitution.v
c161417c3e65e985d9d46bee6af9c9402f4297a49b24186487115e9e2a1358fa  theories/self_interpreter/CanonicalTypeIndex.v
627dda73332768c24923a08bc33ffee3b8337b116967264aa43fb3acc162929d  theories/self_interpreter/Audit.v
ea681a30cee9122bc238c3152178ae7fd92fa6c036efcec15a5d742a96921ca6  theories/self_interpreter/dune
```

The note/PDF and evolving exposition are deliberately outside this source
freeze; their independent build and inspection are recorded by the parent.
Next proof obligation is an actual original-PTS represented dependent family
and typed decoding/reification interface, not merely another metalevel
canonical syntax operation.
