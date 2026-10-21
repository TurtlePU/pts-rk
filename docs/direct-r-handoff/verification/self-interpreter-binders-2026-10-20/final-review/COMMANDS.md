# Dependent-binder checkpoint — fresh final verification, 20 October 2026

Base commit: `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`.
All four new sources plus Audit/Dune were frozen before verification.
No proof, Git reference or index was changed by this audit; concurrent
note/README/handoff editing remained outside the frozen proof manifest.

## Results

- Fresh absolute aggregate build: exit 0, **646** closed reports, comprising
  527 previous + 80 new module reports + 39 added aggregate reports.
  Audit contains 206 Check/Print pairs.
- Recursive original and aggregate `rocq check -silent -o`: exit 0.
- Original kernel inventory: byte-identical to the retained independently
  checked pristine `723cf2ec61c737ae82ba33d2e7db44f650122b0e` inventory.
- Original core, frozen ZFC and NormalizationComplexity comparisons against
  `ffa7131`: exit 0 with empty differences.
- All 45 proof files plus Dune: beginning/end hashes identical.
- Full local CI: exit 0; actionlint and **226/226** stages pass, including
  an actual fresh isolated pristine-upstream build. No stage was weakened.
- New-source safety and whitespace searches: no matches (expected `rg`
  exit 1). Scoped whitespace and runner shell-syntax checks exit 0.

The new public theorem assumption reports are closed. The recursive loaded
inventory lists only the unchanged upstream
`Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep` and
reports no type-in-type, unsafe fixpoints or assumed positivity. Loaded
declarations are not the same thing as dependencies of a printed theorem.

Aggregate interval: 14:41:35–14:43:10 UTC. Full CI: 14:41:36–14:42:28 UTC.
Neither final runner failed or timed out. Earlier compiler failures are
retained in each sibling module evidence directory, not overwritten.

## Exact environment and commands

Fresh Dune directory: `/tmp/pts-rk-self-binders-audit.xrjN04`.
Raw local-only ignored evidence:
`_build/self-interpreter-binders-final-review.r6pl8m/`.
It contains `AUDIT.sh`, `CI.sh`, `CHECK-SOURCES.sh`, full driver/kernel logs,
all exit codes, versions/package inventory, initial/final source manifests,
and the staged-driver logs in `staged/`. These raw paths record local
provenance; generated caches/logs are not source artifacts.

Pinned environment: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1, opam 2.6.1.

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
build_dir=/tmp/pts-rk-self-binders-audit.xrjN04
timeout 1200 opam exec -- dune build --build-dir="$build_dir" \
  --display=short --no-buffer -j 2 @theories/self_interpreter/audit
timeout 1200 opam exec -- rocq check -silent -o \
  -Q "$build_dir/default/theories" PTSrk PTSrk.Ranks
timeout 1200 opam exec -- rocq check -silent -o \
  -Q "$build_dir/default/theories" PTSrk \
  -Q "$build_dir/default/theories/NormalizationComplexity" PTSrk.NormalizationComplexity \
  -Q "$build_dir/default/theories/self_interpreter" PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.Audit
diff -u docs/direct-r-handoff/verification/self-interpreter-2026-10-20/baseline/upstream-kernel.log \
  _build/self-interpreter-binders-final-review.r6pl8m/core-kernel.log
git diff --exit-code ffa7131 -- theories/ZFC_model
git diff --exit-code ffa7131 -- \
  theories/AbstractRewriting.v theories/Congruence.v theories/Confluence.v \
  theories/Context.v theories/DefEq.v theories/Inversions.v \
  theories/Preservation.v theories/Ranks.v theories/Reduction.v theories/SN.v \
  theories/Syntax.v theories/Typing.v
git diff --exit-code ffa7131 -- 'theories/NormalizationComplexity/*.v'
bash -n tools/ci-check-direct-r.sh tools/build-self-interpreter-note.sh

export DIRECT_R_LOCAL_HOME=/Users/akuklev/.local/share/pts-rk-ci
export DIRECT_R_LOCAL_SWITCH=pts-rk-ci
export DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/self-interpreter-binders-final-review.r6pl8m/staged
export DIRECT_R_JOBS=2
export DIRECT_R_STAGE_SECONDS=1200
bash tools/check-local-ci.sh
```

The retained pristine inventory is compared with a NEW original-core kernel
check, while CI separately performs its new pristine archive/build. The
absolute fresh aggregate build reruns all Print Assumptions commands;
cached success is not used as new assumption evidence. Known logical
loadpath remapping and earlier notation warnings remain visible in logs.

## Mathematical contract review

Read-only reviews found no contract defect:

- `TarskiSorts` uses law ZERO to represent `u_r:C0` as an inhabitant of
  `El_0(u_0)`, correctly reflecting the original axiom `U_r:U_0`. Cast
  direction, normality and direct typing before recovery are checked.
- `TarskiContext` uses an actual typed variable renaming, and its concrete
  spine contains only independently sorted original declarations. The
  actual computed identity context/fill retains fresh variables and derives
  wf/TypedSub. All six field equations and generic operations allow new
  binder-dependent inputs. Independent review by the separate paper agent
  passed against the frozen source hash. Instantiated-context normality is
  deliberately not claimed.
- `TarskiBinders` contracts the administrative fresh-variable family redex.
  Normal decoded annotations follow from normal A and B; their typing and
  evidence are transported by original reduction/conversion. Exact renaming
  naturality and one-way substitution reduction are distinct. Local binder
  injectivity preserves its inputs through the unchanged family occurrence
  in the neutral law application. Recovery returns the literal lambda with
  substituted decoded domain and transpose-substituted body, not a completed
  arbitrary source-lambda quotation theorem.
- `TarskiRoundtrip` constructs a genuine well-formed open context in which
  the existing neutral cast roundtrip and its dependent indices are normal,
  typed and nonconvertible. This excludes beta-cancellation for these casts,
  not internal equality witnesses, different casts, higher indices or full
  dependent PHOAS. Reflexivity computation remains independently positive.

Full derivation-directed dependent quotation, generated global conversion
coherence and all-source coverage remain open. These local operations and
context bridges do not assume those desired conclusions.

The updated note abstract, sort/context/smart-binder/roundtrip sections,
remaining-program text and development README were independently reviewed
against these frozen declarations. Two wording precisions were requested
and verified on disk: the smart-operation typing premises are separate from
its normal-input normality condition, and local binder introduction explicitly
states `a,b <= k` and `A:C_a`. The final prose also distinguishes arbitrary-spine
original decoded-product operations from fixed-signature smart operations,
and retains the exact substituted decoded annotation in binder recovery.
No further correction was requested. PDF compilation/visual review is owned
and recorded separately by the parent agent, not claimed by this proof audit.

## Frozen source identity

Complete 46-entry manifest SHA-256:
`21216a6c66d59f5f98ffa3a79a2995f003e4d2f59d92293b8d4501dfe7dba91f`.
Initial/final manifests compare byte-for-byte.

```text
0dcc393aa1edaedd9fe165cce5195295d87f2c99de4c7a45b8cd1fdf830d679a  TarskiSorts.v
225d392d065f8cb57ad15955ca64791cb341b02bce8ba0d568477a95e090ed17  TarskiContext.v
e20c499a7caee0c70b6d70d8aceffdb2afdd361eb208d16be7af5baf3da1f2be  TarskiBinders.v
47c28f9ca35675f2385bd32a9ea97147b445638247e8d7396a86fe0a44dca73e  TarskiRoundtrip.v
25209ade9fbf84a3b82318cac76707aff6ff0900e8137e1cccc38a8b9307de12  Audit.v
7230f5a917b6d7abc8608a220b42df0c23f2a43502c2e87556b5b0f5d51c8fb9  dune
```

All listed files are under `theories/self_interpreter/`. No commit or push
was performed in this continuation.
