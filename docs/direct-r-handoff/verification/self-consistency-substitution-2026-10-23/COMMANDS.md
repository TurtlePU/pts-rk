# Annotated substitution specifications and internal renaming

23 October 2026. Seven new modules; original annotated PTS typing throughout.
This record separates successful incremental checks from the fresh audit.
Fresh compilation and all 385 closed reports pass; independent recursive
kernel checking **timed out** (2400 seconds, exit 124). No complete current
inventory or complete audit pass is claimed. No full repository CI is claimed.

## Exact contracts

- `CodeSubstitution`: independent native `Scoped` and constructor-directed
  `Replaced` relations, executable partial renaming/replacement/substitution,
  exact agreement with original `Syntax.rename`, `replace`, `shift`, and
  `subst`. Scope preservation is separate from totality; `Replaced` agrees
  with the executable algorithm on arbitrary raw inputs. Annotations are
  transformed outside binders, bodies under the lifted environment. These
  are native Rocq results, not internal PTS substitution witnesses.
- `InternalBinary`: positive and natural binary guards at ranks 4 and 6;
  independent successor graph at rank 8, with zero/one/even/odd-carry rules.
  Positive tails exclude an even/odd-zero constructor. Typed constructors,
  guard-to-Good maps, and every-successor input/output number guards are
  actual PTS terms; every output is positive. Exact inhabited padding is
  used, not cumulativity. No internal numerical conversion is introduced.
- `BinaryRealization`: native positive/carry specifications with canonical
  encoding iff theorems; executable original-PTS Pos/Num/Succ witnesses for
  **all** positive/natural indices. Constructor applications use `tApp` and
  original substitution. Native exactness does not assert reflection of
  arbitrary internal Church inhabitants.
- `InternalScope`: independent binary Index (rank 10, motive 6) and annotated
  Scope (rank 12, motive 4). Index entails both number guards; Scope entails
  raw structural Good. All five source constructors are retained. These are
  scope relations, not original source typing or normalization predicates.
- `ScopeRealization`: executable Index witnesses for every `Fin n` and Scope
  witnesses for every original `Term nat n`, including untyped terms. Every
  successful existing decoder output is covered. Application helpers use
  original typing/substitution, not a replacement typing judgment.
- `InternalRenamingLookup`: one fixed relational environment under binders,
  explicit binary depth/target codes, and independent base/zero/step rules.
  RenAt has rank 14 and exact motive 10. Its all-output Index theorem assumes
  the local `FBound` contract, which is absent from the graph clauses.
  A bounded-shift instance has rank 12 and its bound is proved from source
  Index and successor witnesses; no target Index premise is inserted.
- `InternalRenaming`: independent annotated constructor graph, rank 16 and
  exact motive 12. Its rank-17 preservation term folds into literal output
  Scope using the proved RenAt bound. The annotation uses the current
  environment; the body advances source/target bounds and depth, retaining
  the same base environment. The graph contains neither the output-scope
  conclusion nor the bounded-environment contract. All 11 declarations pass
  the final isolated compilation, exit 0.

The original kernel, common assembler/checker and all 27 earlier proof
modules remain unchanged; root hash checks are retained in
`_build/self-consistency-substitution-progress/prior-unchanged.log` and
`common-unchanged.log`. No axioms, admissions, unsafe checks or PTS-rule
changes are introduced.

## Review boundary and next minimal milestone

Every-output preservation really avoids global lookup functionality and
matching-constructor inversion: the proof constructs the output invariant
directly and uses the same successor witnesses in the binder conclusion.
The local environment contract is not the global preservation theorem.
Its concrete bounded-shift instance is derived independently.

RenAt deliberately does **not** enforce `target = base + depth`. Its zero
rule accepts independently witnessed successors for target and depth.
Consequently this interface is an operational overapproximation supporting
the stated scope invariant, not an exact lifted-environment decoder. Native
substitution correctness and standard scope realization do not automatically
give standard realization or exact semantics of internal renaming.
Do not turn the missing global state equation into a new mandatory gate:
standard weakening can explicitly thread its coherent canonical states.

Next: forward-realize the existing bounded-shift graph on every original
`t -> shift t`, with exact canonical endpoints. Then construct term-valued
lookup whose binder step weakens a previous result using that graph, prove
its every-output Scope invariant, and instantiate it with the single-
substitution environment `0 -> u`, `successor j -> var j`. Constructor-
directed replacement can reuse this lookup, preserving annotations and
binder lifting. Global functionality, a uniform decoder, matching inversion,
and complete transported typing certificates are not prerequisites.
Dependent typing/conversion preservation, resource sufficiency, standard
raw-input admission, all-budget soundness and consistency remain open.

## Environment and incremental checks

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Pinned versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. Root progress directory:
`_build/self-consistency-substitution-progress`.

Root Dune commands, each exit 0:

```sh
# attempt-01.log
opam exec -- dune build -j 2 theories/self_consistency/CodeSubstitution.vo \
  theories/self_consistency/InternalBinary.vo theories/self_consistency/BinaryRealization.vo
# attempt-02.log
opam exec -- dune build -j 2 theories/self_consistency/InternalScope.vo
# attempt-03.log
opam exec -- dune build -j 2 theories/self_consistency/ScopeRealization.vo \
  theories/self_consistency/InternalRenamingLookup.vo
```

Isolated compilation uses copied source and the following command shape;
`-time` was additionally supplied for InternalBinary, BinaryRealization and
ScopeRealization. Change the last directory/file to the recorded module:

```sh
opam exec -- rocq compile \
  -Q /Users/akuklev/air/pts-rk/_build/default/theories PTSrk \
  -Q /Users/akuklev/air/pts-rk/_build/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /Users/akuklev/air/pts-rk/_build/default/theories/self_consistency PTSrk.SelfConsistency \
  -Q /tmp/pts-rk-code-substitution.7UZL7A PTSrk.SelfConsistency \
  /tmp/pts-rk-code-substitution.7UZL7A/CodeSubstitution.v
```

Isolated logs and actual attempts:

- `/tmp/pts-rk-code-substitution.7UZL7A`: attempts 01–03 exit 1 with reused
  induction names (`n`, `f`, `b`); renamed locals. Attempt 04 exits 1,
  `Cannot find witness`: supplied the explicit arguments to
  `raw_rename_preserves_scope` and the scoped environment hypothesis before
  arithmetic. Attempts 05 and 06 exit 0; 06 includes the independent Replaced
  graph and exactness/preservation theorems.
- `/tmp/pts-rk-internal-binary.UogCHM`: InternalBinary attempt 01 exits 1
  for an uninferred Boolean parameter; made it explicit. Attempt 02 exits 1
  with checker `Undecided` at the odd-carry constructor; increased its fuel
  from 512 to 1024. Attempt 03 exits 0. BinaryRealization `realization-01.log`
  exits 1 because the term `positive` shadows the native datatype; qualified
  two annotations as `BinNums.positive`. `realization-02.log` exits 0.
- `/tmp/pts-rk-internal-scope.Oa2QER`: attempt 01 exits 1, checker fuel
  exhaustion at index-zero; 02 exits 1 because InternalBinary occurs in
  both temporary and default paths. Removing the redundant path fixes that.
  Attempts 03/04 exit 1 with `Undecided` at index-zero/index-step. Increased
  only evaluation fuel; attempt 05 exits 0, including scope generation.
- `/tmp/pts-rk-scope-realization.jnoHcv`: attempt 01 exits 0. At that time,
  additionally supplied `-Q /tmp/pts-rk-internal-scope.Oa2QER
  PTSrk.SelfConsistency` before the module's own isolated path. Once the
  default Scope object exists, omit this extra path to avoid duplicate files.
- `/tmp/pts-rk-renaming-lookup.ate2xs`: attempt 01 exits 1 for duplicate
  InternalBinary paths; attempt 02 passes after using one consistent
  dependency path. The default Dune rebuild subsequently passes.
- `/tmp/pts-rk-internal-renaming.LM9OJj`: attempt 01 exits 1 with checker
  `Undecided` at the binder constructor, fuel16384; increased to65536.
  Attempt 02 exits 1 with inconsistent InternalScope assumptions from a
  stale isolated InternalRenamingLookup object. Attempt 03 uses the consistent
  default dependencies; both binder cases pass, then application fuel16384
  exhausts (`Undecided`, exit1). Attempt04 was explicitly cancelled early,
  exit143, to settle the final evaluation budgets before replaying prerequisites;
  not a proof failure or timeout. Attempt05 uses binder/app fuel65536,
  final formation16384 and final fold262144. It passes, exit 0, with all
  11 declarations checked. Filesystem timestamps: 00:44:53–00:58:24 UTC,
  811 seconds. The final term starts around 00:55:22 and takes about 182
  seconds. Source unchanged after the fresh audit's initial manifest;
  workspace and compiled-copy SHA-256 both
  `92e19804ee56b7ee9ed96cdd278f9e7c08ed3b433911d61e08d1a2e8c63d397a`.

Successful isolated runs may report logical-loadpath remapping and harmless
large-natural-literal warnings. Fuel increases only allow the sound checker
more evaluation steps; no check or proof obligation is removed.

## Fresh audit: compilation/reports passed, recursive check timed out

```sh
bash docs/direct-r-handoff/verification/self-consistency-substitution-2026-10-23/AUDIT.sh
```

Up-front limits: 1800 seconds for the fresh dependency build, 300 for fresh
public reports, and 2400 for recursive checking of the **new complete
dependency closure** rooted at `CodeSubstitution`, `ScopeRealization`, and
`InternalRenaming`. Pristine build/check limits remain 300 seconds each.
The pristine revision is `723cf2ec61c737ae82ba33d2e7db44f650122b0e`.

The script recompiles **all public assumption reports** in a fresh absolute
Dune directory. It is designed to recursively kernel-check the three new roots
and their entire dependency closure, compare that closure's complete assumption/
unsafe inventory to freshly rebuilt pristine upstream, and check source stability
and unchanged original kernel files. The timeout prevents completion of these
stages in this run. It does **not** rerun recursive kernel
checking of every old module. Those 27 unchanged proof sources have their
separate prior full audit (`self-consistency-relational-2026-10-23`), with
283/283 closed reports and exact pristine inventory agreement. This scope
distinction is intentional and must remain visible in the final results.
Repository CI is unchanged; this is not full CI.

Started 00:46:00 UTC against the frozen attempt05 source, in parallel with
isolated compilation. Any subsequent proof edit must supersede this audit;
the before/after manifest detects such changes. Logs:
`_build/self-consistency-substitution-audit.FlM4MI`; fresh absolute Dune
directory `/tmp/pts-rk-substitution-fresh.NONg0M`; pristine
`/tmp/pts-rk-substitution-pristine.qcNAzd`.
All 102 new Theorem/Example declarations are registered (385 total reports).
Fresh dependencies pass at 01:05:26 UTC, exit 0, 1156 seconds from 00:46:10.
All **385/385** fresh assumption reports are closed at 01:06:20. Recursive
checking ran 01:06:20–01:46:20, then exited **124** at the up-front 2400-second
limit. Its log contains loadpath warnings but no proof error and no completed
`CONTEXT SUMMARY`. The process has ended. This is a timeout, not a successful
independent recheck; no complete new-closure inventory equality is established.
The script stopped before inventory/original/source-after/stability stages.

Separate post-timeout checks below all exit 0. Logs are in the progress
directory; the source manifest still exactly matches the pre-build snapshot.
The prior audit's 27 proof modules and original/common sources remain byte-
identical, excluding the intentionally extended Audit.v and Dune registration.
HEAD remains `6a8dc984fb59a9b3743503cd405ffe59a31d1978`; the index is empty.

```sh
shasum -a 256 theories/*.v theories/dune theories/Interpretation_of_R/*.v \
  theories/Interpretation_of_R/dune theories/self_consistency/*.v \
  theories/self_consistency/dune \
  > _build/self-consistency-substitution-progress/sources-after-timeout.log
cmp _build/self-consistency-substitution-audit.FlM4MI/sources-before.log \
  _build/self-consistency-substitution-progress/sources-after-timeout.log
shasum -a 256 -c _build/self-consistency-substitution-progress/final-sha256.log \
  > _build/self-consistency-substitution-progress/final-hashes-checked.log
shasum -a 256 -c <(rg -v 'self_consistency/(Audit.v|dune)$' \
  _build/self-consistency-relational-audit.ILJDGV/sources-after.log) \
  > _build/self-consistency-substitution-progress/prior-unchanged-final.log
git diff --exit-code 723cf2ec61c737ae82ba33d2e7db44f650122b0e -- \
  theories/Syntax.v theories/AbstractRewriting.v theories/Congruence.v \
  theories/Reduction.v theories/Confluence.v theories/DefEq.v theories/Context.v \
  theories/Typing.v theories/Inversions.v theories/Preservation.v \
  theories/SN.v theories/Ranks.v \
  > _build/self-consistency-substitution-progress/original-unchanged-final.log
git diff --cached --exit-code
```

### Proposed next verification command — NOT RUN

After confirming the same source manifest, use the pinned environment above
and retry only the independent check against the already fresh objects:

```sh
opam exec -- timeout 7200 rocq check -silent -o \
  -Q /tmp/pts-rk-substitution-fresh.NONg0M/default/theories PTSrk \
  -Q /tmp/pts-rk-substitution-fresh.NONg0M/default/theories/Interpretation_of_R Interpretation_of_R \
  -Q /tmp/pts-rk-substitution-fresh.NONg0M/default/theories/self_consistency PTSrk.SelfConsistency \
  PTSrk.SelfConsistency.CodeSubstitution \
  PTSrk.SelfConsistency.ScopeRealization \
  PTSrk.SelfConsistency.InternalRenaming \
  > _build/self-consistency-substitution-progress/kernel-retry.log 2>&1
```

Record its actual exit code/timestamps and compare its completed
`CONTEXT SUMMARY` with `pristine-kernel.log` from this audit. A source edit
instead requires a fresh build/report audit. No proof skipping or CI weakening
is authorized by this resource limitation; the recorded script retains its
original limits. Compositional typing proofs may reduce rechecking cost, but
must preserve the original terms and contracts.

## Note/PDF

```sh
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
mkdir -p _build/self-consistency-substitution-progress/pdf
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift \
  theories/self_consistency/DIRECT_ROADMAP.pdf _build/self-consistency-substitution-progress/pdf
```

Build 01 in `/tmp/pts-rk-consistency-note.FTStli` fails validation for two
overfull lines (27.34274pt at line 670 and 14.90659pt at lines 825–831);
the existing PDF is retained. Build 02 in
`/tmp/pts-rk-consistency-note.PjosAi` passes with clean diagnostics.
The PDFKit inspector passes: 15 nonempty pages, four links, required text
and mathematics, all-page rendering. Changed pages 11–15 were
visually reviewed. Exact logs: `note-build-01.log`, `note-build-02.log`,
`pdf-inspection-01.log` in the root progress directory above.

No staging, commit, push, cleanup, or unrelated development edits are part
of this continuation. Existing dirty work is preserved.
