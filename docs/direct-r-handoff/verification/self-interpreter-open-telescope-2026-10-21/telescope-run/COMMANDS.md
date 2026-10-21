# Contextual applications, original checker and dependent decoder

Date: 2026-10-21. Working directory: /Users/akuklev/air/pts-rk.
Toolchain: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1, opam 2.6.1.
Raw evidence: `_build/telescope-run.rwugef`.
Fresh absolute build directory: `/tmp/pts-rk-telescope-run.QR0a4s`.

Every numbered build uses the following command, with TARGET and NN replaced
by the module/attempt below. Standard output and error are retained in the
corresponding raw log; the shell exit code is retained in the .exit file.

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-telescope-run.QR0a4s --display=short --no-buffer theories/self_interpreter/TARGET.vo > _build/telescope-run.rwugef/NN.log 2>&1
status=$?
printf '%s\n' "$status" > _build/telescope-run.rwugef/NN.exit
exit "$status"
```

ContextualTelescopeRun, attempt-01 through attempt-08:

- 01: exit1, opaque TypedSub prevented index_base rewriting; added explicit change.
- 02–03: exit1, substituted-body rewriting needed explicit syntactic form.
- 04: exit1, diagnostic attempt inspecting that goal.
- 05: exit0, initial three endpoints.
- 06: exit1, pointwise variable substitution needed run_ext in run_rename.
- 07: exit1, unused forall n could not be inferred; typed sigma explicitly.
- 08: exit0, all 12 module assumption reports closed.

ConcreteContextualBeta, concrete-01 onward:

- 01: exit0, five initial uniform-field instantiation/application endpoints.
- 02: exit1, nonexistent ASCII lam_cong_par; original declaration is λ_cong_par.
- 03: exit0, eight closed reports, arbitrary concrete literal recovery and
  carrier/code-family argument typing.
- 04: exit1, implicit rank/carrier unresolved in code_argument_typed application.
- 05: exit0, 11 closed reports, original typing of all four concrete closures
  and concrete_apply_typed from independent original open input judgments.
- 06: exit1, carrier bound needed successor arithmetic.
- 07: exit1, family annotation rewriting did not match the generated domain.
- 08: exit1, diagnostic explicit goal; exact HA solved the first domain,
  and snoc-tail normality required an explicit telescope argument.
- 09: exit0, 15 closed reports including concrete normality.
- 10: exit1, explicit a<=S k carrier bound needed lia.
- 11: exit1, concurrently registered NNS source had not yet been created;
  no proof rejection in this module.
- 12: exit0, 19 closed reports, actual finite field typed/normal/recovering.
- 13: exit0, 20 closed reports including conversion injectivity.

RealizedEquality, equality-01: exit0, eight closed reports. Independently
typed normal reflexivity at the literal filled equality type, actual typed
context extension and unconditional literal payload erasure.

OriginalTypecheck, typecheck-01 through typecheck-07:

- 01–02: exit1, compact sort_retype tactic left parameters unresolved.
- 03: exit0, explicit original typing soundness.
- 04: exit0, completeness for every original typing rule.
- 05: exit1, uppercase S pattern parsed as the nat constructor.
- 06: exit1, infer_sort application needed the explicit source A.
- 07: exit0, eight closed reports, original check_iff plus regressions.

TelescopeInstantiation, instantiation-01: exit0, five closed reports.
Actual mixed substitution retains arbitrary ambient base variables while
instantiating all signature arguments, with independently proved original
TypedSub, literal substitution equations and run agreement.

DependentProgramDecoder, program-decoder-01 through program-decoder-12:

- 01: exit1, unapplied var needed eta expansion for explicit constructor args.
- 02: exit1, arr_apply needed the explicit represented carrier.
- 03: exit1, nonexistent rename_shift; the universe specialization is
  definitionally equal and needs no such lemma.
- 04: exit1, dependent elimination needed an explicit branch variable name.
- 05: exit1, target scope n needed a typed substitution parameter.
- 06: exit1, lift_closed at scope1 needed its explicit shift equation.
- 07: exit0, nine closed reports, actual ordinary P/Q decoder typing.
- 08: exit1, original typ_app implicit context is named Gamma, not G.
- 09: exit1, opaque arrow wrapper prevented substitution rewriting.
- 10: exit1, congruence lemma used scope0 inside the signature telescope.
- 11: exit0,18 closed reports including literal recovery and typed packaging.
- 12: exit0,26 closed reports including exact decoder-type formation rank,
  decoder/package normality, result-type recovery and closure injectivity.

All numbered .log/.exit pairs remain in the raw directory. Two rejected
apply_patch requests (duplicate Dune target; stale documentation context)
were atomic and made no edits; corrected patches were then applied.

## Scoped recursive kernel checks

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-telescope-run.QR0a4s/default/theories PTSrk -Q /tmp/pts-rk-telescope-run.QR0a4s/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-telescope-run.QR0a4s/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.ContextualTelescopeRun PTSrk.SelfInterpreter.ConcreteContextualBeta PTSrk.SelfInterpreter.RealizedEquality PTSrk.SelfInterpreter.OriginalTypecheck
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-telescope-run.QR0a4s/default/theories PTSrk -Q /tmp/pts-rk-telescope-run.QR0a4s/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-telescope-run.QR0a4s/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.TelescopeInstantiation PTSrk.SelfInterpreter.DependentProgramDecoder
```

Both exit0, logs kernel-01 and program-decoder-kernel-01. Inventory contains
only unchanged upstream dependent functional extensionality; no unsafe
fixpoints, assumed positivity or type-in-type. Own endpoints are all closed.
Independent full-source reviews pass for all six modules. No new aggregate
or pristine comparison/full CI is claimed at this in-progress checkpoint.

Frozen SHA256:

```text
cd696e9ff0eff915aed58bf7c8800969e8673bf19a18fefd10df683076f2b25d ContextualTelescopeRun.v
1cb271f46d7c4b1d00e14db87d5d18493da1039fa1628dfbe805b825e2bd75c9 ConcreteContextualBeta.v
a1f3f5e0c608f9809e8f224ab480bfa5408a47230e46aafb30c9e246f1260b2f RealizedEquality.v
d8a15e6fdc989357cafc2eaf0f15bbd05d42c047b792e96491a0c8c738113fae OriginalTypecheck.v
7914af53f55ded9bdbc46d92b15278f8c0346818012253b621221f60d0470964 TelescopeInstantiation.v
dbb5487efb2302afc1c712c8e93dc97ab1d8dfff5ee6837b7d844859f8f27fa8 DependentProgramDecoder.v
```

The generic decoder contract does not assert an all-source quotation.
No full dependent interpreter or general impossibility result yet.
No Git/index mutation.

## Later scoped additions (same toolchain/cache)

FaithfulProgramDecoder, faithful-decoder-01 through08:

- 01: exit1, package-type replacement rewrite did not match.
- 02: exit1, dependent Fin elimination needed explicit branch indices.
- 03–04: exit1, renaming equation required the syntactic renamed variable.
- 05: exit1, diagnostic goal inspection.
- 06: exit0, nine closed reports; explicit posed equation and cbn fixed matching.
- 07: exit1, decoder normality needed the explicit term-program normality lemma.
- 08: exit0,12 closed reports. Independent full-source audit PASS.

SourceQuotationBudget, source-budget-01 through03:

- 01: exit1, maxRankLiteral was not imported.
- 02: exit1, AutomaticBound did not expose the required RankEstimate name.
- 03: exit0,10 closed reports after explicit Rank/RankEstimate imports.
  Three independent reviews PASS, including recursive context extension and
  the U37:U0 rank-zero regression. No quotation-cost bound is asserted.

Recursive kernel commands use the same three -Q arguments above and targets
PTSrk.SelfInterpreter.FaithfulProgramDecoder and
PTSrk.SelfInterpreter.SourceQuotationBudget, respectively. Both exit0;
raw faithful-decoder-kernel-01 and source-budget-kernel-01 .log/.exit pairs.
Only unchanged upstream dependent functional extensionality appears in the
loaded inventory; all own reports closed, no unsafe checking modes.

```text
41d5c1d2cd985e8be2db019ed4eb966cdbcd6142a615814184440710a837f4da FaithfulProgramDecoder.v
2445dac3e1b18c31cd50748ac39124f4bad785185215a5c6c93d81f2642869dc SourceQuotationBudget.v
```

Seven completed build caches were removed with the pinned environment's
`dune clean --build-dir=EXACT_DIRECTORY`; all seven exit0. Each target was
inspected and confirmed inactive, with logs/evidence retained separately.
Only regenerable Dune outputs were removed, never sources or raw proof logs.
Raw cache-clean-N.log/.exit targets, in order:

1. /tmp/pts-rk-global-equality-insertion.kysmeL
2. /tmp/pts-rk-quotation-view-renaming.R1pU4W
3. /tmp/pts-rk-code-alignment.bCOFfn
4. /tmp/pts-rk-contextual-transport-law.crTjcS
5. /tmp/pts-rk-self-contextual-beta-audit.tzMxfv
6. /tmp/pts-rk-telescope-beta-signature.p1q5kv
7. /tmp/pts-rk-contextual-beta-signature.TOn0rm

Disk headroom after the second cleanup was799MiB. Active root/paper/audit/rank
caches were retained. A fresh aggregate audit/full CI remains pending.

Note build note-01 exits0,34pages; PDFKit inspection note-inspection-01 exits0.
Raw extraction/render directory /tmp/pts-rk-self-note.jwDG15. Visual inspection
of new pages29–30 passes (ordinary dependent decoder and checked layers).
Remaining changed pages and later mathematical additions still need review.

## Literal local-spine naturality

LocalSpineNaturality, local-naturality-01 through10, same build command/cache:

- 01: exit1, cbn unfolded present_push before its profile lemma could rewrite.
- 02: exit1, explicit close-type right side required instead of placeholder.
- 03: exit1, inverse cast-sort rewriting affected both sides; normalize the
  right-hand cast explicitly. The large LS alias was mechanically expanded.
- 04: exit0, complete closure/profile/telescope naturality tranche.
- 05: exit1, per-goal all selector applied a four-goal tactic to one goal.
- 06: exit1, scope equality compositions required proof elimination.
- 07: exit1, diagnostic goals identifying those equality compositions.
- 08: exit1, retelescope_close_type needed the same scope elimination.
- 09: exit1, backward renamed_body rewrite could not infer target context H.
- 10: exit0, six own closed reports including exact same-profile adapter,
  body/unbody renaming squares. Independent package-owner review PASS.

Recursive command uses the three -Q arguments above and target
PTSrk.SelfInterpreter.LocalSpineNaturality; local-naturality-kernel-01 exits0.
Only unchanged upstream FEdep inventory, no unsafe features. This check used
the previously built LS dependency; alias-only LS refresh will also be checked
in the next aggregate. Root naturality source is frozen:

```text
c3c9374b13cfa17867e5a583840068356593f26ad299521d1b41234ca3175abe LocalSpineNaturality.v
```

Note note-02 exits0, temp /tmp/pts-rk-self-note.OSFq1g. It adds faithful ACTUAL
program packaging, generic closed interpretation, executable source budgets
and literal local scope/state design. The all-source obligation is explicit.
New-page visual inspection pending. A transient duplicate Dune entry was
corrected immediately before the next build; no duplicate remains.

## Numeric family and open-source closure

IndexedProgramInterpreter, indexed-program-01 through03:

- 01: exit1, rewriting run_flatten required reverting its dependent Fin index.
- 02: exit1, term_program_type needed an explicit closed P scope.
- 03: exit0,13 own closed reports. Independent rank/audit reviews PASS.
  Interpreter parameters are only numerical ranks and a pure numeric plan;
  ordinary P/Q carry represented type and program. The actual signature/fill
  normality is derived, not assumed for source terms.

SourceClosure, source-closure-01 through04:

- 01: exit1, wrong existing rename lemma name rtc_rename.
- 02: exit1, extra Congruence import did not provide the nonexistent name.
- 03: exit1, corrected rename_rtc; a replace_var rewrite also hit the source
  closure's body, requiring a separately posed existing run_closed_term lemma.
- 04: exit0, five own closed reports. Executable literal annotated source
  closure, original derivation typing, reopening typing/recovery, injectivity.

local-naturality-11 exits0,6closed against refreshed alias-cleaned LS.
Combined recursive check indexed-program-kernel-01 exits0 for
LocalSpineNaturality, IndexedProgramInterpreter and SourceClosure, using the
same three -Q arguments, including refreshed LocalQuotationSpine dependencies.

```text
4759662a0bcdaa349f02339b423b2c5b4b9f613c766a5826827422610bc35a90 IndexedProgramInterpreter.v
466e25bcee112895bf63303572dc0300d4f6864c528df38a920f585f88d0ddf3 SourceClosure.v
```

Note inspection note-inspection-02 exits0:36pages, PDFKit renders/extracts in
/tmp/pts-rk-self-note.OSFq1g. Pages1,30–31 visually reviewed PASS. The raw
HOAS tag equations, exact formation-rank equation and literal-source budget
regression render correctly. Still no all-source coverage assertion.

Audit now adds511 Check/Print-Assumptions pairs for36 completed new modules
to the prior340 endpoints. The incremental aggregate-prepare-01 exits0;
this is preparation only, not the required fresh final aggregate/full CI.
Active LocalCodeAlignment/ApplicationQuotation/RecursiveQuotation are not
yet included at that preparatory checkpoint.

## Full-source assembly and final aggregate registration

FullDependentInterpreter, full-dependent-01/02:

- 01: exit0,13 own closed reports. Executable initial budget/state and six-case
  quotation, original closed/open coverage, normality and syntax fidelity.
- 02: exit0,14 own closed reports, adding literal represented-type recovery.
  Independent paper/rank/audit source reviews PASS. The final fresh aggregate
  and recursive kernel checks are owned by final-review/COMMANDS.md.

```text
5fc3541041f88ebc02435e66acf40a86e1a42eeea2db1fe62b65038052ee33fa FullDependentInterpreter.v
```

Audit subsequently includes LocalCodeAlignment, ApplicationQuotation,
RecursiveQuotation and FullDependentInterpreter, including type recovery:
885 public Check/Print pairs,107 proof modules,2229 total Print statements.
These source counts are not a substitute for the independent fresh audit.
Final proofs/Dune/Audit were frozen before that audit; documentation-only
updates do not change its source manifest.

Note-03 and note-inspection-03 exit0:37pages, temporary directory
/tmp/pts-rk-self-note.grxntW. New full-source theorem, abstract and explicit
rank-only boundary were added. Pages31,32,37 visually reviewed PASS.
Note-04 below supersedes this PDF after the final prose consistency review.

Completed exact scoped build caches /tmp/pts-rk-local-quotation-spine.nr1PlD
and /tmp/pts-rk-telescope-run.QR0a4s were verified inactive and cleaned with
pinned `dune clean --build-dir=EXACT` after a fresh-audit disk-exhaustion
failure. Raw cache-clean-8/9.log/.exit both exit0. About900MiB recovered;
sources and all raw verification logs were retained. Earlier cache-clean1–7
also exit0. No user source/data or unrelated build cache was removed.

## Final note and prose consistency

```sh
bash tools/build-self-interpreter-note.sh > _build/telescope-run.rwugef/note-04.log 2>&1
status=$?
printf '%s\n' "$status" > _build/telescope-run.rwugef/note-04.exit
exit "$status"
```

Exit0. Temporary directory /tmp/pts-rk-self-note.PfjEfO. Native PDFKit
inspection (pdfinfo/pdftotext/pdftoppm unavailable):

```sh
swift _build/telescope-run.rwugef/INSPECT-FINAL.swift /tmp/pts-rk-self-note.PfjEfO > _build/telescope-run.rwugef/note-inspection-04.log 2>&1
```

Exit0,37pages. Extracted all page text, rendered pages1,28–33,36–37;
pages1,31,32,37 visually reviewed PASS. Final abstract/theorem clearly assert
the positive numeric-plan construction and distinguish rank-only uniformity.
Earlier local-module limitations no longer contradict final source coverage.
The successful proof-erased sort regression is reported without general
runtime or direct dependent-record reduction claims.

```text
56b9453254cfbec524bee858c04b61c164b3916c70ab7326d921dd659b2bac16 PTS-rk_self_interpreter.tex
a2660b0e28f215d9ac22bee81113de4b4feacdd710fa8d32013738420915cfbd PTS-rk_self_interpreter.pdf
```

Final independent verification (see sibling final-review/COMMANDS.md):
all14 audit stages0, recursive kernel and both pristine inventory comparisons0,
frozen original kernel/NC/ZFC0,110stable manifest entries,226/226 fullCI stages
PASS. Fresh build reports2230closed:2229self-interpreter plus unchanged upstream
Ranks.strong_normalization. FINAL-CHECKS0; no source/theorem change was needed
after the frozen final manifest. Final prose-only patch had one stale-context
application rejected before mutation; the corrected patch succeeded. HEAD and
empty index unchanged; git diff --check0.
