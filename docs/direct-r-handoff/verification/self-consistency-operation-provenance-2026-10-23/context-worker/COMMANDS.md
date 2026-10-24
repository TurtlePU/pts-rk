# Original contextual lookup: isolated checks

Worker owns only new repository source
`theories/self_consistency/InternalContextLookup.v`. No older source, Dune
registration, audit registration, Git index, or global document was edited.
Objects and diagnostic logs live only in this worker directory.

Working directory: `/Users/akuklev/air/pts-rk`.
Worker directory: `/tmp/pts-rk-context-lookup.9QUeXr`.

Every invocation used the pinned environment in CHECK.sh and the command
`bash /tmp/pts-rk-context-lookup.9QUeXr/CHECK.sh attempt-NN`.
Each invocation records its resolved command, UTC start/end, source SHA-256,
exit and complete timed compiler output in matching attempt-NN files.
CHECK.sh is the latest wrapper; historical .command files are authoritative.

Dependencies reuse `/tmp/pts-rk-source-provenance-fresh.yW2QOO` objects.
Because that closure does not contain renaming, dependency-links contains
symlinks to only the missing .vo files from the unchanged replacement build
`/tmp/pts-rk-replacement-fresh.87Hwa9/default/theories/self_consistency`.
It also links the checked InternalJointTraversal helper object from
`/tmp/pts-rk-joint-resources-fresh.TqBIPV/default/theories/self_consistency`.
No object copies or duplicate logical-module providers were introduced.
The parent-owned NamedBeta helper is loaded from
`/tmp/pts-rk-context-provenance.pPeQ4L` once introduced in attempt07.

Attempts:

- 01: exit1, latest closure lacked InternalBinary/renaming dependencies.
- 02: exit1, mapping the entire older closure duplicated StructuralCodes.
  Missing-only symlinks resolve this without copying objects.
- 03: exit1, manually interrupted the expensive inline zero constructor.
  Its tactic finished139.008s, Qed was interrupted140.326s; no completed
  zero-constructor theorem or full compilation is claimed from this attempt.
- 04: exit1, missing InternalJointTraversal helper object after proof factoring.
- 05: exit1, manually interrupted four-step head normalization when it
  expanded large closed annotations to about13GiB RSS. Shared context/body
  proofs had passed; the conversion did not complete.
- 06: exit1, isolated check_conv finished35.901s but exhausted16384 fuel.
  This was inconclusive conversion checking, not mathematical rejection.
- 07: exit1, proactively interrupted to correct the newly supplied generic
  beta helper's argument order; no theorem failure was diagnosed.
- 08: exit1, generic beta structure worked but evaluate_close needed its
  explicit closedness proof argument. Added eq_refl in both places.
- 09: exit1, both constructor conversions and constructors completed.
  Interrupted the expensive monolithic scope-template check after87.5s
  to share its binder context as well. No scope theorem claimed here.
- 10: exit1, all constructor and scope-body proofs closed. The scope body
  tactic took75.224s and Qed74.705s. The final template's definitional type
  comparison was interrupted194.081s in; no final theorem claimed.
- 11: exit1, structural telescope-product proof reached evaluate_close;
  generic rewriting could not infer the dependent name-list index.
- 12: exit1, proactively interrupted once a small independent probe showed
  that even explicit dependent rewriting failed. No theorem failure was
  diagnosed at the interrupted location.
- 13: exit0, complete final module. UTC2026-10-23T19:12:30Z through
  19:16:41Z (251s wall). The proved structural telescope-product equality
  and explicit equality composition avoid expanded closed annotations.
  Scope body tactic74.071s, Qed73.858s; final template assembly0.030s,
  Qed0.029s. Both helper parameters are discharged in the final theorem.

Small syntax probes (not alternate correctness assumptions):

- probe01 was an unwrapped command at2026-10-23; exit1 (0.041s):
  `opam exec -- rocq compile -Q /tmp/pts-rk-source-provenance-fresh.yW2QOO/default/theories PTSrk -Q /tmp/pts-rk-source-provenance-fresh.yW2QOO/default/theories/Interpretation_of_R Interpretation_of_R -Q /tmp/pts-rk-source-provenance-fresh.yW2QOO/default/theories/self_consistency PTSrk.SelfConsistency -Q /tmp/pts-rk-context-lookup.9QUeXr PTSrk.SelfConsistency /tmp/pts-rk-context-lookup.9QUeXr/Probe.v`.
  Same pinned environment as CHECK.sh; missing NamedTemplates loadpath.
  Its output was retained in the tool transcript, not a raw log file.
- probe-02 exit1: independent diagnostic reproduced dependent rewrite failure.
- probe-03 exit1: eq_trans worked; the deliberately tiny test's final target
  omitted the closed-term zero-renaming identity. No repository proof changed
  from this diagnostic discrepancy.
- scope-probe-01 exit1: mechanical definition-only extraction missed inline
  Qed terminators, so the scratch source lacked CtxLookup. Fixed extraction.
- scope-probe-02 exit1: missing parentheses in the new change tactic.
- scope-probe-03 exit1: change could not infer an RHS placeholder; supplied it.
- scope-probe-04 exit1: dependent rewrite failed after structural tail equality.
- scope-probe-05 exit0 (0.259s): the EXACT repository definitions and new
  telescope-product equality compiled; eq_trans/f_equal avoids the problematic
  dependent rewrite and keeps all closed fragments opaque. This definition-only
  scratch file contains no typing claims, axioms, assumptions or admissions.
  It is not a substitute for compiling the complete module in attempt13.
- scope-probe-06 exit0 (0.648s): independently tested final template assembly
  as a generic lemma from context well-formedness and body typing, using the
  same original telescope-abstraction theorem. Those two ordinary native
  premises are proved concretely in the complete module, not assumed there.
  The final assembly tactic and Qed together took0.146s.

PROBE.sh records exact commands, source hashes, start/end and exits for every
wrapped diagnostic. Temporary ScopeProbe files are proof-engineering scratch,
not additional repository modules or exported proof dependencies.

Final source SHA-256:
`0d0e02f986f0ca28e776356b4648ff77964faf5bd187e8b94246a9fa5be0befb`.
Final worker object SHA-256:
`84190d807c3860b7813e53851206c382dfef2e8c281b6d2d21857fc4e24018c2`.
The object is137KiB and is not intended for repository archival.

`bash /tmp/pts-rk-context-lookup.9QUeXr/REPORT.sh` exited0,
UTC2026-10-23T19:17:13Z through19:17:14Z. All15 public Check/Print
Assumptions pairs are present and all15 reports say
`Closed under the global context`. The exact report command and full output
are in report.command and report.log. Scoped git diff --check exited0.

What is proved: independent literal-context guard and original Context.index
zero/successor graph constructors, at fixed ranks14–19, retaining every
annotated shift; an actual closed PTS consumer gives output scope for any
represented lookup witness. What is NOT proved: arbitrary-witness endpoint
functionality/coherence, internal extraction from proof-context certificates,
dependent typing preservation, checker soundness, or milestone4.

All changes so far preserve the literal public graph terms and argument order.
Factoring uses original native typing, well-formedness and beta rules; it does
not change the calculus or trust a second typing judgment. No unsafe checking,
axioms or admissions were added. Full fresh dependency/kernel verification
belongs to the parent integration audit, not these reused-object checks.
