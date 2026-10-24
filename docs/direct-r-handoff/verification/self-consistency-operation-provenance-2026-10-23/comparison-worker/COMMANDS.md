# Proof-indexed comparator graph development

Owned source: theories/self_consistency/InternalComparisonGraph.v.
No previous source, Dune, global documentation or index is modified.
Existing dependencies are from the previous freshly checked closure.
Every CHECK.sh attempt records its exact command, source hash, UTC times,
exit status and full compiler output. No deletion or fresh duplicate build.

1. `bash /tmp/pts-rk-comparison-graph.AaaC94/CHECK.sh attempt-01`
   Verify literal proof-indexed graph formation at calculated fiber rank 6.
   Exit1: unchanged NamedTemplates was not part of the previous build closure.
2. `bash /tmp/pts-rk-comparison-graph.AaaC94/CHECK.sh dependencies-01 /Users/akuklev/air/pts-rk/theories/self_consistency/NamedTemplates.v`
   Compile that unchanged prerequisite into the worker directory, exit0.
3. `bash /tmp/pts-rk-comparison-graph.AaaC94/CHECK.sh attempt-02`
   Exit0: fiber rank6 verified; 47.854s computation and45.182s Qed checking.
4. `bash /tmp/pts-rk-comparison-graph.AaaC94/CHECK.sh agreement-01 /tmp/pts-rk-comparison-graph.AaaC94/AgreementProbe.v 180`
   Isolated rank7 formation and small local-branch agreement probe; no source
   constructor proof or agreement is claimed until this finishes.
5. `bash /tmp/pts-rk-comparison-graph.AaaC94/CHECK.sh constructors-01 /tmp/pts-rk-comparison-graph.AaaC94/ConstructorProbe.v 240`
   Shared telescope/context certificates for the two finite tag families;
   no whole-constructor normalization repeated for every tag.
   Exit1: unchanged InternalJointTraversal was outside the previous closure.
6. `bash /tmp/pts-rk-comparison-graph.AaaC94/CHECK.sh dependencies-02 /Users/akuklev/air/pts-rk/theories/self_consistency/InternalJointTraversal.v`
   Compile the unchanged shared telescope proof infrastructure; exit0.
7. `bash /tmp/pts-rk-comparison-graph.AaaC94/CHECK.sh constructors-02 /tmp/pts-rk-comparison-graph.AaaC94/ConstructorProbe.v 240`
   Atom context verified; exit1 on incorrect tactic bracket scope after
   destructing29 tags (58 generated goals), not a typing/rank failure.
   Agreement01 timed out (exit124) after rank7 formation succeeded; whole
   agreement checking repeated the huge Trace context and is being factored.
8. `bash /tmp/pts-rk-comparison-graph.AaaC94/CHECK.sh helpers-01 /tmp/pts-rk-comparison-graph.AaaC94/HelpersProbe.v 60`
   A native, scope-polymorphic application rule reuses trace_sorted instead of
   rechecking the whole graph to establish a Trace fiber's formation.
9. `bash /tmp/pts-rk-comparison-graph.AaaC94/CHECK.sh constructors-03 /tmp/pts-rk-comparison-graph.AaaC94/ConstructorProbe.v 300`
   Fix the tactic grouping only; retain the shared context approach.
10. `bash /tmp/pts-rk-comparison-graph.AaaC94/CHECK.sh agreement-base-01 /tmp/pts-rk-comparison-graph.AaaC94/AgreementBase.v 150`
    Retain the already successful rank7 type formation separately, so later
    body probes do not rerun it.
11. `bash /tmp/pts-rk-comparison-graph.AaaC94/CHECK.sh agreement-shared-01 /tmp/pts-rk-comparison-graph.AaaC94/AgreementShared.v 180`
    Build the final context from previously proved Trace formation rather
    than asking the checker to reestablish it. Check only the fold body.
    Exit124: body checker still expands59 branch type conversions; no finished
    agreement proof. constructors03 also exits124 after atom-family success
    and pair-atom context formation; all partial logs retained.
12. `bash /tmp/pts-rk-comparison-graph.AaaC94/CHECK.sh local-branches-01 /tmp/pts-rk-comparison-graph.AaaC94/LocalBranchProbe.v 180`
    Factor closed branch proofs out of the large trace context before native
    typed-spine assembly. This attempt does not rerun graph formation.
13. `bash /tmp/pts-rk-comparison-graph.AaaC94/CHECK.sh constructors-04 /tmp/pts-rk-comparison-graph.AaaC94/ConstructorProbe.v 450`
    Infer the variable-headed body directly using the EXISTING infer_sound;
    avoid rechecking formation of its already inferred dependent output.
    Exit124: inference still eagerly traverses the large annotations. It used
    up to17.7GB RSS; no unchecked result is integrated.
14. `bash /tmp/pts-rk-comparison-graph.AaaC94/CHECK.sh native-constructors-01 /tmp/pts-rk-comparison-graph.AaaC94/NativeConstructorProbe.v 90`
    Use original tV and tApp directly; no checker re-inference at all.
    local-branches01 also exits124; CMP beta schemas replace that strategy.
    Exit1: NamedBeta rootworker was built against another NamedTemplates.vo.
15. native-constructors02 removes that unnecessary dependency; exit1 on direct
    tV unification. native03 makes the index explicit, exit1 because the tag
    must be split to compute its lookup. native04 proves head-variable shape
    first, but the remaining vm_compute index equality times out90s (exit124).
    native05 keeps closed payloads symbolic by structural renaming rewrites;
    exposing the assembled61-binder context still times out90s (exit124).
    These are preserved NativeConstructorProbe.v attempts, NOT checked endpoints.
16. beta-local01 compiles the unchanged root-owned NamedBeta source against
    this worker's NamedTemplates closure, exit0 (<1s).
17. scoped01/02 fail on unreduced lifted annotations, scoped03 exposes the
    successful method on atom_zip but fails on the next unconverted family.
    scoped04 (exit0) first changes each CLOSED type, then lifts it and rewrites
    original renaming/substitution plumbing, keeping operation payloads opaque.
18. scoped05 (exit0) adds checked atom and pair/atom Same inhabitants for every
    typed open input. scoped06 adds pair/pair, but exits1 at reflexivity because
    AbstractRewriting was not imported. scoped07 imports it and succeeds:
    all three local cases checked, no universal Trace fold asserted.
19. helpers02 exits1 because the root and local NamedBeta.vo files were both
    mounted under the same short import. The worker CHECK then unmounts the
    rootworker directory; boolean-local01 compiles unchanged BooleanAgreement
    locally (exit0). helpers03 exits0 with Trace formation/application and a
    symbolic four-head beta interface (no annotation normalization).
20. checkpoint01 compiles the merged14-endpoint source with a240s ceiling.
    Exact commands, hashes, UTC timestamps and statuses for every attempt
    above are in their matching .command/.source/.start/.end/.exit files.
    Exit0, UTC19:19:38--19:21:55 (137seconds). Source SHA256:
    219ddbce393b5f4b83a411957f0c8855ad5a04f887963ef65425dbeb00609866.
21. `bash /tmp/pts-rk-comparison-graph.AaaC94/CHECK.sh assumptions-01 /tmp/pts-rk-comparison-graph.AaaC94/CheckpointAssumptions.v 60`
    Exit0; all14 public endpoints freshly print Closed under the global context.
    Git whitespace check exits0; safety scan found no forbidden declaration.
    This worker verification reuses the previous fresh dependency closure;
    root owns the independently fresh final Dune closure/kernel audit.
