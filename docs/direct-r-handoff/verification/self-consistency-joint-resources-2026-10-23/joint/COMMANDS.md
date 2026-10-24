# Isolated joint traversal worker evidence

Working directory: /Users/akuklev/air/pts-rk.
Pinned environment: PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH;
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam; OPAMSWITCH=pts-rk-ci.

Every numbered compile uses this command (with its numbered log):

```
opam exec -- rocq compile -time \
 -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories PTSrk \
 -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/Interpretation_of_R Interpretation_of_R \
 -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/self_consistency PTSrk.SelfConsistency \
 -Q theories/self_consistency PTSrk.SelfConsistency \
 -Q /tmp/pts-rk-joint-traversal.97rvlT PTSrk.SelfConsistency \
 -o /tmp/pts-rk-joint-traversal.97rvlT/InternalJointTraversal.vo \
 theories/self_consistency/InternalJointTraversal.v \
 > /tmp/pts-rk-joint-traversal.97rvlT/attempt-NN.log 2>&1
```

- Attempt01: start 2026-10-23T10:32:32Z, deliberately SIGINT at
  10:43:14Z, actual exit1/User interrupt. Original atom constructor typing
  tactic completed in485.514s, but Qed was interrupted after114.551s.
  This was NOT a completed theorem/module. Literal terms/types preserved;
  optimized proof engineering shares one native well-formed context.
- Attempt02: exit1, parser error at dependent sigma type notation in
  lambda_parts, line117. Generic native telescope lemmas had passed.
- Attempt03: start10:56:37Z, exit1, wrong tactic goal arity in atom_body_typed.
  Shared final-context check passed6.279s + Qed5.849s.
- Attempt04: start10:58:15Z; deliberately SIGINT11:00:51Z; actual exit1.
  Full vm_compute on reconstruction was interrupted after89.728s without
  completing its tactic. Replaced with definitional reflexivity to preserve
  shared annotations rather than fully expanding them. Body-only proof
  already passed7.436s + Qed7.386s; context check passed6.298s +5.839s.
- Attempt05: start11:00:51Z; deliberately SIGINT11:04:04Z; actual exit1.
  Reconstruction by reflexivity still had not completed after125.27s.
  The public proof constructors are now assembled by the common telescope
  directly (same native lambda AST and annotation sequence), eliminating
  the redundant cross-representation reconstruction equality.
  Also incorporates the proved one-head
  reduction helper, independently tested by the parallel worker in
  /tmp/pts-rk-checker-resources.llVQ9U/ProductHead.v.
- Attempt06: start11:04:04Z, using `bash run.sh 06` (same command above);
  SIGKILL/exit137 at11:11:27Z while atom_result_beta was expanding. The
  unverified draft never completed this proof or the full module.
- SortedProbe: isolated formation-only source without any axioms/admitted
  proofs, source copied by apply_patch. First run exit1 at implicit argument
  inference in good_application_sorted; fixed with explicit lifted result
  sort. Second run deliberately SIGINT11:13:14Z/exit1 during definitional
  comparison of lift_closed C with shift C (198.929s). Third run printed the
  exact variable goal, then deliberately SIGINT11:15:27Z/exit1 at the same
  change (101.144s). These are proof-engineering limitations, not rank errors.
- BetaProbe: moved vm_compute before tag case splitting; deliberately
  SIGINT11:15:27Z/exit1 after218.572s. RSS just before interruption was
  31,571,072KiB. No theorem completed. No further large-expansion probes.
- Attempt07: start11:15:28Z, `bash run.sh 07`. Source trimmed to carrier,
  constructors, projections, independent guard TYPE formation, and four
  reusable native telescope/reduction lemmas. Full unfinished design archived
  as UNVERIFIED-JointTraversal-DRAFT.v outside theories; it is NOT build input.
  Completed11:15:54Z, exit0. A source-comment clarification during this run
  did not change declarations or proofs; root fresh audit uses frozen source.

Final assumptions report (exit0, ten Closed under the global context):

```
opam exec -- rocq compile \
 -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories PTSrk \
 -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/Interpretation_of_R Interpretation_of_R \
 -Q /tmp/pts-rk-comparisons-fresh.IyPIZj/default/theories/self_consistency PTSrk.SelfConsistency \
 -Q /tmp/pts-rk-joint-traversal.97rvlT PTSrk.SelfConsistency \
 /tmp/pts-rk-joint-traversal.97rvlT/Report.v \
 > /tmp/pts-rk-joint-traversal.97rvlT/assumptions.log 2>&1
```

Frozen source SHA256:
1582429b1062bb627456994ab38d5405bc51b447d3bfd60b43f278a947f9c5bb.
No full recursive kernel-inventory claim is made by this worker; the parent
fresh closure audit is separate. No active probe processes remain.

The probe compile command was identical to the numbered command above except
the repository-source -Q and -o arguments were omitted, and source was
/tmp/pts-rk-joint-traversal.97rvlT/SortedProbe.v or BetaProbe.v. Logs are
sorted-probe.log, sorted-probe-02.log, sorted-probe-03.log, beta-probe.log.
All probes used the same pinned environment and existing coherent dependencies.

The earlier files were not edited. Only the new InternalJointTraversal.v
is owned by this worker. No axioms, admits, unsafe switches, new PTS rules,
or weakened native typing target are used.
