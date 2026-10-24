# Unverified candidates: not build inputs

None of these draft files is included in the Rocq theory or counted among
the checked public endpoints.

- InternalJointTraversal.v.draft preserves the unfinished constructor/fold
  candidate from the worker directory. Its full proof did not compile;
  expansion-heavy checks were interrupted or killed. The actual theory keeps
  only the independently compiled carrier/projection/guard-formation prefix
  and reusable native helper lemmas.
- JointTraversalRealization.v.draft is the root's proposed integration. It
  was never compiled because its prerequisite did not finish. Its equations
  and executable constructions are design work, not established theorems.
- BetaProbe.v.draft and SortedProbe.v.draft preserve failed proof-engineering
  experiments. Their exact commands, errors and interruption statuses are in
  the joint worker ledger and logs.

The first final whitespace check found one extra empty line at the end of
BetaProbe.v.draft. Only that trailing empty line was removed from this display
copy; no declaration or proof was changed. The BYTE-EXACT original is also
retained as raw evidence in BetaProbe.original.txt, SHA-256
7924cff02ae6523d92c260402d5c9bf13887ef669166f668e6e9c8eada2b0e0f.
The formatted display copy has SHA-256
613399795c75ef010d5ff307dee31e2883a501359b49b6acbb98153a40a0f571.
The worker original is unchanged. The failed final-check attempt is retained
under final-checks-01; raw historical evidence is not silently rewritten.

The second final check found the same extra trailing empty line in the full
candidate display. With the root's explicit authorization, ONLY that final
empty line was removed from InternalJointTraversal.v.draft. The checked
theory sources were not altered. The failed check is retained under
final-checks-02, and both versions of the candidate are durably preserved:

- Byte-exact InternalJointTraversal.original.txt:
  5e5833e624e2bbdaf4796d4c8352ac1e9d27cdbf033ff772d9f145c2b8423551.
- Display InternalJointTraversal.v.draft:
  42e836bb35c89b7939ac5db77b7ef2295964802c74e3bec4eef71043a2b0e243.

Resource exhaustion or interruption does not refute the mathematical
construction. Conversely, successful intermediate tactics do not establish
an unfinished theorem or module. The fresh audit covers only registered
sources under theories and the declarations listed in JointResourceAudit.

No draft is patched with an admitted proof or unsafe checking option. The
preserved source is evidence for resuming work, not a source of trusted facts.
