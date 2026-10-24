# Independent Church Horn proof encoding — 2026-10-23

The worker adds only HornProofEncoding.v and this evidence directory. Existing
proof files and Dune registrations are unchanged by this worker. Compilation
uses the pinned Rocq 9.2 environment and previously fresh dependencies from
`/tmp/pts-rk-mm0-bridge.IH9mrh/default/theories`. The isolated new object is in
`/tmp/pts-rk-horn-encoding.vF7hVq`; it is not a whole-repository fresh build.

```sh
bash docs/direct-r-handoff/verification/combinatory-internal-horn-2026-10-23/encoding/CHECK.sh attempt-01
bash docs/direct-r-handoff/verification/combinatory-internal-horn-2026-10-23/encoding/CHECK.sh attempt-02
bash docs/direct-r-handoff/verification/combinatory-internal-horn-2026-10-23/encoding/KERNEL.sh kernel-final
```

Attempt 01 fails in the renaming proof: replacing variables by their renamed
images needs an explicit naturality equality. Attempt 02 repairs that proof,
passes, and prints 18 closed public assumption reports. It changes no syntax
definition or theorem statement from attempt 01. The successful complete
recursive kernel check runs 19:45:17–19:45:29 UTC, exit 0. Its whole context
inventory is byte-for-byte equal to the fresh pristine inventory recorded by
the preceding final MM0 audit:

```sh
diff -u <(sed -n '/CONTEXT SUMMARY/,$p' _build/combinatory-mm0-bridge-audit.BLPblO/upstream-kernel.log) <(sed -n '/CONTEXT SUMMARY/,$p' docs/direct-r-handoff/verification/combinatory-internal-horn-2026-10-23/encoding/kernel-final.log)
```

This comparison returns 0: inherited functional_extensionality_dep only; no
unsafe fixpoints, type-in-type, assumed positivity or rewrite rules. Every
compile/check attempt has exact commands, output, UTC times and exit status
in the corresponding evidence files. A read-only probe initially sought the
pristine log inside the temporary tree; that path does not exist. The actual
preceding fresh-audit log named above exists and is the compared source.

The independent Church type quantifies one `X : U_1` for every atom and one
curried handler for every selected clause. Its formation rank is between one
and three, independently of the number of atoms and clauses. The bound is a
type-formation rank, not a redex-rank or generated-code-size bound.

`specialize_typed` applies to an arbitrary native inhabitant, under an
arbitrary context and at arbitrary supplied atom types of sort U_1. It derives
the handler telescope by literal simultaneous substitution. No model, truth
table, source proof tree, normalization or canonicity is used in this module.
This is a representation and elimination interface for each externally fixed
finite theory; it does not internally quantify over fragment descriptions.
