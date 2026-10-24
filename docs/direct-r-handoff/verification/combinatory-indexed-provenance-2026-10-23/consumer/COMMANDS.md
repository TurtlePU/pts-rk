# Internally varying query soundness — 2026-10-23

New source only: theories/CombinatoryLogic-rk/IndexedHornSoundness.v.
No preceding proof, Dune registration, shared note, kernel or Agda source
was changed. The original IndexedHornEncoding.v remains frozen.

The reproducible CHECK.sh and KERNEL.sh scripts record exact commands,
UTC start/end times, outputs and exit codes for every isolated run. They use
the pinned Rocq 9.2 / OCaml 4.14.2 environment. Existing dependency objects
come from the preceding fresh 63-module build plus the new isolated indexed
encoding, type-dispatch and realization workers. This is not a fresh full
library audit.

Compile attempts 01 through 06 return 1. Attempt 01 needs explicit table
values in the selector-beta theorem to avoid higher-order inference choosing
truth a for its selector index. Attempts 02 through 06 reach the same bound
variable typing proof; two use temporary Show diagnostics. The needed
renaming must use the literal eta-expanded fsucc function in Syntax.shift,
not a syntactically different rewrite pattern. No definition or theorem
statement is weakened. Attempt 07 passes, 20:45:06–20:45:08 UTC, exit 0,
printing 16 closed public reports. All diagnostics are removed from source.

The recursive kernel check passes, with timestamps in kernel.start/kernel.end
and status in kernel.exit. Its whole context inventory is byte-for-byte equal
to the fresh pristine inventory from the preceding audit:

```sh
diff -u \
  <(sed -n '/CONTEXT SUMMARY/,$p' _build/combinatory-internal-horn-audit.JMyhh0/upstream-kernel.log) \
  <(sed -n '/CONTEXT SUMMARY/,$p' /tmp/pts-rk-indexed-consumer.qBciO2/kernel.log)
```

The comparison returns 0: only inherited functional_extensionality_dep,
no type-in-type, unsafe fixpoints or assumed positivity. Every new public
endpoint itself has a closed assumption report. Scoped whitespace checks pass.

Frozen 224-line source SHA256:
3b3ac5305ab95b2338ff932e7861be3d51a89e6eb7e674ea449a50d8d6e12257.

The original-PTS term uniform_reflect has literal type
`Π q:Code_k. Proof_cs(q) -> truth_predicate(q)`, formed at U_4.
It accepts arbitrary open query terms and proof inhabitants, without using
canonicity or selector exhaustiveness. Canonical-query output computes to
the independent Boolean truth proposition by ordinary beta conversion.
Model validity supplies actual clause witnesses, not an assumed target proof.

The fixed clause list, support and Boolean table remain external parameters.
Exact source correspondence at supported atoms uses canonical finite indices;
arbitrary positional aliases need not inherit source derivability. No uniform
budget-polymorphic raw-source theorem or runtime/code-size bound is claimed.
