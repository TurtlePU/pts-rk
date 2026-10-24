# Guarded finite carriers

GuardedFiniteCarriers.v compiles in isolated `/tmp/pts-rk-guarded-carriers.mPsQdQ`
against the previously audited `/tmp/pts-rk-quantified-models.uhpkYv` build.
Attempt 12 exits 0 and prints 28 closed public assumption reports. The
source manifest records the compiled bytes. No compiled artifacts were
written to the source directory.

Complete recursive `rocq check -silent -o` exits 0, with no dependency
skips or admissions. Its entire context inventory matches the earlier
fresh pristine inventory byte-for-byte: inherited
`functional_extensionality_dep` only and no unsafe entries. The new public
theorems themselves are closed. This isolated verification does not replace
the root agent's integrated fresh build or full repository CI.

Exact commands, timestamps, exits and output are stored per attempt;
CHECK.sh and KERNEL.sh reproduce the successful commands. Versions.log
records Rocq 9.2 / OCaml 4.14.2. Attempts 1–8 fail on local notation/tactic
issues; attempt 9 succeeds for the core carrier. Attempts 10–11 fail on a
missing explicit import and intro-pattern spacing in the added native
wrappers; attempt 12 succeeds for the final complete module. No checks
were weakened and no assumptions added.

The finite carrier is `option (Fin (length xs))`, including one overflow;
positions do not require quotienting or proof irrelevance even if `xs` has
duplicates. Complete enumeration has exactly `1 + length xs` entries.
Encoding is injective on listed values. Every non-overflow result of the
heterogeneous lifted unary/binary/ternary operations is characterized by
decoded inputs and independent output membership.

Native carriers enumerate original annotated `Term nat scope`, filtering
depth-bounded terms by node count and a finite universe alphabet. The
admission guard is exactly `nodes t <= size /\ depth t <= depthBound /\
Uses alphabet t`. No typing or desired soundness fact occurs in it.
Fixed-budget app/Pi/lam/substitution are total; their exact decoding laws
retain the necessary output guard. Every original native term has its
own explicit size/depth/alphabet envelope. The finite enumeration capacity
is bounded by `1 + tower 2 (3*depthBound + scope + length alphabet + 4)`.

Only the new proof module and this verification subdirectory were edited.
No staging, commit, cleanup, Dune/shared-document edits or unrelated changes.
