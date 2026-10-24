# Indexed Horn transport

New source: `theories/CombinatoryLogic-rk/IndexedHornTransport.v`.
No preceding proof, Dune file or original kernel file was edited.

Final SHA256:
`841fd328d821e409016f0f38ae4a335b2205cb2fec671813548f560d5e002c5c`.

The module contains 27 public `Print Assumptions` reports, all closed.
The original PTS term `uniform_transport f cs ds` has type
`Π q : Code_k. Proof_cs(q) → Proof_ds(map_f q)`, of rank exactly four.
The sole theory-map premise says each literal mapped source clause occurs
in the target list. Query and proof may be arbitrary open typed terms;
there is no selector-canonicity, source-generation or model premise.
`canonical_query_transport` additionally proves the target canonical
selector result by actual beta reduction. Clause inclusion permits arbitrary
target ordering, duplicate clauses and unused target clauses.

The proof first pulls back the arbitrary target predicate along the literal
Church finite-map program. Its application to any query beta-reduces to
that predicate on the mapped query. At source selectors, the table reduces
to the corresponding target selector. A source body thus reduces to the
mapped-clause body. Independent handler selection implements clause inclusion.

## Verification

Commands, UTC start/end times, exit codes, source snapshots and hashes are
retained separately for every attempt. Run `bash CHECK.sh attempt-name`
from the repository root with this checkpoint's full script path.
The script uses pinned Rocq 9.2 / OCaml 4.14.2 and dependencies from
`/tmp/pts-rk-indexed-provenance.cjt8S0/default/theories`; the new object is
under `/tmp/pts-rk-indexed-transport.rdQzB4`.

| Attempt | UTC start–end (2026-10-23) | Exit | Result |
| --- | --- | --- | --- |
| 01 | 22:40:44–45 | 1 | Expanded substitution no longer matches folded lemma. |
| 02 | 22:40:59–59 | 1 | Target clause projection not reduced by body rewrite. |
| 03 | 22:41:07–07 | 1 | Same projection mismatch. |
| 04 | 22:41:18–19 | 1 | Explicit target change reveals unfolded lifted body. |
| 05 | 22:41:35–36 | 1 | Diagnostic goal retained for the same mismatch. |
| 06 | 22:41:44–44 | 1 | Shift occurrence index selected the wrong term. |
| 07 | 22:41:51–52 | 1 | Shifted query rewrite requires explicit renaming shape. |
| 08 | 22:42:01–02 | 1 | Diagnostic goal retained for that rewrite. |
| 09 | 22:42:10–11 | 1 | Explicit lambda needed to match the shift renaming. |
| 10 | 22:42:23–24 | 0 | Exact mapped-list transport; 13 closed reports. |
| 11 | 22:43:31–33 | 0 | Final general transport; 27 closed reports. |

Full recursive `rocq check -silent -o` passes, exit zero,
22:44:01–22:44:14 UTC; exact command is in `kernel.command`.
The entire normalized context inventory equals the preceding checkpoint's
fresh pristine inventory byte-for-byte: inherited
`functional_extensionality_dep` only, no unsafe fixpoints, assumed positivity,
type-in-type or rewrite rules. This isolated check reuses preceding
dependencies; the parent task performs a fresh integrated audit.

Initial inventory comparison removed trailing horizontal whitespace but kept
an extra final blank line and therefore failed with EOF on the pristine
report. The sole diff is that blank line, retained in `inventory.txt`.
The successful `inventory-normalized.txt` comparison also removes trailing
blank lines, leaving one final newline; no inventory entry is changed.

No theorem was weakened to repair elaboration. The terms do not assume a
semantic source-reflection theorem. Fixed fragment parameters and the atom
map remain metalevel data; no internal budget-polymorphism, Church code
exhaustiveness or independent consistency theorem is claimed.
