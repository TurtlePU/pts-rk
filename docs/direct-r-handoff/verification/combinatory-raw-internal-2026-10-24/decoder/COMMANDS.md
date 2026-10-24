# Fixed internal raw decoder — 2026-10-24 local date

New proof source only: theories/CombinatoryLogic-rk/MM0InternalDecoder.v.
Existing proof modules, registrations, note and shared handoff files were not
edited by this worker. Dependencies use the preceding fresh 69-module build
plus the concurrently checked IndexedHornTransport object. This isolated
check is not a fresh full-library audit.

Pinned Rocq 9.2, OCaml 4.14.2. The executable CHECK.sh records exact commands,
UTC start/end times, exit status and complete outputs for every attempt.
It copies the current source into /tmp/pts-rk-mm0-internal-decoder.3D2W4B and
uses /tmp/pts-rk-indexed-provenance.cjt8S0/default/theories and
/tmp/pts-rk-indexed-transport.rdQzB4 as dependency loadpaths.

| Attempt | UTC on 2026-10-23 | Exit | Result |
| --- | --- | --- | --- |
| 01 | 22:43:09–10 | 1 | Singleton-list in_map inference failure |
| 02 | 22:43:16–19 | 0 | Foundation, 13 closed public reports |
| 03 | 22:44:22–24 | 1 | maps_into folded forall elaboration failure |
| 04 | 22:44:33–37 | 0 | Full decoder/proof transport, 19 closed public reports |
| 05 | 22:46:59–22:47:01 | 1 | Reverse rewriting under shifted proof type |
| 06 | 22:47:17–19 | 1 | Same elaboration after explicit target change |
| 07 | 22:47:28–30 | 1 | Same elaboration after eta-expanded renaming |
| 08 | 22:47:39–41 | 1 | Same elaboration with direct rename target |
| 09 | 22:47:56–22:48:02 | 0 | Composed raw truth soundness, 27 closed public reports |

No statement was weakened. The first repair supplies an explicit list-map
witness; the second supplies the full selected_clause_mapped function. The
final weakening proof rewrites an explicitly typed proof-variable hypothesis
forward with proof_type_rename, instead of rewriting the target backwards.

KERNEL.sh records the exact recursive kernel command and inventory diff.
The first 19-endpoint check passes at 22:45:02–32 UTC, exit 0. Its full inventory is byte-equal
to the preceding fresh pristine upstream report, comparison exit 0. Only
inherited functional_extensionality_dep occurs; no type-in-type, unsafe
fixpoints, assumed positivity or rewrite rules. The final 27-endpoint check
passes at 22:48:25–54 UTC, exit 0, with the same full inventory (diff exit 0),
using the separately retained kernel-final.* ledger. All 27 new public theorem
reports themselves are closed.

Frozen source SHA256:
db0a387ef493bf49af76555ae352286d5731bcce106b3dc215513237e739147c.
The preceding 19-endpoint snapshot was
9888b831b3ce0bd205373971b763de42c3144b9f908225c097b45190fbf8fd30;
its earlier kernel check is not final-source evidence.

decoded_soundness is a separately constructed closed internally quantified
query/proof function, also of type rank 4. It composes independent raw proof
translation with the raw least-model consumer, returning the raw truth
family at decoder q. arbitrary_query_decoded_soundness types the actual
double application to arbitrary open typed inputs. The least model premise
is discharged; no model or source-derivation premise occurs in its API.

## Mathematical boundary

Both semantic and raw supports are fixed before a query is supplied. Raw
reserve singleton lists ensure every semantic observation is represented;
they enlarge support only, not axioms or denial constraints. Decoder
computation preserves None as overflow and does not identify it with zero.
The literal mapped semantic clauses belong to the independently generated
raw clause list.

decode_proof is an actual original-PTS term with function type rank 4:
it accepts arbitrary open typed query q and proof p and returns a proof of
the independent raw indexed theory at decoder q. It does not require p to
be externally emitted, and its generic typing uses no canonicity.
Canonical selector computations and canonical source/no-overflow reflection
are separately stated. The latter closed-inhabitant converse uses the
existing external canonicity theorem. This is not uniform budget reflection
or an independent internal consistency proof; the fragment, budgets, tables
and supports remain fixed metalevel parameters.
