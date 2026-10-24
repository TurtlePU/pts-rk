# Raw MM0 guard/source provenance — 23 October 2026

Only MM0GuardProvenance.v is added to the proof tree. Root/development
READMEs, live STATE/DECISIONS/BUILD, relevant Dune/diffs and preceding audit
logs were read. No old proof source, original kernel, Agda/MM0 source, Dune
registration or shared handoff file was edited by this worker. No Git
staging, commit, push, process interruption or cleanup was performed.

The finite observation alphabet is None plus Some e for closed sorted raw
expressions satisfying the existing numerical guards. None is never identified
with Some EZ. Independent clipped evaluation agrees with every semantic
valuation, including ill-sorted and overflowing inputs. The raw named-entry
table retains literal axiom names and complete variable tuples. Its clause
membership is exactly the observation image of the entire existing semantic
table, including inactive identity clauses. Active entries derive closed
first-order substitution sorting, all size/depth bounds and exact argument
substitution. None of these admission checks uses typing, derivability,
consistency or a relation model.

Observation images can merge carrier aliases; no unproved quotient argument
is used. raw_source_model proves an independent invariant, and
raw_derivation_reflects reconstructs an actual literal source derivation
with exactly Some-quoted output. raw_derivation_no_overflow follows.
semantic_proof_observed and semantic_proofs_observed are executable mutually
recursive proof translations. guarded_source_raw and raw_source_union_exact
prove reverse coverage and exact source-derivability union coverage.
This remains external raw syntax and externally fixed budgets; no internal
raw-Expr eliminator or uniform budget representation is asserted.

## Commands and results

CHECK.sh records each exact command, input snapshot/hash, start/end UTC,
raw output and exit. It compiles a copied source under the pinned environment,
reusing /tmp/pts-rk-internal-horn.6x5cr6/default/theories dependency objects.
It is not a fresh integrated audit.

```sh
bash docs/direct-r-handoff/verification/combinatory-guard-provenance-2026-10-23/provenance/CHECK.sh attempt-17
bash docs/direct-r-handoff/verification/combinatory-guard-provenance-2026-10-23/provenance/KERNEL.sh kernel-03
```

Attempts 01–09 fail on elaboration/library/tactical details: missing operation
argument types; ambiguous None rewrite; explicit Vector.caseS reduction;
vector-map list unfolding; absent Stdlib forallb map/extensionality helpers;
and a list induction applied to an expression occurring only on one side.
Attempt10 passes the initial eight public endpoints at 20:36:47–48 UTC.
Attempts11/12 fail on map-composition normalization in exact argument decoding;
attempt13 passes 23 endpoints at 20:38:29–31. Its recursive kernel check01
passes 20:39:23–44 with inherited functional_extensionality_dep only and no
unsafe entries. Attempts14/15 fail at an explicit axiom-name application and
unfinished head-membership subgoal. Attempt16 passes all 33 endpoints at
20:41:11–14. A comment-only edit replaces a word colliding with the conservative
lexical safety scanner; no theorem or proof changed. Attempt17 passes all 33
closed reports, exit0, 20:41:40–44. Kernel02 passes at 20:41:33–54 but overlaps
that comment-only rebuild; kernel03 is the final frozen-source recheck.

Final proof source SHA-256:
5a03251d2e1a488cdd5151867fc3204f6e956e1739d85a878a562eff036fe257.
Final recursive kernel03 PASSES, exit0, 20:42:33–20:42:55 UTC. Complete
inventory contains only inherited functional_extensionality_dep, with no
type-in-type, unsafe fixpoints or assumed positivity. Final source hash is
unchanged. Exact log/timestamps/exit are retained; integrated fresh audit
remains the parent's task.
