# Dependent normal product operations — root evidence

Final NormalizedProducts.agda: 255 lines, SHA256
`3efde5a0b43e88873415a2b9cb3afc3527a1d9e7b5afe4b7e6b25be65abf2a93`.
It matches attempt-12.agda byte-for-byte. Final fresh check12 passed with
exit 0 and zero warnings, 24 October 2026, 02:35:17–02:38:26 UTC, under a
2 GiB heap cap. No source statement or safety check was weakened.

The included root driver was invoked from `/Users/akuklev/air/pts-rk` as
`bash /tmp/pts-rk-normal-products.5ZaaRR/check.sh NN`, with `fresh` for 01/12
and diagnostic probe selection for 06/07. Exact expanded Agda invocations
are retained per run. `probe-core.agda` and `probe-type.agda` are the retained
probe files; the per-run attempt-NN.agda snapshots are authoritative for the
actual selected main source. Metadata includes numeric exit and UTC times.

| Run | UTC start–finish | Exit | Scope/outcome |
| --- | --- | --- | --- |
| 01 | 02:08:18–02:09:04 | 42 | Fresh closure; evolving Families dependency had unresolved motives. |
| 02 | 02:10:52–02:11:02 | 42 | Incremental check; three soundness lemmas needed explicit proof arguments. |
| 03 | 02:11:10–02:11:15 | 0 | Incremental core through lambda naturality passed. |
| 04 | 02:13:42–02:16:07 | 143 | Interrupted for elaboration/memory growth after adding application naturality. |
| 05 | 02:16:31–02:19:36 | 143 | Interrupted elaboration diagnostic with abstract coherence lemmas. |
| 06 | 02:19:36–02:19:42 | 0 | Incremental core probe including typed lambda naturality passed. |
| 07 | 02:20:30–02:22:15 | 143 | Application-type-naturality probe interrupted for elaboration growth. |
| 08 | 02:22:15–02:24:45 | 143 | Explicit endpoints/local types diagnostic interrupted. |
| 09 | 02:24:45–02:28:40 | 42 | Factored raw beta chain and smart casts; remaining ElNF context/rank inference metas. |
| 10 | 02:29:22–02:30:37 | 143 | Nonstable diagnostic: run11 copied the shared source directory before run10 was interrupted. |
| 11 | 02:30:00–02:32:24 | 42 | Only ElNF input-family inference metas remained; fixed by the literal NfAt Γ (U r) input. |
| 12 | 02:35:17–02:38:26 | 0 | Final complete source, fresh --ignore-interfaces closure; zero warnings. |

## Evidence limits

The root driver reuses ONE scratch source/config/data directory. Runs02–11
are incremental diagnostics, not fresh import-closure evidence. In particular,
run10's copied source tree was mutated while it was running by run11; its
snapshot records the initial requested source, not a guaranteed stable tree.
Neither run10 nor the overlapping failing run11 is used as positive evidence.
Only the final stable fresh run12 verifies the final complete source. Run01
was fresh but failed in a concurrently developed dependency. All failed and
interrupted attempts remain archived.

The final checker uses Agda 2.8.0-3d04bac and Cubical v0.9 revision
`b150186d2544e7efeddd31e5d14a8b9ecbb100f7`, with `--safe`, isolated scratch
configuration/data, no default libraries and `--ignore-interfaces`. The
collection-time toolchain observation is not another proof run.

The archive includes commands, complete logs, exits/times, original source
hash inventories, main-source snapshots, probes and the final driver. It
excludes source/config/data trees and all generated interfaces/caches.
Trailing-whitespace readable evidence is normalized only with exact original
bytes retained in `.raw.gz` companions. All Agda snapshots are byte-preserved.
COLLECT.sh reproduces the collection; archive.sha256 checks every retained file.

## Checked scope

Normal universes/decoding, dependent products, abstraction, normalized dependent
application and substitution retain original typing. Original beta, universe
and decoding naturality, product naturality, and typed abstraction/application
naturality are proved paths, not imposed quotient equations. Smart casts retain
the literal normal subject and agree with ordinary dependent transport.

The operations still use original annotated binders and the existing native
normalizer. Extended-context well-formedness witnesses in naturality statements
are explicit native premises, not desired equations or normalization assumptions.
This is not a literal interpretation/initiality proof of the independent QIIRT,
a directly binder-free dependent compiler or a simultaneous syntax/evaluator IIRT.
