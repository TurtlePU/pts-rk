# Dependent normal algebra regression tests — 24 October 2026

Each invocation is `bash /tmp/pts-rk-normal-examples.LRVW14/check.sh checkNN`.
The retained driver copies all current sources, isolates configuration/data,
records SHA256, expanded command, UTC times and numeric status, and checks
NormalizedExamples.agda and its closure freshly with --safe --ignore-interfaces
and +RTS -M2G. Agda 2.8.0-3d04bac, pinned sibling Cubical v0.9.

check01 was stopped using `kill -TERM 92785` after 2m52s, RSS 2243776 KiB,
exit143. Its last reported import was NormalizedProducts. Parent independently
reproduced excessive resource use checking Products alone; therefore this run
does NOT establish that an Examples computation assertion is expensive.

check02 used the updated Products with opaque naturality proofs, but still
stopped at that import. `kill -TERM 93260` after 2m41s, RSS2227424KiB, exit143.
Parent's simultaneous Products-only process also exceeded 2m47s and2GiB.
No regression assertion was removed or weakened in either run.

All interrupted source snapshots, exact commands/times/statuses/logs remain
in the named run directories. Final check05 uses the repaired Products dependency.

check03 used the additional module argument NeutralProbe:
`bash /tmp/pts-rk-normal-examples.LRVW14/check.sh check03 NeutralProbe`.
This scratch probe imports Families/Comprehension but not Products, constructs
the same genuine neutral type f U₀, substitutes f with λ(U₀).U₀, and proves
the resulting public pullTy computation by refl. PASS0, 02:22:03–02:22:51UTC,
zero warnings. New Families castNF/agrees were included. Observed transient
RSS1890512KiB at43s was not a failure; the run completed normally.

check04 imported a Products snapshot for which the parent's independent
check11 reported unresolved context metavariables at ElNF/ElNF-natural.
Stopped redundant process96376 with `kill -TERM 96376` at1m24s,
RSS1845424KiB, exit143, to retry the corrected dependency. The Examples
assertions remained unchanged, with added IR-context tests.

check05 PASSED exit0, zero warnings, 02:35:29–02:38:40UTC, fresh complete
import closure under the 2GiB heap cap. All computational assertions remain
literal refl: neutral dependent type substitution, polymorphic identity
specialized to U₀ and then applied to U₇, both dependent result types,
lifted substitution images, IR context decoding, WF-free computed type and
WF-free dependent type action. Pairing/eta/projection-lift specializations
also pass, as does the independent computed-type fibre embedding theorem.
There was no failed or removed computation assertion: earlier interruptions
occurred in dependency proof checking, independently diagnosed by the parent.

Final NormalizedExamples.agda is 134 lines, SHA256
`57959f97ef8753e340f548df107794ffc83a8798075092c491e9944966e52859`.
Live and check05 copied source hashes agree. The complete project source
manifest is retained; the archive preserves only relevant source snapshots,
not interfaces, generated caches or complete copied dependency trees.
Command files have trailing blanks stripped in readable copies; byte-exact
originals are retained as command.raw.txt.gz.
