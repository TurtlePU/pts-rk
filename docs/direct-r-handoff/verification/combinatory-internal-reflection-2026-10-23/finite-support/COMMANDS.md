# Finite guarded atom support — 2026-10-23

GuardedFiniteSupport.v adds explicit finite indexing for a fixed Horn fragment,
all denial premises and a distinguished query. The support has exactly
`1 + sum (1 + premise count) + sum (denial premise count)` positions.
It is finite independently of proof-tree depth. Duplicated atoms may occupy
several positions; the executable index/reify roundtrip is exact on the
support, so encoding is injective there. Arbitrary indices can be aliases.
Unsupported atoms use the distinguished query as a total fallback; every
clause, denial and chosen query is proved supported, so fallback does not
identify distinct atoms used by the fragment.

Mutual executable proof translations preserve arbitrary finite derivation
trees. Indexed and original derivability coincide on supported atoms; models,
denials, satisfiability, the finite Boolean query and denial checker are
preserved exactly. The MM0 specialization includes every semantic valuation
of every selected guarded axiom, including inactive tautologies, and every
subject instance of the unguarded universal Void denial. No native typing,
consistency or semantic correctness predicate is an admission condition.
These are finite-support and external translation results, not themselves
an internal reflection theorem or a bound on the number of proof trees.

The only proof source added by this worker is GuardedFiniteSupport.v.
No existing source, Dune registration, shared handoff or original kernel was
changed. The copied build source is byte-identical to the repository source.

## Commands and actual results

Pinned environment: OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam,
OPAMSWITCH=pts-rk-ci. The opam executable is
/Users/akuklev/.local/share/pts-rk-ci/bin/opam.
Toolchain versions are those of the preceding fresh bridge audit:
Rocq 9.2.0, OCaml 4.14.2, Dune 3.23.1, Stdlib 9.1.0,
Equations 1.3.2+9.2. This isolated worker compile reuses its dependency
objects from /tmp/pts-rk-mm0-bridge.IH9mrh/default/theories.
The new compiled object is in /tmp/pts-rk-finite-support.Q1zQ9S.

```sh
bash docs/direct-r-handoff/verification/combinatory-internal-reflection-2026-10-23/finite-support/CHECK.sh attempt-04
bash docs/direct-r-handoff/verification/combinatory-internal-reflection-2026-10-23/finite-support/KERNEL.sh
```

Exact commands, UTC start/end, source hash, raw output and exit code are kept
per attempt. Attempt01 exits1 at the local decode/option-map simplification;
attempt02 exits1 because broad simplification unfolds the recursive index
before list rewriting. Both are proof-engineering failures, not incomplete
library declarations. Attempt03 passes the initial27 endpoints. Attempt04
passes the final36 endpoints, all closed,19:45:33–19:45:34UTC,exit0.
Full recursive kernel verification passes19:45:55–19:46:17UTC,exit0,
without dependency admission or skipping. Its complete CONTEXT SUMMARY
is byte-identical to the preceding fresh pristine upstream inventory:
inherited functional_extensionality_dep only, no unsafe declarations.
This is not a new fresh-dependency or full-repository CI run.

Final SHA-256:
e05014da233ae6b1999a33b97a6fd15e8bca15026b2d3a2a169a402644571632.

No commits, staging, pushes, cleanup or unrelated process changes.
