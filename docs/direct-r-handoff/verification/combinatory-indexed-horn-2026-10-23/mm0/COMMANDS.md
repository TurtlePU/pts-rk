# MM0 internally indexed fixed-fragment reflection — 2026-10-23

This worker adds only MM0IndexedReflection.v and this evidence directory.
The final source is frozen at SHA256
`ba0ee54842916489af3b0b2dc43f669ae9eeade838006a27d1c3ef017e9d5bc9`.
All 23 public assumption reports are closed.

## Checked result and boundary

One original-PTS term per fixed finite guarded fragment and support has
type `Pi q : Code. Proof(q) -> Truth(q)`, at rank4. Its two arguments are
internal, arbitrary original-PTS terms with the displayed types. The finite
support includes all clause atoms and every semantic Void denial, with an
external seed fixing the support once. The established least model supplies
all clause handlers without an additional model premise. Arbitrary query
soundness returns the indexed type `Truth(q)`; no theorem here identifies
every arbitrary query with a selector or normalized Boolean.

For supported semantic atoms, canonical query codes give exact inhabitation
iff finite derivability, original source reflection, executable proof
realization and all-subject Void refuters at bounds N>=5,d>=3. A computed
two-position example records why reifying an arbitrary duplicate position
does not imply its indexed derivability: both positions decode to the same
true semantic atom, but only its canonical index is derivable.

The raw-source presentation separately uses the independently generated
raw clause list with explicit optional-expression observations and guards.
Its arbitrary closed indexed inhabitants reflect to actual literal MM0
source deductions; no overflow or Void proof is possible. All literal source
proofs are covered by the union over numerical bounds. The raw proof type's
finite support is externally seeded afresh by that raw query. This is an
external theorem about arbitrary closed inhabitants, not one internal raw
decoder/guard consumer or an internally budget-polymorphic theorem. No
fixed-budget raw/semantic derivability equivalence is asserted.

The generic indexed consumer's typing uses no canonicity. Exact closed
inhabitation converses and the Void specialization retain the existing
external native canonicity dependency. No new axiom, unsafe operation,
cumulativity or native typing rule is introduced. Rank4 bounds the generated
consumer TYPE, not runtime allocation or global redex rank.

## Commands and actual outcomes

Pinned environment: OPAMROOT
`/Users/akuklev/.local/share/pts-rk-ci/opam`, OPAMSWITCH `pts-rk-ci`.
The exact paths and invocation are in CHECK.sh and each attempt's command
file. These isolated checks reuse the preceding fresh 63-module build plus
the five separately compiled new dependencies; they are not the root's
fresh integrated verification. Worker objects are in
`/tmp/pts-rk-mm0-indexed.Eivfwl`.

```sh
bash docs/direct-r-handoff/verification/combinatory-indexed-horn-2026-10-23/mm0/CHECK.sh attempt-05
```

Each attempt retains its source hash, command, start/end UTC, output and
exit code. Attempts01--02 fail on an omitted explicit congruence instance;
02 prints the actual goal for diagnosis. The diagnostic is removed before
03, whose remaining failure is an uninferred raw-reflection budget parameter.
04 fixes that and reaches the regression example, then fails because its
finite-equality helper needs an explicit import. Attempt05 fixes that import
and passes all 23 endpoints, exit0, 20:48:21--20:48:26 UTC (4.7 seconds).
The final frozen hash equals that successful attempt's hash. Independent
read-only review finds no mathematical or proof-integrity issue; its raw
query/support and alias boundaries are recorded above.
Exact raw whitespace-bearing command/diagnostic outputs are preserved in
adjacent .raw.gz files before whitespace formatting of the readable copies.
The replay wrapper now emits commands without terminal spaces; its actual
compiler arguments are unchanged.

No staging, commit, push, cleanup, unrelated process action, prior proof
module edit, native kernel edit, Agda edit or MM0 edit was performed. Dune,
the note and shared handoff updates are owned by the root agent.
