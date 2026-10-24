# Literal quantified MM0 search and projection model — 2026-10-23

New sources owned by this subtask:

- `theories/CombinatoryLogic-rk/MM0FiniteSearch.v`
- `theories/CombinatoryLogic-rk/MM0ProjectionModel.v`

No existing proof, registration, documentation, index or commit was changed
by this subtask. Parent handles integration and fresh audit. The accompanying
`source.sha256` records all four owned source files, including the preceding
generic enumeration helpers.

## Exact compiler invocation

Working directory `/Users/akuklev/air/pts-rk`. Replace MODULE by
MM0FiniteSearch or MM0ProjectionModel and LOG by the corresponding attempt
log below:

```sh
env PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH" \
  OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
  opam exec -- timeout 180 rocq compile -time \
  -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-algebra-search.LjN7h7 PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-operation-algebras.0JQW1q PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-internal.6wfWep PTSrk.Combinatory \
  -Q /tmp/pts-rk-native-model-boundary.iBL2hu PTSrk.Combinatory \
  -Q /tmp/pts-rk-mm0-finite-search.iwaQRP PTSrk.Combinatory \
  -o /tmp/pts-rk-mm0-finite-search.iwaQRP/MODULE.vo \
  theories/CombinatoryLogic-rk/MODULE.v \
  > /tmp/pts-rk-mm0-finite-search.iwaQRP/LOG 2>&1
```

Search attempt 01 omitted `timeout 180` and `-time`; search attempt 07
omitted `-time`. The other commands have exactly the wrapper above. Final
compile stages import the frozen signature09 and rebuilt axioms04 objects.

| Search log | Exit | Result |
| --- | --- | --- |
| attempt-01.log | 143 | Deliberately stopped after approximately one minute to diagnose expensive higher-order `apply` inference. |
| attempt-02.log | 1 | Axioms object used an older signature object; colleague rebuilt it against frozen signature09. |
| attempt-03.log | 143 | Timed diagnosis identifies checker extensionality's implicit-argument `apply`; stopped and replaced with explicit theorem application. |
| attempt-04.log | 1 | Missing natural exponent notation import. |
| attempt-05.log | 1 | No declared natural ring structure from the initial narrow arithmetic imports. |
| attempt-06.log | 1 | `list_sum` remained folded, preventing arithmetic normalization. |
| attempt-07.log | 1 | Diagnostic goal output confirms the folded sum; then explicitly unfolded it. |
| attempt-08.log | 0 | Six closed reports for generic literal search integration. |
| attempt-09.log | 143 | Full singleton candidate check computed successfully; direct normalization of dependent-key exhaustive search was deliberately stopped. |
| attempt-10.log | 0 | Nine closed reports. Singleton exhaustive-search rejection proved via the exact search theorem and generic subsingleton impossibility. |

| Projection log | Exit | Result |
| --- | --- | --- |
| projection-01.log | 143 | Deliberately stopped costly kernel conversion of a filtered-list property inside the specialized full-fragment model proof. |
| projection-02.log | 143 | Isolated that property; its generic filter proof still caused costly conversion, then replaced it by a direct checked finite-list proof. |
| projection-03.log | 0 | Nine closed reports, including the actual all-valuation model and enabled application. |
| projection-04.log | 0 | Eleven closed reports; explicit countermodels to the two omitted axioms added, and rebuilt against final search10. |

All compilations emit the upstream Vector.t advisory. It is not suppressed.
The final search and projection checks take approximately one second each.
No timed-out or cancelled attempt is a successful check. No claimed general
efficiency bound depends on direct execution of exhaustive constructor search.

## Recursive kernel check

```sh
env PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH" \
  OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
  opam exec -- timeout 180 rocq check -silent -o \
  -Q /tmp/pts-rk-consistent-horn.2l5WGN/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-algebra-search.LjN7h7 PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-operation-algebras.0JQW1q PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-internal.6wfWep PTSrk.Combinatory \
  -Q /tmp/pts-rk-native-model-boundary.iBL2hu PTSrk.Combinatory \
  -Q /tmp/pts-rk-mm0-finite-search.iwaQRP PTSrk.Combinatory \
  PTSrk.Combinatory.MM0FiniteSearch PTSrk.Combinatory.MM0ProjectionModel \
  > /tmp/pts-rk-mm0-finite-search.iwaQRP/kernel.log 2>&1
```

Recursive check exits 0. Complete context inventory has no axioms,
type-in-type, unsafe (co)fixpoints, or assumed positivity. This isolated
closure check is additional evidence; parent handles the full fresh
registered-library build and pristine inventory comparison.

## Mathematical scope

Search interprets every selected literal universal MM0 axiom at EVERY semantic
valuation. All nine constructors are total on the SAME finite carrier per
sort. NAT, TM and TEL are separate copies of an equally sized domain; this
does not cover unequal cardinalities without another interface. Constructor
interpretations are exhaustively enumerated, predicate interpretations solved
by complete finite Horn saturation. No accepted candidate is an input.

There are `2+3n+3n^2+n^3` operation-call keys over an n-element enumeration,
and `n^(2+3n+3n^2+n^3)` enumerated total tables. Exact success iff model
existence and failure iff nonexistence concern THIS fixed carrier, not all
finite sizes. An actual full55 one-element candidate rejection is computed.
The general subsingleton theorem proves that h_universe plus Void denial
already excludes a singleton term domain.

The explicit projection construction uses any two distinct values u/v and
the total operations z=nil=u, s=id, u(_)=u, v(_)=v, app=first projection,
pi/lam=second projection, cons=third projection. Numeric/stel/prefix relations
are true; lift/sub/red compare their source and result; h(t,A) means A=u;
form and ax are false. Every one of the 53 retained universal axioms is
proved under arbitrary valuations. Typing is inhabited, and application
has an explicitly enabled instance; Void denotes v and is empty.

The two omitted rules are EXACTLY sveq and f0, and the module proves that
this algebra violates both. In particular f0's omission disables catalogue
realization. The construction is a sound model of these selected subtheories,
NOT a full original-PTS model or a witness of finite satisfiability of all
55 axioms. The Bool specialization gives an actual two-element model and
proves search success for every subset of the retained named rules; the
large exhaustive search is not executed to obtain that existence proof.
