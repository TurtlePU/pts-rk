# FiniteUniversalHorn isolated proof development, 2026-10-23

Working directory: `/Users/akuklev/air/pts-rk`.
Only new project source `theories/CombinatoryLogic-rk/FiniteUniversalHorn.v`
was edited. No registration/docs changes, staging or commit.

All compiler attempts used:

```sh
env PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH" \
  OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
  opam exec -- rocq compile \
  -Q _build/default/theories/CombinatoryLogic-rk PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-horn.sct6i1 PTSrk.Combinatory \
  -Q /tmp/pts-rk-finite-universal-horn.V4OGh9 PTSrk.Combinatory \
  -o /tmp/pts-rk-finite-universal-horn.V4OGh9/FiniteUniversalHorn.vo \
  theories/CombinatoryLogic-rk/FiniteUniversalHorn.v
```

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | Importing Vector shadowed list `In`; changed to qualified `Require Vectors.Vector` without importing its names. |
| 02 | 1 | A dependent schema binder needed its explicit PositiveSchema/NegativeSchema type before applying its body. |
| 03 | 0 | Full semantic-grounding, decision and model interface; fourteen closed reports. |
| 04 | 0 | Added exact vector/clause enumeration counts and saturation bound; eighteen closed reports. |

All attempts emit ONE upstream Stdlib advisory: using Vector.t is known
to be technically difficult. It is not a guard, universe, positivity or
proof-obligation warning. The required representation is Vector.t; importing
VectorDef directly would emit the identical warning (same `Attributes warn`
declaration). No warning is suppressed. No other warnings occur in the final
attempt. Versions: pinned Rocq 9.2/OCaml 4.14.2 as in the earlier subtask.

The isolated compile imports the existing built GroundHorn and preceding
isolated FiniteHorn objects; it is not a fresh dependency-closure verification.
Root handles fresh integration after all parallel source changes.

Results:

- Complete enumeration of EVERY Vector.t D k semantic valuation over an
  explicitly enumerated finite domain, with exact list length |D|^k.
- Positive/negative dependent schemata are compiled to finite ground clauses;
  exact clause counts are sums of |D| raised to schema arities.
- Universal satisfaction under every semantic valuation iff satisfaction of
  the compiled clauses and denials. No functional extensionality is needed.
- Executable candidate check iff some predicate interpretation satisfies all
  schemata. The least interpretation is constructed by saturation and is
  sound, has exact ground-query derivability, and uses the same fixed domain.
- Nonempty domain witness and complete enumeration supply the fixed finite
  model theorem. No growing carrier is used.
- Boolean-domain examples: universal P(x)->P(x) permits denial of P(false),
  while universal P(x) rejects it; the failure arises at the second valuation.

Boundary: schema templates already interpret the chosen constructor algebra.
This is a complete check of EACH GIVEN finite candidate interpretation, not
an existence theorem for arbitrary PTS fragments, and not a syntactic compiler
for the full MM0 signature. Built-in equality needs its actual-domain diagram
if represented as a predicate. No target-model-validity premise is assumed.
