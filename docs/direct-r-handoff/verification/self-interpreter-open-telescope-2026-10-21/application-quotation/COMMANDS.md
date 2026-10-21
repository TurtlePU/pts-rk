# Actual state-threaded application quotation

Date: 2026-10-21. Frozen source theories/self_interpreter/ApplicationQuotation.v,
226 lines, SHA-256 d42b1562702d3452f173a16a3ca0503b26869ec28c18c38bd50ad902d3b501b1.
No Git/index mutation; coordinator owns common Dune/Audit/handoff.

`application_result st f u A B jf ju` consumes two independently constructed
judgments in the SAME concrete state, at the literal original source types
Pi A B and A. It returns an actual state-threaded result at app f u and
literal subst B u. No extra budget, source typing, internal equality or
output-inhabitation premise is assumed. First an actual checked contextual
equality layer aligns the argument with the retained domain code. Then a
second actual layer aligns the function with the reconstructed product code.
The retained dependent children are transported across both state extensions.
Original typing of the final operation, full normality, neutral argument,
structural codomain view substitution and literal recovery are obtained from
those inputs. `exactly_two_layers` proves the flattened local plan contains
exactly two numeric requests; it is not a source-recursion cost bound.

Both the source-recursion owner and the alignment owner independently
reviewed this exact frozen source and passed the contract/integrity review.

Raw logs: _build/application-quotation.0OqUkB, RUN.sh/CHECK.sh. This new module
uses the existing absolute /tmp/pts-rk-local-quotation-spine.nr1PlD dependency
cache to avoid redundant disk use. Own new assumption output was actually
printed, not inferred from a cached success.

```sh
cd /Users/akuklev/air/pts-rk
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-local-quotation-spine.nr1PlD \
  --display=short --no-buffer -j 2 theories/self_interpreter/ApplicationQuotation.vo
```

Attempt01 exit1: unfold advance-state projections before the inherited-map
rewrite. Attempt02 exit1: specify both renamings in an exact typing change.
Attempt03 exit1: specify the target context in that same change. Attempt04
exit0: four helper reports closed. After the shared LocalCodeAlignment API
froze, attempt05 exit0 checked the full application and exact two-layer
endpoint on their first build, with all NINE own reports CLOSED. No theorem
weakening, timeout, disk failure or interrupted compilation occurred.

```sh
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-local-quotation-spine.nr1PlD/default/theories PTSrk \
  -Q /tmp/pts-rk-local-quotation-spine.nr1PlD/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-local-quotation-spine.nr1PlD/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.ApplicationQuotation
```

Recursive kernel exit0, only unchanged upstream dependent functional
extensionality in the loaded inventory; no unsafe fixpoints, assumed
positivity or type-in-type. Own reports separately closed. Forbidden
declaration scan exit1 (no matches). The subsequent coordinated
LayerCodeAlignment alias-only cleanup is outside this scoped dependency
snapshot; the fresh final aggregate verifies the final combined snapshot.

CHECK.sh records HEAD and exact tool/package versions: Rocq9.2.0,
Stdlib9.1.0, Equations1.3.2+9.2, OCaml4.14.2, Dune3.23.1, opam2.6.1;
HEAD e822cd62df393faf4d5e4ed0c4c8fed173ccba6f. Fresh combined
aggregate/pristine/full CI are recorded separately at the final-review gate.
