# Finite uniform one-binder contextual beta signature — 21 October 2026

Base commit `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`.
Own source: `theories/self_interpreter/ContextualBetaSignature.v`.
Parent owns Dune/Audit/shared prose. No Git/index mutation or edit to frozen
dependencies. This concrete layer is distinct from arbitrary-length schemes.

## Contract

The actual context appends exactly `(k+1)^4` declarations to the EXISTING
TarskiBetaSignature context. The only external field indices are bounded
s,a,b,d. Each field quantifies over the actual binder type X and dependent
families/terms A,B,f,u, rather than enumerating concrete syntax instances.
Original well-formedness, normal declarations, bounded lookup typing and
an actual inherited TarskiContext.environment are proved. Existing local
beta fields retain their typings and literal identity-fill equations.

Each declaration has its own exact proved formation rank; bounded indices
give the arithmetic upper bound k+3. No cumulativity rule or claim of a
sufficient full-source literal budget is inferred from that inequality.
Actual normal closed ContextualBetaFamily.identity_family terms construct
the identity TypedSub; no new field-existence premise is assumed.

Five actual applications have direct original typing from independent input
typings and are normal when all five supplied arguments are normal. Actual
identity replacement reduces the witness to literal reflexivity at the
dependent carrier and lambda term, retaining binder annotations.
The filled application has direct original typing via the actual TypedSub,
not subject expansion. Fixed-index syntax injectivity recovers ALL five
inputs; normal-input beta conversion also implies their literal equality.
This is local input fidelity, not a full-source quotation injectivity theorem.

One binder is not arbitrary telescope length. No function extensionality,
eta, neutral-cast cancellation or full source-conversion theorem is claimed.

## Exact compilation

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-contextual-beta-signature.TOn0rm \
  --display=short --no-buffer -j 2 theories/self_interpreter/ContextualBetaSignature.vo
```

Ignored local-only raw evidence: `_build/contextual-beta-signature.iPncm5/`
with RUN.sh, VERSIONS.sh, versions.log, status.tsv and every attempt log.
Versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1, opam 2.6.1; full installed package inventory retained.

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 0 | Quartic enumeration and bounded descriptor laws; 2 closed reports. |
| 02 | 0 | Complete concrete signature against the frozen family API; 25 own closed reports. |
| 03 | 0 | Added direct filled-application typing; all 26 own reports closed. |

The full signature draft waited for the independently compiled family API;
there were no failed Rocq attempts in this module, and no timeout, theorem
weakening, axiom, admit, unchecked cast or disabled check. An unexecuted shell
runner line typo was corrected before the first run. Known logical-loadpath
and arithmetic-notation deprecation warnings remain in raw logs.
Recursive aggregate/kernel/pristine and full local CI evidence is separate,
not inferred from this module compilation.

Independent read-only review of this exact frozen source passed: genuine
quartic rank-only descriptors, five bound object arguments, independently
typed normal identity values, exact bounded lookup/fill, literal recovery
and correctly guarded local conversion injectivity. The direct filled
typing wrapper uses original typing_replace, not subject expansion.

Frozen source SHA-256:

```text
733d2d0ed64e38084d0422ea17cf644c28543eb8547ebd43e3655f83735790ec  theories/self_interpreter/ContextualBetaSignature.v
```
