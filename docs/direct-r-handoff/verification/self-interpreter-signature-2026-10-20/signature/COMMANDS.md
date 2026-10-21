# Finite Tarski signature — 20 October 2026

Base commit: `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`.
This task added only `theories/self_interpreter/TarskiSignature.v` and its
evidence. Parent owns Dune/Audit integration. No Git/index mutation was made.

## Checked contract

The actual original context contains the four base blocks (carriers, decoders,
universe codes and universe-law witnesses), followed by one product constructor
and one polymorphic product-law family for every pair `a,b <= k`. The field
count is exactly `4*(k+2) + 2*(k+1)*(k+1)`. Carriers through `k+1` cover
`max(a+1,b)` for these pairs; closure under all pairs of all available carrier
ranks is neither required nor claimed. Out-of-range selectors have no public
typing contract.

- `context_wf`, `context_normal`: original well-formed context with normal
  annotated declarations.
- `carrier_typed`, `decoder_typed`, `universe_typed`, `universe_law_typed`,
  `product_typed`, `law_typed`: all six actual variable-field interfaces.
- `fill_typed`: an independently constructed original `TypedSub` into any
  target context, with no hypothesis supplying the desired substitution.
- `fill_carrier`, `fill_decoder`, `fill_universe`, `fill_universe_law`,
  `fill_product`, `fill_law`: exact replacement by the actual identity
  carriers, decoders, universe witnesses, product constructors and law families.
- `fill_replace`: these closed concrete fields are stable under substitution.
- `close_typed`, `closed_type_sort`, `close_normal`, `close_injective`: literal
  closed telescope terms preserve original typing, normality and syntax.
- `identity_run_typed`, `identity_run_closed`: direct original application
  typing and administrative beta recovery of the substituted body.

These are finite interface/closure results, not a quotation of all dependent
source derivations. Closing an independently typed body does not construct
such a body, and administrative beta recovery is not global conversion
coherence or neutral-cast cancellation. All 22 own assumption reports are
closed. No PTS rules, annotated syntax, or original source domain changed.

## Exact build and versions

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-self-tarski-signature.MV1HYT \
  --display=short --no-buffer -j 2 theories/self_interpreter/TarskiSignature.vo
```

Raw local-only ignored artifacts are retained in
`_build/self-interpreter-tarski-signature.LeUxzZ/`: `RUN.sh`, `VERSIONS.sh`,
`versions.log`, `status.tsv`, and every attempt log. Versions: Rocq 9.2.0,
Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2, Dune 3.23.1, opam 2.6.1;
the full installed-package list is retained.

| Attempt | Exit | First actual result |
| --- | --- | --- |
| 01 | 0 | Initial pair arithmetic, context definitions and syntax naturality. |
| 02 | 1 | Concurrent dependency `TarskiLawFamily.v` line 131 focus error; new signature proofs not reached. |
| 03–06 | 1 | Selector-index rewriting required exposing the implicit `Fin` scope; diagnostic type printing retained in attempts 04 and 06. |
| 07 | 1 | All context/field proofs passed; polymorphic value family needed explicit scope instantiation. |
| 08 | 1 | Substitution rewriting required unfolding the implicit product-context width. |
| 09 | 0 | Complete six-field context and actual identity substitution; 15 closed reports. |
| 10 | 0 | Final closure/application and naturality results; 22 closed reports. |

No axiom, admitted proof, disabled safety check, theorem weakening or timeout
was used. The known logical-loadpath remapping warnings and a deprecated
`Nat.div_lt_upper_bound` notation warning remain in the logs. Scoped whitespace
check exits 0. The fresh aggregate recursive kernel/pristine/full-CI verification
is recorded separately in `../final-review/COMMANDS.md`; standalone module
compilation is not presented as that final audit.

Frozen source SHA-256:

```text
034281219e3e1011f7c690cbfc9184990d6b4f4c1d53a3e76ce7c5f176d92acc  theories/self_interpreter/TarskiSignature.v
```
