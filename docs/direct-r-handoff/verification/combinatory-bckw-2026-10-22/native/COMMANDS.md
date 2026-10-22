# Rank-typed BCKW arithmetic: direct compiler evidence

Source: `/Users/akuklev/air/pts-rk/theories/CombinatoryLogic-rk/BCKW.v`.
No other repository source was changed by this worker. The root agent owns
Dune registration, documentation and fresh joint/pristine audits.

Each direct compilation used the existing dependency build below and wrote
all generated files into this temporary directory (not the source tree):

```sh
env PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH" \
  OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
  opam exec -- rocq compile \
  -R /tmp/pts-rk-combinatory-bj-bounds.TgqGUp/default/theories PTSrk \
  -Q /tmp/pts-rk-bckw-native.0pOZbj PTSrk.Combinatory \
  -o /tmp/pts-rk-bckw-native.0pOZbj/BCKW.vo \
  theories/CombinatoryLogic-rk/BCKW.v
```

The shell redirected compiler output to each log, saved `$?` in `result`,
displayed the log and exited with that compiler result. Attempts 01--06
completed immediately; attempt 07's asynchronous completion code was not
separately polled, but its log contains all 13 then-current closed reports.
Attempts 08--12 and final were explicitly polled to their completion.

| Log | Exit | Result |
| --- | --- | --- |
| attempt-01.log | 1 | Existing dependency build lacks STLCEmbedding; removed unnecessary import and defined local simple type grammar. |
| attempt-02.log | 1 | Premature unfolding of type decoding in typing tactic. |
| attempt-03.log | 1 | Required rewrite absent in variable helper. |
| attempt-04.log | 1 | Variable lookup needed reduction of eq_rect. |
| attempt-05.log | 1 | Rejected incorrect successor formula C(B W)H; corrected to B W H. |
| attempt-06.log | 0 | First eight closed reports. |
| attempt-07.log | not retained | All 13 then-current closed reports, no error text. |
| attempt-08.log | 1 | Needed to fold reduces_to before binder congruence. |
| attempt-09.log | 1 | Normality proof needed explicit E unfolding. |
| attempt-10.log | 1 | Boolean simplification incomplete. |
| attempt-11.log | 1 | Last Boolean conjunction needed rewriting by induction hypothesis. |
| attempt-12.log | 0 | Eighteen closed reports, including arithmetic correctness and unapplied numeral normalization. |
| final.log | 0 | Twenty-three closed reports, with public ranks/counts/typing corollaries. |

Final code uses only original Term/Typing/beta reduction and a simply typed
combinator-code datatype with proved original-PTS elaboration. It contains
no axioms, admissions or disabled checks. This direct check is not a fresh
transitive-assumption comparison; the root agent runs that separately.

Final direct recursive kernel check, exit 0, log `kernel.log`:

```sh
env PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH" \
  OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci \
  opam exec -- rocq check -silent -o \
  -R /tmp/pts-rk-combinatory-bj-bounds.TgqGUp/default/theories PTSrk \
  -Q /tmp/pts-rk-bckw-native.0pOZbj PTSrk.Combinatory PTSrk.Combinatory.BCKW
```

Inventory reports only upstream dependent functional extensionality, no
unsafe fixpoints, type-in-type or assumed positivity. Dependencies are the
existing build, not a new pristine build. Rocq version is 9.2, OCaml 4.14.2.
Final source SHA256:
`69968bff1bae46c37e3d9cac51987ff6e8b2ae082e5c6b6dc4dd2f960297dbc9`.
