# Actual closed PHOAS decoder for independent ChurchSTLC

Source: theories/self_interpreter/PHOASDecoder.v.
SHA-256: f52518d4b040126a1c02c998404727be789fd350cfe02bf6bc11b6f3580e1576.
Working directory: /Users/akuklev/air/pts-rk.
Fresh build: /tmp/pts-rk-phoas-decoder.ljICyj.
Raw local evidence: _build/phoas-decoder.awMgXP.

## Commands and attempts

Each attempt used `bash _build/phoas-decoder.awMgXP/RUN.sh NN`.
The retained runner exports the pinned PATH, OPAMROOT and OPAMSWITCH,
runs the following exact command, redirects complete stdout/stderr to
attempt-NN.log, and immediately records the numeric exit in attempt-NN.exit:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-phoas-decoder.ljICyj --display=short --no-buffer theories/self_interpreter/PHOASDecoder.vo
```

| Attempt | Exit | First result/error |
| --- | --- | --- |
| 01 | 1 | Concurrent PHOASPackage.v line313 needed explicit k in its fidelity proof; decoder not reached. |
| 02 | 1 | Same dependency checkpoint, decoder not reached. |
| 03 | 1 | Same dependency checkpoint, decoder not reached. |
| 04 | 1 | Decoder beta substitution needed reduction of an eq_rect reflexive cast. |
| 05 | 1 | Ordinary destruct could not eliminate dependent Fin1 in the source-renaming proof. |
| 06 | 1 | Dependent elimination renamed the impossible Fin0 branch variable. |
| 07 | 0 | Actual closed decoder, direct typing and strong recovery; eight closed reports. |
| 08 | 0 | Concrete executable beta-source regression added; nine closed reports. |

All failures are preserved. No timeout occurred. Dependency owners edited
only their assigned modules; the decoder agent did not modify their proofs.

Recursive kernel command (kernel.log/kernel.exit), exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-phoas-decoder.ljICyj/default/theories PTSrk -Q /tmp/pts-rk-phoas-decoder.ljICyj/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-phoas-decoder.ljICyj/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.PHOASDecoder
```

The recursive loaded-context inventory contains only existing upstream
functional_extensionality_dep, with no unsafe fixpoints, assumed positivity,
type-in-type or additional axioms. All nine new public reports are closed.

Actual installed versions were recorded by the following command
(versions.log/versions.exit, exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1. Source SHA is also retained in source.sha256.
Safety scan has no admissions, axioms or disabled checks (rg exit 1);
scoped git diff --check exits 0. Independent final source/contract review
passes at the recorded source hash. Aggregate audit/full CI belong to the
parent checkpoint and are not inferred from this targeted build.

## Exact positive endpoint and index boundary

The source evidence is the independently defined computational
ExecutableQuotation.derivation, not an original target typing proof or an
assumption of quotation existence. For d over the one ground-type variable
and empty source term environment, and rank_budget(d)<=k,
closed_phoas_interpretation proves ALL of the following for actual computed
PHOASPackage.quote k d and the actual original closed decoder:

- The package is fully beta-normal, including all annotations.
- The package, the closed decoder and their actual application have the
  stated ORIGINAL PTS typing judgments.
- Decoding strongly reduces to lambda o:U_0.t, retaining the original
  unreduced annotated source body t.

The ground-type lambda is INSIDE decoder k A; no external lambda is appended
to its application. run_at_typed uses the actual finite typed substitution
and original application rules, then original type conversion; it does not
infer application typing backwards from the reduct. quote_type_has_sort
obtains the decoder-domain universe from independently proved type formation,
not from a source inhabitant or from an already typed quotation.

quote_strong_recovery specializes the real finite family/handler telescope
to the original identity families and original Abs/App inhabitants.
The quoter does not normalize the source, and there is NO supplied semantic
value payload. Exact fixed-budget syntax fidelity remains separately proved
in PHOASPackage.quote_conversion_injective. The public theorem retains the
independent-source and supplied-finite-budget boundary; choosing the computed
rank_budget supplies such a budget for every computational source derivation.

decoder k A is externally indexed by BOTH the budget k and the FULL simple
type A. This does NOT yet construct one rank-only raw decoder accepting all
type shapes via an internal type-representation argument. Nor does the STLC
endpoint establish full dependent PTS quotation or conversion coherence.
The general full-dependent development remains separate.

The concrete regression uses the existing reducible beta_source:
vm_compute establishes rank budget 1, nonnormal closed source, and normality
of the actual PHOAS quote. beta_interpretation_recovers_source applies the
general strong-recovery theorem to the actual decoder/quote, recovering the
unreduced beta redex. No core rule was changed; no commit or push performed.
