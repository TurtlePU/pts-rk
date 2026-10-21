# Originally typed Tarski product-code constructor

Source: theories/self_interpreter/TarskiProducts.v.
SHA-256: 27e6de3d9f10b7d07c9c68c3acf89fb6f40e632e423103351adc72a7fe1bd75f.
Working directory: /Users/akuklev/air/pts-rk.
Fresh build directory: /tmp/pts-rk-tarski-products.sY54J1.
Raw local evidence: _build/tarski-products.Wlfd3X.

## Commands and all attempts

Each attempt used `bash _build/tarski-products.Wlfd3X/RUN.sh NN`.
The retained runner sets PATH, OPAMROOT and OPAMSWITCH, redirects complete
stdout/stderr to attempt-NN.log, and immediately records the numeric exit
status in attempt-NN.exit. Its exact build command is:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-tarski-products.sY54J1 --display=short --no-buffer theories/self_interpreter/TarskiProducts.vo
```

| Attempt | Exit | First result/error |
| --- | --- | --- |
| 01 | 1 | Line 55: weakening required explicitly exposing the shifted universe before arr_shift rewriting. |
| 02 | 1 | Line 72: first application substitution equation retained a replacement/renaming goal. |
| 03 | 1 | Unfolding shift alone did not discharge the same substitution equation. |
| 04 | 1 | Diagnostic Show exposed the remaining replacements by successor variables. |
| 05 | 1 | After fixing replacement by successor, line 165 contained an unnecessary replacement rewrite in beta specialization. |
| 06 | 0 | All nine public assumption reports closed. |

All failures are preserved. No timeout occurred, no assumption was added,
and no theorem statement was weakened. Diagnostic Show was removed.

Recursive kernel command (kernel.log/kernel.exit), exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-tarski-products.sY54J1/default/theories PTSrk -Q /tmp/pts-rk-tarski-products.sY54J1/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-tarski-products.sY54J1/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.TarskiProducts
```

The recursive loaded-context inventory contains only existing upstream
functional_extensionality_dep; no type-in-type, unsafe fixpoints or assumed
positivity. All nine new public theorem reports are closed.

Installed versions were recorded with the following command, exit 0
(versions.log/versions.exit):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Actual versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1. Source hashing used
`shasum -a 256 theories/self_interpreter/TarskiProducts.v`.
Scoped git diff --check exits 0; safety scan for admissions, axioms and
disabled checks has no matches (rg exit 1). Independent read-only contract
review passes. Aggregate audit, pristine comparison and full CI are separate
parent-run checks, not inferred from this targeted build.

## Exact scope

For explicit original objects Ca,Cb,Cc:U0 and Ea:Ca->Ua,
`product_type_sort` derives the sort U_(a+2) of the actual polymorphic
constructor interface Pi A:Ca.(Ea A->Cb)->Cc. Its sort does not depend on
the external result rank: the code carriers all have sort zero.
`product_specialize` proves original typing of the two actual applications.

Given additionally Eb:Cb->Ub and B:Ea A->Cb, `decoded_product_sort`
derives Pi x:Ea A.Eb(B x):U_max(a+1,b). B is genuinely dependent; no
constant-family restriction or erased lambda annotation is used.

`identity_product a b` is the actual closed, fully normal original term
lambda A:Ua.lambda B:A->Ub.Pi x:A.B x. Its original typing is constructed
directly, followed only by checked conversion to the identity-decoder
interface. `identity_product_specializes` gives the two administrative beta
steps to the literal dependent product. `identity_decoded_product_agrees`
uses the common reduct Pi x:A.B x to prove the identity decoding equation;
it is not an assumed abstract algebra law, and it uses no eta conversion.

This module constructs local code/decoding operations, not a recursive
dependent quotation or a source-family translation. The carriers, decoders
and constructor are explicit parameters in the generic theorems, and the
actual identity instance is separately proved. No internal normalizer,
global conversion coherence, finite closed PHOAS package, or full dependent
self-interpreter follows from these local theorems alone.
