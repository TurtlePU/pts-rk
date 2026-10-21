# Normal identity fillings for the concrete numeric family

Date: 2026-10-21. Frozen source: theories/self_interpreter/NormalEqualityFill.v,
71 lines, SHA-256 c701da6fb5e00df8420fe5bf659092f0a09a8542dc5f4ed96c1bc5b478d81562.
No Git/index mutation; coordinator owns common Dune/Audit/prose.

The original proof checkpoint below had 79 lines and SHA-256
efec74a0ff4eaa0b0c2b04ec099d0e75c5d7f02c91b15b37346e2858ead25c97.
Coordinator-authorized mechanical alias expansion subsequently removed
eight redundant exported aliases after checking no consumer used them.
No definition, theorem contract or proof logic changed. Exact old sources,
expansion script, consumer search and full diff are retained in
_build/local-alias-cleanup.yfL2pV; see the companion local-spine record for
the exact command. LocalInitialState attempt03 recompiled this module and
reprinted all six CLOSED reports. Repeated combined recursive kernel check
exited0 in _build/local-initial-state.mTFIrR/kernel.log. The object shrank
from 12,182,546 to 14,324 bytes. That scoped rebuild reused the existing
absolute dependency cache, not a claimed fresh combined audit.

The generic fill_block induction proves normality of exactly the allocated
bounded fields plus inherited base variables. `signature_normal` proves
normality of the ACTUAL TarskiSignature identity fill, including carrier,
decoder, universe, universe law, product and product law values.
`layer_normal` uses independently typed normal contextual equality witnesses;
`build_normal` preserves the invariant along any finite numeric vector.
`base k` is the actual original TS context/fill realization and
`concrete_normal k bs i` has NO normal-fill premise. The full interpreter's
decoder normality can therefore use this concrete fact without adding a
normal-fill condition to the source domain. No source quotation is assumed.

## Reproduction and checks

Raw logs: _build/normal-equality-fill.oGUP7S, RUN.sh/CHECK.sh.
To avoid redundant caches under current disk pressure, this NEW module used
the already independently verified LocalQuotationSpine build directory
/tmp/pts-rk-local-quotation-spine.nr1PlD. Its first successful compilation
printed all six NEW own assumption reports; no cached report is claimed.

```sh
cd /Users/akuklev/air/pts-rk
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-local-quotation-spine.nr1PlD \
  --display=short --no-buffer -j 2 theories/self_interpreter/NormalEqualityFill.vo
```

Attempts01/02 exit1: Dune registration pending, no proof rejected. Attempt03
exit0: all SIX own reports CLOSED. No proof revision, timeout, disk failure
or interruption occurred.

```sh
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-local-quotation-spine.nr1PlD/default/theories PTSrk \
  -Q /tmp/pts-rk-local-quotation-spine.nr1PlD/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-local-quotation-spine.nr1PlD/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.NormalEqualityFill
```

Recursive kernel exit0. The loaded inventory has only unchanged upstream
dependent functional extensionality and no unsafe fixpoints, assumed
positivity or type-in-type. Own endpoint reports are separately closed.
Forbidden-declaration scan exit1 (no matches). Independent full-source review
by the closed-package owner passed, explicitly checking bounded fields,
concrete TS identity values, original checked-layer realization and the
absence of any extra source-domain premise. Combined fresh aggregate,
pristine comparison and full CI remain separate later gates.

CHECK.sh records HEAD, complete installed package/version inventory and
tool versions: Rocq9.2.0, Stdlib9.1.0, Equations1.3.2+9.2, OCaml4.14.2,
Dune3.23.1, opam2.6.1; HEAD e822cd62df393faf4d5e4ed0c4c8fed173ccba6f.
