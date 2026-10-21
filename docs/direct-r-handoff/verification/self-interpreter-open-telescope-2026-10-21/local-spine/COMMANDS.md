# Literal-scope local quotation spines

Date: 2026-10-21. Frozen source: theories/self_interpreter/LocalQuotationSpine.v,
448 lines, SHA-256 6748b812547d2890b2528c912543a7feea9958017ba13cf29826588505b3c45b.
No Git/index mutation; coordinator owns shared Dune/Audit/prose.

The original proof checkpoint below had 457 lines and SHA-256
2820e2506fa803efaa84efa8aa3e604894c77ab6d2dfe92aba54d5492170aed2.
A coordinator-authorized mechanical cleanup removed nine redundant exported
module aliases and expanded their qualified uses. A consumer search found
no uses of those nested aliases. No definition, theorem contract or proof
logic changed. Exact before-sources, expansion script and full diffs are in
_build/local-alias-cleanup.yfL2pV. The exact rewrite was:

```sh
perl -0777 -i -p _build/local-alias-cleanup.yfL2pV/EXPAND.pl \
  theories/self_interpreter/LocalQuotationSpine.v \
  theories/self_interpreter/NormalEqualityFill.v
```

Rebuild in LocalInitialState attempt03 exit0 reprinted all 26 own CLOSED
reports. Repeated recursive kernel check of LocalQuotationSpine,
NormalEqualityFill and LocalInitialState exited0; full commands, versions,
hashes and output are in _build/local-initial-state.mTFIrR/CHECK.sh and
kernel.log. The compiled object shrank from 89,150,612 to 100,467 bytes.
This rebuild reused the existing absolute cache but actually recompiled
the changed module; a fresh combined aggregate remains a separate gate.

The snoc spine has literal source width n and target width n+base. A push
therefore has definitionally the original source scope S n and target scope
S(n+base). `state` contains the actual independently formed normal local
declarations, original signature environment, and QC.realization into the
SAME literal source context H. It has no source-quotation premise.
`extend_state` applies a whole numerical budget vector, preserving H by an
original TypedSub proof. `push_state` uses independently typed/normal target
declaration and its actual literal source recovery. `extended_push_domains`
is reflexive: after a recursive global extension the last local binder is
exactly the renamed original declaration. No source binder is normalized.

`present` computes an existing CT telescope, retaining both source and target
scope equalities, original context equality, formation, full annotation
normality, and the exact fill square. `body`/`unbody` only eliminate equality
of natural-number scope indices; their typing, inverse and normality proofs
use no unsafe casts or extra axioms. `body_filled` and `filled_conversion`
retain the literal source filling. Composition/identity of local renaming,
numeric-vector concatenation and recursive code-view preservation are
proved. Exact target-renaming naturality between the two spine formats is
a separate follow-up module; no full recursive quoter is claimed here.

## Commands and results

Fresh absolute build: /tmp/pts-rk-local-quotation-spine.nr1PlD.
Raw logs: _build/local-quotation-spine.6myUh0. RUN.sh/CHECK.sh retain commands,
dates, versions, hashes, complete output and exit codes.

```sh
cd /Users/akuklev/air/pts-rk
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-local-quotation-spine.nr1PlD \
  --display=short --no-buffer -j 2 theories/self_interpreter/LocalQuotationSpine.vo
```

Attempt01 exit1: registration pending. Attempt02 exit1: an induction proof
used an automatically named hypothesis that was not generated. Attempt03
exit1: supplied the explicit sigma parameter to the induction hypothesis.
Attempt04 exit1: made both sides of a successor-index equality explicit.
Attempt05 exit1: made the closed-renaming RHS explicit. Attempt06 exit1:
supplied the original base context to formed_rename. Attempt07 exit1:
supplied both substitutions explicitly to the fill-square rewrite.
Attempts08/09 exit1: normalized reflexive scope casts in the local-fill
equation with an exact change. Attempt10 exit1: exposed the literal original
typing goal before rewriting its context. Attempt11 exit1: filled_conversion
needed its substitution equation at BOTH endpoints. Attempt12 exit0 with all
TWENTY-SIX own reports CLOSED. No proof weakening, timeout, disk failure or
interrupted compilation occurred.

```sh
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-local-quotation-spine.nr1PlD/default/theories PTSrk \
  -Q /tmp/pts-rk-local-quotation-spine.nr1PlD/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-local-quotation-spine.nr1PlD/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.LocalQuotationSpine
```

Recursive kernel exit0. Loaded inventory contains only unchanged upstream
dependent functional extensionality, with no unsafe fixpoints, assumed
positivity or type-in-type; all 26 own reports are separately closed.
Forbidden-declaration scan exit1 (no matches). Independent full-source review
by the quotation-recursion owner passed: literal source H, independent push
typing/domain recovery, complete old-local/new-global TypedSub, and exact
scope/fill presentation were checked. No source-context normalization or
quotation hypothesis is hidden. Fresh combined aggregate/pristine/full CI
are separate later gates.

CHECK.sh records HEAD, rocq -v, dune --version, ocamlc -version, opam --version,
and the installed package/version inventory. Pinned versions: Rocq9.2.0,
Stdlib9.1.0, Equations1.3.2+9.2, OCaml4.14.2, Dune3.23.1, opam2.6.1;
HEAD e822cd62df393faf4d5e4ed0c4c8fed173ccba6f.
During this development the coordinator ran Dune clean on three validated
completed earlier own caches (GlobalEqualityInsertion, QuotationViewRenaming,
CodeAlignment) and the other agent's completed transport cache to recover
disk space. Source and all raw/scoped evidence were retained. This active
cache was not cleaned.
