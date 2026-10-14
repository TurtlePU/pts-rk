# BZC foundation audit — 2026-10-14

Proof-source baseline: c91f9564856a2a94afb7e2d55432693ae2d92bf0.
This continuation changes audit/handoff documentation only. Existing user
logs/ and generated .lia.cache are preserved. No external write is needed
for this review request.

Commands run at the repository root:

```sh
export OPAMROOT="$HOME/.local/share/pts-rk-ci/opam"
export PATH="$HOME/.local/share/pts-rk-ci/bin:$PATH"
opam exec --switch=pts-rk-ci -- timeout 180 dune build --display=short --no-buffer ZFC_model/ModelSoundness.vo ZFC_model/MaterialZermelo.vo ZFC_model/BoundedFormulaSelection.vo > /tmp/pts-rk-bzc-audit-baseline.log 2>&1
```

Exit 0. Cached build; its empty compiler log is not a fresh recompilation
or a new foundation-strength theorem.

```sh
# Fresh output directory allocated by mktemp -d /tmp/pts-rk-bzc-audit.XXXXXX.
opam exec --switch=pts-rk-ci -- timeout 180 rocq c -Q _build/default/vendor/zfc ZFC -Q _build/default/theories PTSrk -Q _build/default/ZFC_model PTSrkModel -o /tmp/pts-rk-bzc-audit.NmrOLS/AUDIT.vo docs/direct-r-handoff/verification/model-soundness-2026-10-14/AUDIT.v > /tmp/pts-rk-bzc-audit-types.log 2>&1
```

Exit 0; 14 closed Print Assumptions reports. Adjacent types.log is the raw
output. The explicit hierarchy/classical/cardinal/Choice premises remain
visible in the printed types. No proof-source change, new axiom, admitted
proof or changed PTS rule was made. No timeout or compiler failure occurred.

Source review found no material GCH/hierarchy axiom or derivation in the
current .v files. MaterialZermelo.bzc_satisfied goes from ambient Ens to
BZC satisfaction; it is not the converse internal construction theorem.
See ZFC_model/BZC_AUDIT.md for the mathematical and source findings.
