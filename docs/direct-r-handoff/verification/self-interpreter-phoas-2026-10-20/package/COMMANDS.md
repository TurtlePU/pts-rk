# Finite source-indexed PHOAS package — 2026-10-20

`PHOASAlgebra.v` specializes the genuinely polymorphic rank-pair Abs/App
operations at interpreted source types. `PHOASPackage.v` supplies an actual
finite context, closes it to original annotated PTS terms, and constructs
the identity interpretation as a typed simultaneous substitution.

At budget `k`, the context contains the ground variable, `k+2` family
variables, and both operations for each pair `a,b <= k`: altogether
`k+3+2(k+1)^2` parameters. The extra family at `k+1` types unused boundary
handlers. All lookups needed by the bounded source derivation are proved in
range; no law for an infinite neutral palette or fallback above the budget
is assumed. The source is the independent annotated Church-STLC derivation
system. This is not a full-dependent-PTS interpreter.

Checked endpoints include original `quote_typed`, beta-normal `quote_normal`,
fixed-budget `quote_injective` and `quote_conversion_injective`, literal
`fill_typed`, and strong `payload_recovers` and `run_quote_recovers`.
`every_source_quote` gives existential coverage from the independent Prop
source judgment. Executable quotation consumes independent Type-valued
derivation data. Recovery uses actual identity arguments, not a precomputed
normal form. The type-sort theorem is existential; no exact package or
decoder rank is claimed here. A fixed object-language decoder is the separate
`PHOASDecoder.v` integration.

Exact compiler command, run from the repository root:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH \
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam \
opam exec --switch=pts-rk-ci -- dune build \
  --build-dir=/tmp/pts-rk-phoas-package.MH6KEA/build \
  --display=short --no-buffer theories/self_interpreter/PHOASPackage.vo \
  > _build/phoas-package.sJlpbJ/package-NN.log 2>&1
build_status=$?
tail -40 _build/phoas-package.sJlpbJ/package-NN.log
exit "$build_status"
```

Raw logs remain in ignored `_build/phoas-package.sJlpbJ`. The initial
`algebra-01.log` command used the same environment/build directory with
target `PHOASAlgebra.vo` and exited 0. This Dune directory was freshly created
for this development. Compilation attempts were:

- Package 01--05: exit 1, respectively list/lambda notation conflict,
  Prop-to-Type elimination in a context-well-formedness helper, an unresolved
  formation rank, an uninferred term-label type, and a context placeholder.
  The helper now uses the actual explicit rank of each handler declaration;
  no elimination restriction or typing rule was weakened.
- Package 06: exit 0, finite contexts and original lookup typing complete.
- Package 07--10: exit 1, respectively an impossible `Fin 0` branch,
  an uninferred budget, and two normal-conversion lemma namespace errors.
- Package 11--13: exit 1, explicit source-lookup induction and dependent
  slot rewrite fixes, then a local identifier colliding with the STLC
  constructor `base`.
- Package 14--15: exit 1, nested substitution distribution and an automatically
  renamed impossible finite-index hypothesis.
- Package 16: exit 0, all finite identity-fill laws and original `TypedSub`
  complete.
- Package 17: exit 0, final recovery/coverage endpoints and assumption reports.
  It printed 2 closed reports for `PHOASAlgebra`, 4 for its recompiled recovery
  dependency, and 11 for `PHOASPackage`. Every report was
  `Closed under the global context`.

No timeout occurred. Existing overlapping-logical-loadpath warnings remain
visible in the logs. The package sources are frozen at attempt 17.

Toolchain inventory (exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH \
OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam \
opam exec --switch=pts-rk-ci -- sh -c \
  'rocq -v; dune --version; ocamlc -version; opam list --installed --columns=name,version' \
  > _build/phoas-package.sJlpbJ/versions.log 2>&1
```

Observed: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. Scoped `git diff --check` exited 0.
Root owns the final independent fresh aggregate, recursive kernel check,
and complete local CI; those are not claimed by this module-only build.

Final source SHA-256:

```text
d5180f6efa44c2a03bafd7712c161a4a2b0045b7ce0fb4e4a94ce6671cc2cb2e  theories/self_interpreter/PHOASAlgebra.v
8dff8574ecb500e058dcfcfc3159fad559da5fa066febd4a8d898f52a637febf  theories/self_interpreter/PHOASPackage.v
```
