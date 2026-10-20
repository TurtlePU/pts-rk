# Original-PTS raw HOAS encoding

Working directory: `/Users/akuklev/air/pts-rk`.
Fresh build directory: `/tmp/pts-rk-hoas.kEs9Sw/build`.

Every numbered attempt ran this exact command, with `NN` replaced by the
two-digit attempt number:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-hoas.kEs9Sw/build --display=short --no-buffer theories/self_interpreter/ChurchSyntax.vo > docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/hoas/attempt-NN.log 2>&1
```

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | Missing closing parenthesis in the initial quotation definition. |
| 02 | 1 | Missing closing parentheses in the initial code-type definition. |
| 03 | 0 | HOAS definitions compiled. |
| 04 | 1 | Bound-name collision in environment extensionality proof. |
| 05 | 1 | Unspecified sort-label type in transpose helper. |
| 06 | 0 | Definitions, environment extensionality, and full normality compiled. |
| 07 | 1 | Dependent elimination removed an induction binder in carrier-variable typing. |
| 08 | 1 | Underdetermined context placeholder in quotation typing. |
| 09 | 0 | Complete module; six closed transitive assumption reports. |

No timeout occurred. `source.sha256` records the source after attempt 09.
The six reports cover `quote_normal`, `ast_fold_typed`, `bind_vars_typed`,
`quote_typing`, `code_type_sort`, and
`every_original_term_has_church_code`. The last theorem covers every original
raw annotated `Term nat m`, with no source typing or rank premise. The quote
is a closed beta-normal original PTS term with the original type
`code_type r m : U_(r+3)`; source variables are represented by host variables
under `m` additional carrier binders. Product and lambda annotations remain
explicit handler arguments. This is target-typed raw HOAS, not an
intrinsically source-typed PHOAS representation or a dependent evaluator.

Version commands (exit 0) were run under the same PATH/OPAMROOT prefix:

```sh
opam exec --switch=pts-rk-ci -- sh -c 'rocq --version; ocamlc -version; dune --version; opam list --installed --short --columns=name,version rocq-core rocq-stdlib coq-equations'
opam exec --switch=pts-rk-ci -- opam list --installed --columns=name,version
shasum -a 256 theories/self_interpreter/ChurchSyntax.v
git diff --check -- theories/self_interpreter/ChurchSyntax.v
```

Outputs are retained in `versions.log`, `packages.log`, and `source.sha256`.
The version filter did not select the renamed Equations package; the full
package inventory records it. Diff whitespace check exited 0.
The parent task performs the aggregate fresh audit and recursive kernel
check; this directory does not claim those broader checks.
