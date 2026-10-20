# Full-PTS rank-indexed normalization and canonical HOAS codes

Working directory: `/Users/akuklev/air/pts-rk`.
Fresh absolute Dune build: `/tmp/pts-rk-ranked-normalization.uzxYum/build`.
Disposable raw logs: `_build/ranked-normalization.r7bYSG/` (ignored).
No commit or push; no original kernel or normalization-library source edited.

Each numbered attempt ran this exact command, substituting the two-digit
attempt number for `NN`. Its exit code was captured in `status` immediately,
the log tail displayed, and the shell exited with that code:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-ranked-normalization.uzxYum/build --display=short --no-buffer theories/self_interpreter/RankedNormalization.vo > _build/ranked-normalization.r7bYSG/attempt-NN.log 2>&1
```

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | New module had not yet been registered by the Dune owner. |
| 02 | 0 | Full-PTS semantic correctness and canonical equality/conversion compiled. |
| 03 | 1 | Arithmetic abstraction distinguished convertible hidden scope indices in `nodes q`. |
| 04 | 1 | Diagnostic goal output confirmed the same scope-index issue. |
| 05 | 0 | Full module, ten closed transitive assumption reports. |

No timeout occurred. Final source SHA-256:

```text
8cba486895077ccbfa417cc4cdc22eb1a8cd7d26c447e3e88c4c3f3a9a9335e1  theories/self_interpreter/RankedNormalization.v
```

The reports cover `normalized_source_correct`,
`normalized_quote_typed_normal`, `normalized_quote_conversion_iff`,
`normalized_quote_equal_iff`, `quote_nodes`, `normalized_quote_size`,
`automatic_quote_correct`, `automatic_quote_equal_iff`,
`automatic_quote_conversion_iff`, and `automatic_quote_size`.

`normalized_quote r d t` computes `ChurchSyntax.quote r (rounds d t)`.
Original `Typing.typ`, well-formed contexts, and the existing semantic
`RedexBound` justify normality, beta reachability, and preservation of the
exact original source type. The automatic closed version computes
`conservativeRank`; no rank-success or termination premise is supplied.
Canonical codes are equal exactly when their originally typed sources are
beta-convertible, even when source types and sufficient budgets differ.
Code beta conversion additionally identifies the external carrier rank.

The exact HOAS output-node equation is `34 + 2*n + hoas_mass t`; the mass
includes all annotations and unary representations of source sort labels.
This gives the checked bound
`34 + 2*n + (2*maxRankLiteral t+5)*tower d (nodes t)` for normalized codes.
The automatic bound replaces the tower height by `2*encodingSize t+1` and
its bottom argument by `encodingSize t`.

Cost statements explicitly charge ONLY the existing normalization stage:
`tower (2*d+1) (nodes t+5*d+2)` for a supplied bound, and
`tower (4*s+3) (18*s+8)` automatically, including automatic rank discovery.
They do not claim a running-time bound for constructing/serializing the
HOAS code, nor an internal PTS interpreter. Output constructor count is not
a bit-complexity or unary-index-serialization bound. This is an executable
metalevel canonicalization interface for the full original calculus.

Versions were checked with the same PATH/OPAMROOT prefix:

```sh
opam exec --switch=pts-rk-ci -- sh -c 'rocq --version; ocamlc -version; dune --version; opam list --installed --columns=name,version rocq-core rocq-stdlib rocq-equations'
shasum -a 256 theories/self_interpreter/RankedNormalization.v
git diff --check -- theories/self_interpreter/RankedNormalization.v
rg -n 'Admitted|admit|Axiom|Parameter|Unset Guard|Unset Universe' theories/self_interpreter/RankedNormalization.v
```

Version command exited 0: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1; raw output is in `versions.log`. Hash and scoped
diff checks exited 0; the forbidden-marker scan exited 1 (no matches).
The parent task owns broader aggregate/recursive-kernel/full-CI checks;
these local logs do not claim those checks.
