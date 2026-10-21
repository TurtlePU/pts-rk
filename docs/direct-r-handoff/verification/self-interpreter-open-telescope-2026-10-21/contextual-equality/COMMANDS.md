# Normal contextual equality realizers

Date: 2026-10-21. Repository: `/Users/akuklev/air/pts-rk`.
Source: `theories/self_interpreter/ContextualEqualityRealizer.v`,195 lines.
Frozen SHA-256:
`36f94438093c37a368f8164733da3ae5a79623da39d136ad08d1526fa9705221`.
Only this new module and scoped evidence were edited; coordinator owns
Dune/Audit/shared prose. No Git mutation.

## Contract and independent review

For independent original wf G, formed dependent telescope D, and endpoint
typings C:U_c and u,v:C with original u~v, `normal_witness` is an actual
NORMAL program at the LITERAL type `CT.close_type D (IE.eq_type d C u v)`.
D and its annotations need not be normal. It closes the independently typed
RealizedEquality reflexivity program and applies the existing executable
metalevel canonicalizer to that lambda closure. The desired original type is
retained by original preservation, not a new typing rule or subject expansion.
Exact declaration rank is `CT.rank rs (max(c+2,d+1))`, numerically <=k+2
for rank-vector entries,c,d<=k.

The normalization does NOT weaken literal recovery. A structural `eraser`
invariant identifies |rs|+2 lambdas ending in the final variable. Ordinary
replacement, greedy reduction and every number of rounds preserve it.
`normal_witness_erases` therefore proves that arbitrary complete telescope
arguments followed by P,z compute to the LITERAL z, even after arbitrary
base substitution. No typing/normality condition on that returned payload
is needed. Direct original typing of the actual run and transport is proved
separately from recovery. This is equality-only realization, not arbitrary
payload normalization, a uniform field enumeration or a full source quoter.

Independent read-only review by the source-validity/telescope-recovery owner
passed at the frozen hash. It specifically checked eraser preservation,
literal arbitrary application, original typing, and the nonnormal-D boundary.
No correction requested.

## Commands, failures and kernel

Fresh directories were obtained with `mktemp -d`:
`/tmp/pts-rk-contextual-equality-realizer.QkRvlm` and
`_build/contextual-equality-realizer.nVdSFw`.
Retained `RUN.sh NN` writes each attempt's complete output and exact exit:

```sh
cd /Users/akuklev/air/pts-rk
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-contextual-equality-realizer.QkRvlm \
  --display=short --no-buffer -j 2 \
  theories/self_interpreter/ContextualEqualityRealizer.vo
```

Attempt01 exited1 because Dune registration was pending; no theorem was
checked. Attempt02 was the first real proof build and exited0, with all
TWELVE own reports CLOSED. No proof weakening, timeout, interruption or
disk failure occurred.

Retained `CHECK.sh` exited0, including this recursive kernel command:

```sh
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-contextual-equality-realizer.QkRvlm/default/theories PTSrk \
  -Q /tmp/pts-rk-contextual-equality-realizer.QkRvlm/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-contextual-equality-realizer.QkRvlm/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.ContextualEqualityRealizer
```

`kernel.exit` is0. Recursive loaded inventory: unchanged upstream dependent
functional extensionality only; no unsafe fixpoint, type-in-type or assumed
positivity. This is distinct from the twelve CLOSED own theorem reports.
Forbidden-declaration scan exit1 means no matches. Hash and raw log/driver
files are retained locally; later aggregate/pristine checking is separate.

CHECK.sh also records HEAD and full tool/package versions: Rocq9.2.0,
Stdlib9.1.0, Equations1.3.2+9.2, OCaml4.14.2, Dune3.23.1, opam2.6.1;
HEAD `e822cd62df393faf4d5e4ed0c4c8fed173ccba6f`. Exact commands are
`git rev-parse HEAD`, `rocq -v`, `dune --version`, `ocamlc -version`,
`opam --version`, `opam list --installed --columns=name,version` under the
same pinned environment. Raw scripts/logs are generated local evidence.
