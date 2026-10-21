# Object-language indexed equality composition and map congruence

Source: theories/self_interpreter/IndexedCoherence.v.
SHA-256: 137c4fd12afe57ebea28692c5c456e510d5fd25254df6959f4acca6107f6973b.
Working directory: /Users/akuklev/air/pts-rk.
Fresh build directory: /tmp/pts-rk-indexed-coherence.3HnsbB.
Raw local evidence: _build/indexed-coherence.BPcsC4.

## Exact commands and retained outcomes

Both attempts were run by `bash _build/indexed-coherence.BPcsC4/RUN.sh NN`.
The runner captures the complete stdout/stderr in attempt-NN.log and the
immediately captured numeric exit code in attempt-NN.exit. Its build command is:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-indexed-coherence.3HnsbB --display=short --no-buffer theories/self_interpreter/IndexedCoherence.vo
```

- Attempt 01: exit 1. The typing and replacement proofs passed; the first
  error was line 168 in map_congruence_applies, where a lifted substitution
  remained under the lambda binder rather than simplifying to a shift.
  Explicit reduction of transpose/fin_match and the existing replace_fsucc
  lemma resolved this administrative syntax equation.
- Attempt 02: exit 0, all eleven new public assumption reports closed.

No other build attempt or timeout occurred. No theorem statement was weakened.

Recursive kernel command, kernel.log/kernel.exit, exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-indexed-coherence.3HnsbB/default/theories PTSrk -Q /tmp/pts-rk-indexed-coherence.3HnsbB/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-indexed-coherence.3HnsbB/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.IndexedCoherence
```

The recursive loaded-context inventory lists only the pre-existing
functional_extensionality_dep; no type-in-type, unsafe fixpoints or assumed
positivity. The eleven new theorem reports themselves are closed.

Version command, versions.log/versions.exit, exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Actual versions: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2 and Dune 3.23.1. Source hash was obtained with
`shasum -a 256 theories/self_interpreter/IndexedCoherence.v`.
Scoped git diff --check exits 0. The source safety scan for admissions,
new axioms/parameters and disabled checks has no matches (rg exit 1).
Full CI, pristine comparison and the combined audit are separate parent checks.

## Exact scope and remaining boundary

All constructions are actual original annotated PTS terms with original
Typing.typ proofs. With A:U_a, compose builds Eq_b(A,u,w) from
e:Eq_b(A,u,v) and f:Eq_b(A,v,w), at the SAME predicate level b. Its equality
type has sort max(a+2,b+1). Nondependent map_congruence builds
Eq_b(B,g u,g v) from g:A->B and e:Eq_b(A,u,v), where B:U_d; its equality
type has sort max(d+2,b+1), again preserving b. The map motive is constructed
as the actual lambda x:A.P(g x), not assumed.

Replacement commutes with both evidence constructors. Application equations
are original beta reduction: composed transport performs the two supplied
transports, and mapped transport applies the supplied equality proof to the
constructed map motive. Two reflexivity proofs compose to literal reflexivity;
mapping literal reflexivity reduces to literal reflexivity at g u, including
the administrative beta redex in its lambda annotation.

For arbitrary evidence e, left/right identity equations are deliberately
stated AFTER application to a motive P and input z. No eta contraction of
lambda P.lambda z.e P z to e is claimed. This module does not supply
dependent function extensionality, same-level symmetry, source-conversion
coherence, a globally inhabited arbitrary algebra, or a complete dependent
PHOAS quotation. It supplies independently typed operations for combining
already available local coherence witnesses.
