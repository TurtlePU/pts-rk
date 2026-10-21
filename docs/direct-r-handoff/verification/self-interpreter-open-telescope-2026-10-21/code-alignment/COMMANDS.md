# Actual globally allocated code alignment

Date: 2026-10-21. Source: `theories/self_interpreter/CodeAlignment.v`,237 lines.
Frozen SHA-256: `108a287af1c10409b05fa0b2a600474d86f512d6946fbd49187d46d4cea5e48f`.
No Git mutation; only own module and evidence edited.

## Checked contracts

`align` consumes the ACTUAL fresh global ContextualEqualityExtension field
under the shifted dependent telescope. Independently typed E:C→U_r and
q:E a give original typing at E b. Full normality needs normal E/q; neutral
shape is unconditional. The actual extended identity fill reduces alignment
to the LITERAL previously filled q, and direct filled original typing is
proved separately with independently justified field realization.

The smart dependent `application` allocates code equality R=p_ab A B,
aligns f:El_c R with predicate El_c, and invokes ScopedTarski's actual
smart application. Original context wf and independently typed inputs
derive its original dependent result type. Full normality follows from
normal A,B,f,u even when B is a lambda: smart decoded annotations avoid the
administrative redex. Actual filled alignment erases INSIDE the literal
original smart application. Its subsequent existing semantic recovery can
be composed without normalizing the source payload. This is an actual
equality-only field consumer, not a full source compiler or an assumed
coherence hypothesis. The inherited finite interface remains a typed
variable environment beneath all local binders.

## Commands and failures

Fresh absolute Dune directory `/tmp/pts-rk-code-alignment.bCOFfn`; raw local
evidence `_build/code-alignment.F8pcWA`. RUN.sh/CHECK.sh retain exact output,
dates, exit statuses and versions.

```sh
cd /Users/akuklev/air/pts-rk
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-code-alignment.bCOFfn \
  --display=short --no-buffer -j 2 theories/self_interpreter/CodeAlignment.vo
```

All failed attempts exit1; successful attempts exit0. Attempt01: excessive
cbn hid a pointwise substitution-square rewrite; fixed by an explicit
shift equality. Attempt02: initial eight endpoints closed. Attempt03:
redundant tactic after f_equal solved the product-renaming goal. Attempt04:
unfolding EX.lifted obscured decoder-renaming rewrite. Attempts05/06:
context placeholder in change could not be inferred; changed only the
explicit type subexpression. Attempt07: wrong unfold occurrence in the
application recovery rewrite. Attempt08: explicit target context/TypedRen
needed by application_term_rename. Attempt09: all ELEVEN own reports CLOSED.
No theorem weakening, timeout, disk failure or interruption occurred.

```sh
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-code-alignment.bCOFfn/default/theories PTSrk \
  -Q /tmp/pts-rk-code-alignment.bCOFfn/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-code-alignment.bCOFfn/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.CodeAlignment
```

Recursive kernel exit0. Loaded inventory: unchanged upstream dependent
functional extensionality only, no unsafe fixpoint, assumed positivity or
type-in-type. Own eleven reports are separately closed. Forbidden-declaration
scan exit1 means no matches. Independent full-source review by the contextual
field enumeration owner passed at the frozen hash, checking actual field
consumption, original smart-application typing, full guarded normality and
literal filled payload erasure. Later aggregate, pristine comparison and
complete CI are separate gates.

CHECK.sh records HEAD and exact version commands (git rev-parse HEAD,
rocq -v, dune --version, ocamlc -version, opam --version, opam list
--installed --columns=name,version): Rocq9.2.0, Stdlib9.1.0,
Equations1.3.2+9.2, OCaml4.14.2, Dune3.23.1, opam2.6.1;
HEAD e822cd62df393faf4d5e4ed0c4c8fed173ccba6f.
