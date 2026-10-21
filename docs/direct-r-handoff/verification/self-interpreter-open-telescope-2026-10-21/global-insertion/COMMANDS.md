# Global equality insertion into a literal source context

Date: 2026-10-21. Frozen source: theories/self_interpreter/GlobalEqualityInsertion.v,
213 lines, SHA-256 96216547ec708e0d965e70adfd014bc4eb2b533d8d3de46d0757904cf96944c4.
No Git/index mutation; coordinator owns shared Dune/Audit/documentation.

The original TypedSub extension is proved into the SAME literal source
context H, not only the syntactically substituted telescope. Every variable
under an inserted global field is either inherited or the new base field;
the latter has an independently typed closed normal equality realizer.
The actual QC.realization and all old recursive code/shape views are retained.
The generic base_extension_realization also handles a complete finite numeric
layer/vector, using actual typed base renaming, exact context lookup and fill
equations, independently typed closed fill, and original telescope formation.
No quotation existence, source-context equality or semantic payload field is
assumed.

## Commands and outcomes

Fresh build directory: /tmp/pts-rk-global-equality-insertion.kysmeL.
Raw evidence: _build/global-equality-insertion.CR4XKY; RUN.sh/CHECK.sh retain
exact commands, versions, dates, complete output and exit codes.

```sh
cd /Users/akuklev/air/pts-rk
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-global-equality-insertion.kysmeL \
  --display=short --no-buffer -j 2 theories/self_interpreter/GlobalEqualityInsertion.vo
```

Attempt01 exit1: Dune registration pending. Attempt02 exit1: induction
introduced n already used by the telescope constructor. Attempt03 exit1:
the specialized substitution lemma did not match replacing a shifted
declaration; used the exact replace_rename equation. Attempt04 exit1:
an implicit RHS placeholder could not infer the existing TS.fill; supplied
it explicitly. Attempt05 exit0 with seven closed reports. Attempt06 exit0
after adding generic finite-base extension, with all NINE own reports CLOSED.
No timeout, disk failure, proof weakening or interrupted compilation.

```sh
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-global-equality-insertion.kysmeL/default/theories PTSrk \
  -Q /tmp/pts-rk-global-equality-insertion.kysmeL/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-global-equality-insertion.kysmeL/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.GlobalEqualityInsertion
```

Recursive kernel exit0. Loaded inventory contains only unchanged upstream
dependent functional extensionality, no unsafe fixpoints/assumed positivity
or type-in-type; own reports are separately closed. Forbidden-declaration
scan exit1 (no matches). Fresh aggregate/pristine/full CI are separate later
gates, not claimed here.

Independent full-source review by the coordinator passed: complete
image/base variable classification, actual closed new-field typing, same
literal source context, exact lookup/renaming/fill equations, and the
whole-base-extension generalization were checked. After completion, the
coordinator ran Dune clean on this completed cache and the completed
CodeAlignment/QuotationViewRenaming caches to recover disk space. Their
independent raw logs/hashes and scoped evidence were retained; this does
not change the successful historical commands above.

Recorded versions: Rocq9.2.0, Stdlib9.1.0, Equations1.3.2+9.2, OCaml4.14.2,
Dune3.23.1, opam2.6.1. HEAD e822cd62df393faf4d5e4ed0c4c8fed173ccba6f.
