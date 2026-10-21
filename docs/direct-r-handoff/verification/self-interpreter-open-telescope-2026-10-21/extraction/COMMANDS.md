# Actual full-quoter extraction sanity check

Working directory: /Users/akuklev/air/pts-rk.
Raw evidence and complete probe/runner sources:
_build/self-interpreter-extraction.QFuxgY.
Dune cache: /tmp/pts-rk-checked-contextual.vLMi7j (same-phase reuse).

This checks the ACTUAL full structural quoter on the independent closed
source derivation `d_sort ε 0`, then its actual raw term and closed type and
faithful term programs. It is not a hand-written implementation of the sort
case. No lambda/application example was attempted: exhaustive equality-layer
enumeration has no practical performance claim. A successful finite run does
not replace the separately checked all-source theorem.

All commands use the pinned environment:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1; independently retained version output in sibling
local-code-alignment raw versions.log/exit, exit 0, using:

```sh
opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

## Commands and results

`bash _build/self-interpreter-extraction.QFuxgY/BUILD.sh` ran:

```sh
opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-checked-contextual.vLMi7j --display=short --no-buffer theories/self_interpreter/FullDependentInterpreter.vo
```

dependencies.log/exit: exit 0, including the actual four closed reports for
RecursiveQuotation and fourteen for FullDependentInterpreter.

`bash _build/self-interpreter-extraction.QFuxgY/EXTRACT.sh 01` ran:

```sh
opam exec --switch=pts-rk-ci -- rocq compile -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories PTSrk -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories/self_interpreter PTSrk.SelfInterpreter _build/self-interpreter-extraction.QFuxgY/Probe.v
```

extract-01.log/exit: exit 0. The standard extractor reports that it accessed
opaque helper bodies (actual context-formation and morphism helpers); the full
warning is retained. The generated OCaml contains standard dependent-erasure
`Obj.magic` and impossible-case assertions. These are OCaml extraction artifacts,
not new source Rocq axioms or unsafe casts. No claim is made that all dependent
record projections reduce equally readily with direct Rocq `vm_compute`.

`bash _build/self-interpreter-extraction.QFuxgY/RUN.sh` ran:

```sh
probe_dir=/Users/akuklev/air/pts-rk/_build/self-interpreter-extraction.QFuxgY
opam exec --switch=pts-rk-ci -- ocamlc -I "$probe_dir" -o "$probe_dir/probe.exe" "$probe_dir/probe.mli" "$probe_dir/probe.ml" "$probe_dir/main.ml"
/usr/bin/time -p /usr/local/bin/timeout 60 "$probe_dir/probe.exe"
```

ocaml-build.log/exit: exit 0, empty compiler log. run.log/exit: exit 0,
under the explicit 60-second runtime cap:

```text
empty_plan=true normal_term=true normal_type_program=true normal_quote=true
real 0.37
user 0.02
sys 0.01
```

All attempts succeeded; there were no retries, runtime timeouts, ignored
compiler failures, repository proof changes or Git actions for this probe.
The generated implementation is 7,979 lines (278 KiB); the extracted interface
is approximately 20 MiB because it retains imported module signatures.

## Exact probe sources

Probe.v:

```coq
From Stdlib Require Import Lists.List Bool.Bool Extraction ExtrOcamlBasic.
From PTSrk Require Import -(notations) Syntax Context.
From PTSrk.NormalizationComplexity Require Import Greedy.
From PTSrk.SelfInterpreter Require FullSource FullDependentInterpreter
  FullQuotation QuotationJudgment.
Import Context ListNotations.

Definition source := FullSource.FullSource.d_sort ε 0.
Definition computed := FullDependentInterpreter.FullDependentInterpreter.closed_quote source.
Definition probe_summary : bool * (bool * (bool * bool)) :=
  (match FullQuotation.FullQuotation.flatten
      (FullQuotation.FullQuotation.result_plan computed) with
   | [] => true | _ => false end,
   (normalb (QuotationJudgment.QuotationJudgment.term_code
      (FullQuotation.FullQuotation.result_judgment computed)),
    (normalb (FullDependentInterpreter.FullDependentInterpreter.closed_type_program source),
     normalb (FullDependentInterpreter.FullDependentInterpreter.closed_program 0 source)))).

Extraction Language OCaml.
Extraction "/Users/akuklev/air/pts-rk/_build/self-interpreter-extraction.QFuxgY/probe.ml" probe_summary.
```

main.ml:

```ocaml
let () =
  let (empty_plan, (normal_term, (normal_type_program, normal_quote))) = Probe.probe_summary in
  Printf.printf "empty_plan=%b normal_term=%b normal_type_program=%b normal_quote=%b\n%!"
    empty_plan normal_term normal_type_program normal_quote;
  if not (empty_plan && normal_term && normal_type_program && normal_quote) then exit 1
```

The supplied source derivation is computational data. Original Prop-typing
coverage remains a separately proved Prop existential; this probe does not
claim to extract a source derivation from an erased typing proof.
