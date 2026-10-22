# GenericFold: independent incremental check, 22 October 2026

The new source was developed outside the repository while the parent's
source-manifest audit was active. No repository source, Dune file, or
shared build cache was changed by this check.

## Exact implementation contract

For a fixed original well-formed dependent telescope `D`, `C : U0`, and
`E : C -> Us`, the actual closed original PTS term is

```
head = lambda P : TypeProgram. lambda Q : TermProgram(P).
         lambda fields : D. Q fields
```

Its type is `Pi P : TypeProgram. TermProgram(P) -> TermProgram(P)`.
The remaining telescope arguments of the returned term program are the
algebra fields. No selected algebra filling occurs in `head`.
`run` supplies the fields as ordinary original PTS applications.
There is no eta-conversion assumption: explicit expansion computes by
beta reduction only after the ordinary field arguments are supplied.

Checked endpoints: substitution naturality of expansion; original typing
and normality of expansion; original head typing, explicit type sort and
normality; first specialization beta step and full specialization;
specialization typing; expansion/field application computation; general
run computation and original typing; literal substitution computation on
closed telescope programs; syntactic composition of two such folds.

Normality assumes the fixed telescope annotations, C and E are normal,
with E neutral, as for the existing specialized decoder. It does not
assume normality of a selected algebra, since no filling is built in.
Run typing assumes actual original typing of the supplied finite algebra
fields and represented type/term programs. No source semantics, recovery,
quotation, or alternative algebra correctness premise is assumed.
Composition is a raw computational equation, not a new semantic theorem
or a typing theorem for arbitrary incompatible intermediate interfaces.
Signatures remain plan-specific; rank-only signatures and nonidentity
dependent coherence fillings are not obtained here.

## Commands and attempts

Run `bash /tmp/pts-rk-generic-fold.AlVdu8/compile.sh NN` from any directory.
The script records UTC start/end, exit status and complete compiler output
under `attempt-NN.{start,end,exit,log}`. Its exact compiler command is:

```
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
cd /Users/akuklev/air/pts-rk
opam exec -- rocq compile -q \
  -Q /tmp/pts-rk-fold-fresh.VfFDz4/default/theories PTSrk \
  -Q /tmp/pts-rk-fold-fresh.VfFDz4/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-fold-fresh.VfFDz4/default/theories/self_interpreter PTSrk.SelfInterpreter \
  -Q /tmp/pts-rk-generic-fold.AlVdu8 PTSrk.SelfInterpreter \
  -o /tmp/pts-rk-generic-fold.AlVdu8/GenericFold.vo \
  /tmp/pts-rk-generic-fold.AlVdu8/GenericFold.v
```

- Attempt 01: exit 1 at source line 148; pointwise equality in
  `fold_expand` needed symmetry before `DP.lift_closed_zero`.
- Source revision: added that `symmetry`; no statement or premise changed.
- Attempt 02: exit 0, **14** `Closed under the global context` reports.
  The logical-loadpath remapping warning is preserved in the log.

Source SHA256:
`efc4e7d9960f11809b3f96f5f9a54afa69cfb46931a7c0f274424866ec3f0c81`.
Compiled object SHA256:
`cb2dba26f2b3f7cd318dd834db109be20e9ab12237817d89613dce036d97cff9`.
Attempt 02 log SHA256:
`d048e436cfa1bbc8ecd0d94be2977a5a65ebaee0af902267ce5c5c19b35d1e41`.

An explicit `rg` scan found no proof escapes or trailing whitespace in
the source. Its exit 1 means no matches. This is a fresh compilation of
this one new file against the parent's fresh built dependencies, not a
second complete repository or upstream audit. Integration still requires
the parent's source-stable build and audit entry points.
