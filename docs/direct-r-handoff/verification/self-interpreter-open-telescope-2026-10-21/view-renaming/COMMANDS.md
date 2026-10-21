# Recursive typed quotation-view renaming

Date: 2026-10-21. Source: `theories/self_interpreter/QuotationViewRenaming.v`,167 lines.
Frozen SHA-256: `6f2ebfa5f7b1cdb93e3b5eaaa95e8a304dcd1c64050e9bbaee4eaa2fa70d35de`.
No Git mutation; coordinator owns shared Dune/Audit/prose.

`rename_view` and `rename_shape` preserve the ENTIRE finite recursive typed
product view, not just its root cache. Inputs are simultaneous source/target
variable renamings, actual original target TypedRen, exact inherited
carrier/decoder compatibility, and a literal realization square. The new
environment is arbitrary; no equality between proof records is required.
The recursive product case reconstructs the actual dependent child context,
lifting both renamings and the realization square. Source syntax and all
target annotations are retained. `weaken_view`/`weaken_shape` supply the
fresh-variable case with actual transpose fill. No source quotation
existence, substitution operation or global coherence theorem is assumed.

## Reproduction

Fresh directories: `/tmp/pts-rk-quotation-view-renaming.R1pU4W` and
`_build/quotation-view-renaming.FsST1j`. RUN.sh/CHECK.sh retain exact commands,
dates, complete output, exit codes, hashes and versions.

```sh
cd /Users/akuklev/air/pts-rk
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
timeout 1200 opam exec -- dune build \
  --build-dir=/tmp/pts-rk-quotation-view-renaming.R1pU4W \
  --display=short --no-buffer -j 2 theories/self_interpreter/QuotationViewRenaming.vo
```

Attempts01/02 exit1: registration pending. An additional dependency-only
build of QuotationCache.vo used the same flags/build directory, output
dependencies.log and dependencies.exit=0. Attempt03 exit1: caught concurrent
QuotationCache realization helper's unresolved k; reported to owner, no
dependency edits. Attempt04 exit1: recursive Fixpoint calls require all
explicit parameters before the function's final Arguments declaration.
Attempt05 exit1: Pi source must be supplied explicitly to rename_certificate
after constructor reduction. Attempt06 exit0: all NINE own reports CLOSED.
No proof weakening, timeout, disk failure or interruption occurred.

```sh
timeout 1200 opam exec -- rocq check -silent -o \
  -Q /tmp/pts-rk-quotation-view-renaming.R1pU4W/default/theories PTSrk \
  -Q /tmp/pts-rk-quotation-view-renaming.R1pU4W/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q /tmp/pts-rk-quotation-view-renaming.R1pU4W/default/theories/self_interpreter PTSrk.SelfInterpreter \
  PTSrk.SelfInterpreter.QuotationViewRenaming
```

Recursive kernel exit0, only unchanged upstream dependent functional
extensionality in loaded inventory; no unsafe fixpoint, assumed positivity
or type-in-type. The nine own theorem reports are separately closed.
Forbidden-declaration scan exit1 (no matches). Independent full-source review
by the contextual field enumeration owner passed at the frozen hash:
recursive constructor views, original typing, exact cache/root recovery,
typed renaming and field compatibility were checked; no proof-record
equality or cache-to-constructor equality was assumed. Fresh aggregate,
pristine comparison and full CI remain later separate gates.

CHECK.sh records git rev-parse HEAD, rocq -v, dune --version, ocamlc -version,
opam --version and opam list --installed --columns=name,version:
Rocq9.2.0, Stdlib9.1.0, Equations1.3.2+9.2, OCaml4.14.2, Dune3.23.1,
opam2.6.1; HEAD e822cd62df393faf4d5e4ed0c4c8fed173ccba6f.
While awaiting registration, rocq compile --help was inspected read-only;
no direct compiler fallback was used.
