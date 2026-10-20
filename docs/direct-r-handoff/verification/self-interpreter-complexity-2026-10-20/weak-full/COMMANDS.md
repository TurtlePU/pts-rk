# Full closed PTS: normalization-assisted weak interpretation

Source: theories/self_interpreter/WeakFullInterpretation.v.
SHA-256: ed2818269d20d89f7f8101fa6a756eaa2b3861c1840517e1cb0e92eb68a3244e.
Working directory: /Users/akuklev/air/pts-rk.
Raw logs and the exact runner remain local in _build/weak-full.T0V7k8.
Fresh initial Dune directory: /tmp/pts-rk-weak-full.Jnl8Pn.

## Commands and attempts

Every attempt used `bash _build/weak-full.T0V7k8/RUN.sh NN`, with NN from
01 through 06. The retained runner sets:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
opam exec -- dune build --build-dir /tmp/pts-rk-weak-full.Jnl8Pn theories/self_interpreter/WeakFullInterpretation.vo
```

Complete stdout/stderr, UTC start time and immediate numeric EXIT status are
in each attempt-NN.log. All failures are preserved; no timeout occurred.

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | Initial package typing: handler renaming rewrite needed an explicit unfolded shift. |
| 02 | 0 | Generic tag/package/selector definitions and original typing compiled. |
| 03 | 1 | Package reduction substitution equality required the symmetric orientation. |
| 04 | 0 | Decoder typing/rank, five-step recovery and normalized-payload typing compiled. |
| 05 | 1 | Faithfulness proof needed explicit source-type parameters A and B. |
| 06 | 0 | Complete public API compiled; eleven closed assumption reports. |

The root agent implemented attempts 01–02. The paper-analysis agent took
exclusive source ownership before attempt 03; no simultaneous edits occurred.
Pinned toolchain is unchanged: Rocq 9.2.0, Stdlib 9.1.0,
Equations 1.3.2+9.2, OCaml 4.14.2, Dune 3.23.1. The preceding complete
HOAS checkpoint retains exact versions/package inventories.

Recursive kernel command (kernel.log and kernel.exit), exit 0:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-weak-full.Jnl8Pn/default/theories PTSrk -Q /tmp/pts-rk-weak-full.Jnl8Pn/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-weak-full.Jnl8Pn/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.WeakFullInterpretation > _build/weak-full.T0V7k8/kernel.log 2>&1
```

No admission or recursion bypass. Loaded-context inventory contains only
the existing upstream functional_extensionality_dep, no unsafe fixpoints,
assumed positivity or type-in-type. All eleven printed new theorem reports
are closed. Source safety scan has no matches (rg exit 1), and scoped
git diff --check exits 0. Parent performs aggregate fresh audit/pristine
comparison/full CI; those are not asserted by these targeted logs.

## Exact contract

`full_closed_weak_interpretation` covers EVERY closed judgment in ORIGINAL
Typing.typ with RankSorts, including dependent terms and reducible annotations.
The program is computed from the supplied raw t and A. Original validity
supplies an existential s with A:U_s; no executable extraction of s from
an erased Prop proof is claimed. No source checker replaces original typing.

The normal package contains BOTH the faithful raw-HOAS tag of t AND the
externally computed nf(t), with nf(A) used in every semantic type annotation.
nf is the actual executable rounds(conservativeRank t)t, whose normality
and original typing follow from the existing proved normalization results.
`quote_typed` and `quote_normal` certify the resulting package;
`quote_indices_injective` and `quote_conversion_injective` recover exact
source syntax and the tag index. At a common original source type,
`quote_conversion_iff` gives the corresponding equivalence.

`decoder_typed` constructs the actual original decoder;
`decoder_type_sort` gives its type rank max(s+3,r+6).
`decode_package_recovers` proves two decoder beta steps followed by three
payload-selector steps. `quote_recovers_nf` returns nf(t), and
`decoded_quote_original_type` retains original type A by allowed beta
conversion. `quote_weak_recovery` proves conversion to t.

This is a WEAK normalization-assisted retraction, not Brown–Palsberg strong
unquotation of the unreduced source, and not evaluation from pure HOAS data.
The internal decoder projects the precomputed payload and ignores the tag;
normalization occurs EXTERNALLY during quotation. The tag supplies fidelity,
not a proof that a parser/reifier was implemented. A dependent strong
HOAS/PHOAS interpreter remains open. These source definitions are frozen;
no commit or push was performed by this subtask.
