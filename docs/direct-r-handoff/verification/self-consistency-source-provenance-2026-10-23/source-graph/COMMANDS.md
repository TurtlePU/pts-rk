# Native checker source graph: isolated checks

Only the new repository source
`theories/self_consistency/CheckerSourceGraph.v` was changed by this worker.
No older proof, Dune registration, audit registration, index or documentation
was edited. No objects or caches were written to the repository.

Working directory: `/Users/akuklev/air/pts-rk`.
Worker directory: `/tmp/pts-rk-source-graph.Ovrq0T`.
Reused dependency objects:
`/tmp/pts-rk-joint-resources-fresh.TqBIPV/default/theories`.
These isolated checks are not the fresh integrated dependency/kernel audit.

All wrappers set:

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Exact invocations:

```sh
bash /tmp/pts-rk-source-graph.Ovrq0T/CHECK.sh attempt-01
bash /tmp/pts-rk-source-graph.Ovrq0T/CHECK.sh attempt-02
bash /tmp/pts-rk-source-graph.Ovrq0T/REPORT.sh
```

CHECK.sh records each fully resolved command, UTC start/end, source SHA-256,
exit status and unfiltered output. Attempt01 exits1: one sort comparison
operand lacked its explicit native scope index, so encode_term could not
infer that index. Attempt02 fixes only that annotation and exits0 (0.23s).
No timeout or proof-kernel failure occurred. Report exits0 (0.45s), with all
35 public endpoint reports closed. Full recursive kernel verification is
reserved for the fresh integrated audit.

Final source SHA-256:
`86fbf8c6e10f5f2345d463f758dec595b283bf700a89954ed04139b53ddeec85`.
Rocq reports version9.2 compiled with OCaml4.14.2.

The source relations use independent constructor-by-constructor premises,
never checker/evaluator agreement, acceptance, or native typing. Local fields
expose original substitution and comparison-operand provenance. The source
graphs cover all six certificate rules, beta/equality fields, contexts,
malformed inputs and both Boolean outputs. The rejected self-comparison
counterexample cannot carry the source graph.

These are NATIVE Rocq graphs and external compiler correspondence. Context
indexing, original substitution, decoding and encoding remain native. No
internal raw-code checker, internal graph evidence, arbitrary Church-value
reflection or internal finite-fragment soundness is claimed.
