# Actual checked-layer code alignment

Source: theories/self_interpreter/LayerCodeAlignment.v (228 lines).
SHA-256: 8b0344e7e555a29ef98cfc60259b5ece0673397ff594b70f161a3722f87ca81b.
Before authorized alias-only cleanup: 241 lines,
f046d10188390f93dc1428358917f9dca0f57a8b7cd62dd7daa992ba9cd58edf.
Working directory: /Users/akuklev/air/pts-rk.
Raw evidence: _build/layer-code-alignment.yQnSnR.
Dune directory: /tmp/pts-rk-checked-contextual.vLMi7j (same-phase reuse;
this new module had no prior compiled output).

All attempts used `bash _build/layer-code-alignment.yQnSnR/RUN.sh NN`:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-checked-contextual.vLMi7j --display=short --no-buffer theories/self_interpreter/LayerCodeAlignment.vo
```

- 01: exit 1, deliberately interrupted the compiler while elaborating the large GlobalEqualityInsertion module alias; used its fully qualified theorem instead. The raw log retains `User interrupt` at the alias.
- 02: exit 1, overlapping invocation encountered the still-active Dune lock from 01; no proof was checked by this invocation.
- 03: exit 1, the raw lifted-term definition needed an explicit `Term nat` parameter annotation.
- 04: exit 1, the telescope substitution square required rewriting the identity rename before applying the literal fill theorem; direct rewriting did not match the folded wrappers.
- 05: exit 0, first frozen source, eighteen distinct closed assumption reports.
- 06: exit 0, final frozen source after mechanically expanding the thirteen exported module aliases to fully qualified references. Eighteen unchanged closed reports; compiled object is now 32 KiB. Exact nested-alias consumer scan returned no matches before the cleanup. Definitions, statements and proof steps are otherwise unchanged.

All attempt logs and exit files are retained. No timeout, admission, new axiom,
unsafe cast, disabled guard/universe check or Git mutation. Scoped
`git diff --check -- theories/self_interpreter/LayerCodeAlignment.v` exits 0.

The authorized representation-only cleanup used this mechanical command,
after a read-only search confirmed no consumers of the removed aliases:

```sh
perl -0pi -e 's/^Module (\w+) := ([A-Za-z0-9_.]+)\.\n/$aliases{$1}=$2; ""/gme; for my $alias (keys %aliases) { s/\b\Q$alias\E\./$aliases{$alias}./g; }' theories/self_interpreter/LayerCodeAlignment.v
```

The earlier recursive evidence is preserved as kernel-before-alias.log/exit;
kernel.log/exit is the post-cleanup rerun of the identical command below.

Recursive command (`CHECK.sh`):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam OPAMSWITCH=pts-rk-ci opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories PTSrk -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-checked-contextual.vLMi7j/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.LayerCodeAlignment
```

kernel.log/kernel.exit: exit 0. The loaded inventory contains only unchanged
upstream dependent functional extensionality; no type-in-type, unsafe
fixpoints or assumed positivity. All own reports are closed.
Aggregate/pristine verification is separate.

Version command (versions.log/exit, exit 0):

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam list --switch=pts-rk-ci --installed --columns=name,version --short rocq-core rocq-stdlib rocq-equations ocaml dune
```

Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1.

`allocate_codes` computes the actual checked slot in a complete numeric-budget
layer from independently originally typed normal endpoints and their actual
filled conversion. It does not consume an equality oracle or successful-quoter
premise. The dependent `unpack_pack` equality preserves the literal contextual
identity witness, including the normalizer's actual context. Inherited typed
renaming and the literal lookup/fill square preserve the same source context.
The actual neutral field application supplies an original typed transport;
normal motive and payload give a normal aligned term. Applying the real closed
identity fill erases this transport to the literal old filled payload, not its
normal form. The module does not yet prove recursive all-source quotation.

Independent full-source read-only review by the audit agent: PASS. In
particular, original typing, actual allocation, normality guards and literal
payload recovery were checked separately.
