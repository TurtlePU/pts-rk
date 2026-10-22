# Shared algebra: incremental compilation evidence

These are direct compilation checks against the existing working-tree
dependencies, not the later fresh aggregate/pristine/kernel audit. No Dune
cache was copied. All times below are UTC on 2026-10-22.

Working directory: `/Users/akuklev/air/pts-rk`.
Raw command, start, end, exit and compiler-output records are retained in
`_build/unified-algebra-2026-10-22`, using the run identifiers below and
suffixes `.command`, `.start`, `.end`, `.exit`, `.log`.

## Commands and final sources

Every compiler invocation used the pinned project environment:

```sh
export PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

The final commands, reproduced from their command records, were:

```sh
opam exec -- rocq compile -q \
  -Q _build/default/theories PTSrk \
  -Q _build/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q _build/default/theories/self_interpreter PTSrk.SelfInterpreter \
  -Q theories/self_interpreter PTSrk.SelfInterpreter \
  -Q /Users/akuklev/air/pts-rk/_build/unified-algebra-2026-10-22 PTSrk.SelfInterpreter \
  -o /Users/akuklev/air/pts-rk/_build/unified-algebra-2026-10-22/Algebra.vo \
  theories/self_interpreter/Algebra.v

opam exec -- rocq compile -q \
  -Q _build/default/theories PTSrk \
  -Q _build/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity \
  -Q _build/default/theories/self_interpreter PTSrk.SelfInterpreter \
  -Q theories/self_interpreter PTSrk.SelfInterpreter \
  -Q /Users/akuklev/air/pts-rk/_build/unified-algebra-2026-10-22 PTSrk.SelfInterpreter \
  -o /Users/akuklev/air/pts-rk/_build/unified-algebra-2026-10-22/UnifiedAlgebra.vo \
  theories/self_interpreter/UnifiedAlgebra.v
```

The original three monolithic attempts omitted the final `-Q` for the
incremental output directory; their `.command` files retain the exact
invocations. No guard, positivity, universe or kernel check was disabled.
The final successful logs retain the ordinary logical-loadpath remapping
warning; the earlier monolithic source also emitted a module-name masking
warning. These are not warning-free-build claims.

Final source SHA-256 values, rechecked after the successful runs:

| Source | SHA-256 |
| --- | --- |
| `theories/self_interpreter/Algebra.v` | `af668dbb663cf77462de201423587c911b00e6fb1650fdcf05f677c0a04443d8` |
| `theories/self_interpreter/UnifiedAlgebra.v` | `803c53cb6d9ccbc58e57217c0c7738d08b142fef872e287899d08edc26ed2f8a` |

## Attempts and revisions

| Run | Time | Exit | Source state and result |
| --- | --- | --- | --- |
| `104635` | 10:46:35–10:47:05 | 1 | Initial monolithic `UnifiedAlgebra`: invalid nested module name `ChurchSyntaxFaithful.ChurchSyntaxFaithful`; corrected to the existing exported theorem. |
| `104724` | 10:47:24–10:47:53 | 1 | After the namespace correction: missing direct `Morphisms` import left `TypedSub` unavailable; added that import. |
| `104813` | 10:48:13–10:48:58 | 0 | Monolithic generic/full-source interface: 24 closed assumption reports. |
| `105123-Algebra` | 10:51:23–10:51:23 | 0 | Extracted the shared generic interface into `Algebra`; added exact ranked/context-telescope spine bridges: 9 closed reports. |
| `105142-UnifiedAlgebra` | 10:51:42–10:52:26 | 0 | Full-source facade now includes the shared interface rather than duplicating it: 17 closed reports. |
| `105310-UnifiedAlgebra` | 10:53:10–10:53:56 | 0 | Added actual head application typing/recovery and open-context reopening: 22 closed reports. |
| `105440-Algebra` | 10:54:40–10:54:41 | 0 | Final shared module, including the executable context-presentation adapter: 13 closed reports. |
| `105501-UnifiedAlgebra` | 10:55:01–10:55:01 | 1 | Shell launch failure: redirection used an unset `compile_log` variable (`No such file or directory`). The compiler did not run; no `.log` was produced. Command/timing/exit records remain. The next invocation corrected only the redirection. |
| `105535-UnifiedAlgebra` | 10:55:35–10:56:21 | 0 | Final facade rebuilt against final `Algebra`: 22 closed reports. |

Intermediate source snapshots were not archived, so the earlier successful
runs are identified by the source changes above, not asserted to match the
final hashes. The two final runs report **13 + 22 closed public assumption
checks**. Scoped whitespace and prohibited-proof-escape scans passed.
No timeout, commit or push occurred in this incremental work.

## Checked boundary

The common fold is an original-PTS application spine over an actual typed
finite-telescope filling. Full-source type/term programs omit the raw HOAS
envelope, and the identity instance has literal recovery and original
typing. Arbitrary nonidentity fillings must supply their own original
typing/coherence witnesses. No full dependent CPS filling is assumed.

Normal-source injectivity is conditional on a common algebra. This does not
replace the legacy arbitrary-source, cross-plan syntax-fidelity theorem:
an intrinsic parser through the actual dependent casts remains open.
These direct builds also do not establish fresh recursive dependency
checking, pristine-assumption agreement or whole-repository CI; consult
the aggregate audit's separate records for those claims.
