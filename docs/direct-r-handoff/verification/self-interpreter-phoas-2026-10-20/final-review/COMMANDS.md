# Independent PHOAS contract review and full CI — 2026-10-20

## Independent review

Read-only review of the frozen finite-package, decoder, telescope, bounded
recovery and local dependent-handler modules found no contract defect.

- `PHOASPackage` binds a finite ground/family/handler context, independent of
  source term size and type shape at fixed budget. The `k+2` families cover
  the boundary pair rank `k+1`; all pairs `a,b <= k` give exactly
  `2*(k+1)^2` polymorphic handler entries. Fallback entries outside the
  relevant ranks supply no typing/recovery premises.
- The actual `fill` supplies every telescope argument. `fill_typed`
  derives an original `TypedSub`; it does not postulate interpreter typing.
  `PHOASTelescope.run_typing` types actual sequential applications directly,
  not by subject expansion from a reduct. Telescope closure checks every
  annotation for normality.
- `PHOASRecovery` uses only ranks up to the computed derivation budget and
  rank pairs with `max(a+1,b) <= k`. Its quantification over simple type
  shapes is discharged by specialization of finitely many polymorphic
  object-language handlers, not by an infinite object-language palette.
- `every_source_quote` starts from independent `ChurchSTLC.has_type` and
  obtains the executable derivation existentially in `Prop`. The executable
  quoter itself consumes independent `Type`-valued source evidence; no
  elimination of target typing evidence into a program is asserted.
- `PHOASDecoder.decoder` is literally `Term nat 0`. Its ground-type lambda
  is inside the decoder body. Actual application recovers the unreduced
  original closed source `lambda o:U_0. t`, without an externally attached
  wrapper. The final bundle requires only independent source evidence and
  its computed budget bound. The executable beta regression checks a
  reducible source, a normal code, and strong recovery of that source.
- The decoder is indexed by **budget k and the full external simple type A**,
  not just by the type's numerical order. No single rank-only polymorphic
  decoder or internal abstraction of the whole type-interpretation family
  is claimed. Package/decoder sort existence is proved, but no new exact
  numeric sort formula is claimed by this checkpoint.
- `DependentPHOAS` proves genuinely dependent local product/constructor
  operations and actual typed identity interpretations, including direct
  typing of the applied dependent handler. Its family
  `B : F_a(A) -> U_b` is supplied, not recursively constructed from arbitrary
  original `B_0 : A -> U_b`. The universe decoder has original sort 1;
  generic conversion coherence for abstract handlers is not assumed.
- `PHOASConversion` rules out a faithful normal map simultaneously acting
  as a conversion-preserving semantic index, even up to pointwise beta
  agreement. Separate syntax and semantic indices escape this limited
  obstruction. It is not a general impossibility of dependent PHOAS.

The final research-note abstract, finite-PHOAS, dependent-handler, shared-map,
status and remaining-goal sections were reviewed against these literal
contracts. The full-simple-type decoder index is explicit; the obsolete
remaining goal about finite STLC closure has been replaced by internalizing
that type interpretation. The abstract and closing status distinguish the
checked strong STLC result from the open full-dependent evaluator. No
remaining mathematical or contract discrepancy was found in these sections.

Reviewed source SHA-256:

```text
13ea13586b288fd8a96a29285a1f1dc160892682506624b51d4c3e9da881387b  theories/self_interpreter/DependentPHOAS.v
0e433a5d40c5b79241704848f55784c5e0a8e8ea1c37e4098e1f426af7efc848  theories/self_interpreter/PHOASTelescope.v
29c3452e4817e387b4f2e82ef50309e4720fb7068d9382cbcb589bc7f787e8c6  theories/self_interpreter/PHOASConversion.v
d5180f6efa44c2a03bafd7712c161a4a2b0045b7ce0fb4e4a94ce6671cc2cb2e  theories/self_interpreter/PHOASAlgebra.v
be380cd2859e255f4202f71316ca5ab5d9cf50ef6a8aaac4b47bac9467ffe073  theories/self_interpreter/PHOASFaithful.v
f921cc8efb66106db5519901b2e5e367db413526d59d29c29e3ba53efd2952e8  theories/self_interpreter/PHOASRecovery.v
8dff8574ecb500e058dcfcfc3159fad559da5fa066febd4a8d898f52a637febf  theories/self_interpreter/PHOASPackage.v
f52518d4b040126a1c02c998404727be789fd350cfe02bf6bc11b6f3580e1576  theories/self_interpreter/PHOASDecoder.v
9ccda979394b526785fd037692c6bb6321cdc8253d608ba0ad069867d58ff194  theories/self_interpreter/Audit.v
```

## Full local CI

Fresh ignored evidence directory:
`_build/self-interpreter-phoas-ci.v3H6S5`.
The literal launcher is retained there as `RUN.sh`:

```sh
export DIRECT_R_LOCAL_HOME=/Users/akuklev/.local/share/pts-rk-ci
export DIRECT_R_LOCAL_SWITCH=pts-rk-ci
export DIRECT_R_LOG_DIR=/Users/akuklev/air/pts-rk/_build/self-interpreter-phoas-ci.v3H6S5/staged
export DIRECT_R_JOBS=2
export DIRECT_R_STAGE_SECONDS=1200
bash /Users/akuklev/air/pts-rk/_build/self-interpreter-phoas-ci.v3H6S5/RUN.sh
```

Result: **PASS**, exit code **0**, 2026-10-20 10:09:59--10:10:35 UTC.
All **226/226** entries in `staged/stages.tsv` are `PASS` with exit code 0;
`staged/result.txt` reports `Last stage: complete`. The starting HEAD was
`73c4303dca2228bb6b3a8ec6ba5099a86da00bb0`, with the reviewed worktree changes.
The frozen source hashes above were captured immediately before execution.
There was no failed or timed-out stage in this final run.

The launcher invokes the unchanged `bash tools/check-local-ci.sh`, including
actionlint, a fresh pristine upstream build and the complete staged driver.
No stage was weakened. Exact commands, timestamps, source hashes, complete
output and exit code are retained in `RUN.sh`, `driver.log`, `exit-code.txt`
and `staged/`; individual stage logs, Dune logs and the pinned switch inventory
are retained by the existing driver. The inventory records Rocq 9.2.0,
Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2, Dune 3.23.1 and opam 2.6.1.
The known physical/logical loadpath-remapping warnings were emitted; there
were no compiler errors.

The parent owns a separate fresh aggregate assumption inventory and recursive
kernel check. This ordinary staged CI run is not described as replaying every
cached `Print Assumptions` command, nor as proving the still-open dependent
interpreter, material BZC reduction or external STLC hardness theorem.
