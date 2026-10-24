# SK binder-free migration worker verification

Owned exactly the six BinderFree*.agda project modules. Final source hashes
are in final-source.sha256; immutable source copies are under source/.
No paper, docs, build registration, Git index or commits were edited.

Compiler: Agda 2.8.0-3d04bac. Cubical revision
b150186d2544e7efeddd31e5d14a8b9ecbb100f7.

All checking used the compiler /tmp/pts-rk-agda-2.8.0.MvVO53/agda,
AGDA_DIR=/tmp/pts-rk-sk-binderfree.tCrz00/config,
XDG_DATA_HOME=/tmp/pts-rk-sk-binderfree.tCrz00/data and include paths
/tmp/pts-rk-sk-binderfree.tCrz00/source and
/tmp/pts-rk-agda-2.8.0.MvVO53/cubical.

Checks, in chronological order:

- core-01.log: --no-libraries BinderFreeCore.agda, exit 42. This incorrectly
  disables Cubical's library-local flags, producing InfectiveImport. No
  source change was needed to resolve it.
- core-02.log: --safe --no-default-libraries BinderFreeCore.agda, exit 0.
- quotient-01.log: same flags BinderFreeQuotient.agda, exit 0. Checks the
  Core/Coherence/Equality/Bidirectional closure as well.
- boundary-01.log: same flags BinderFreeBoundary.agda, exit 42. Local
  identity-normal name collided with imported BoundedReduction declaration;
  renamed to identity-nf. Added needed Nat imports while waiting on this
  check; no other proof diagnostic was hidden.
- boundary-02.log: same flags BinderFreeBoundary.agda, exit 0.
- boundary-03.log: same flags BinderFreeBoundary.agda after adding the
  eta-sensitive counterexample, exit 0.
- final-check.log: --safe --no-default-libraries --ignore-interfaces
  SKBinderFreeCheck.agda, exit 0. This temporary aggregate imports all six
  final modules. Started/finished timestamps and exit code are preserved in
  final-started.txt, final-finished.txt, final-exit-code.txt. No warnings.

Final exact command:

```sh
AGDA_DIR=/tmp/pts-rk-sk-binderfree.tCrz00/config XDG_DATA_HOME=/tmp/pts-rk-sk-binderfree.tCrz00/data /tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries --ignore-interfaces -i /tmp/pts-rk-sk-binderfree.tCrz00/source -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical /tmp/pts-rk-sk-binderfree.tCrz00/source/SKBinderFreeCheck.agda
```

git diff --check for all six files passes. Final source stability check
`shasum -a 256 -c final-source.sha256` passes. No postulates, termination,
positivity or universe-check disabling and no warning suppression were added.

The six modules total 1,021 source lines. New native bridge expand-typed
covers every intrinsic SK.Tm A in every native context at decode A, with
ground labels interpreted by original universes. Weak normalization remains
distinct from native beta normalization; the source checks both the extra
native-beta identity and failure of eta as a repair.
