# Normalized dependent substitutions: final safe check

Agda 2.8.0-3d04bac, Cubical v0.9 commit
b150186d2544e7efeddd31e5d14a8b9ecbb100f7. This directory contains copied
sources and isolated Agda configuration/data. Earlier root-agent attempts
are preserved separately at /tmp/pts-rk-normal-sub.JGiC6D; none was erased.

Final command (check04):

```sh
AGDA_DIR=/tmp/pts-rk-normal-sub-finish.pAp4MF/config \
XDG_DATA_HOME=/tmp/pts-rk-normal-sub-finish.pAp4MF/data \
/tmp/pts-rk-agda-2.8.0.MvVO53/agda \
  --safe --ignore-interfaces --no-default-libraries \
  -i /tmp/pts-rk-normal-sub-finish.pAp4MF/source \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  /tmp/pts-rk-normal-sub-finish.pAp4MF/source/NormalizedSubstitution.agda \
  +RTS -M1500m -RTS
```

check04.log, check04.exit.txt, check04.started.txt and check04.finished.txt
record the complete output, exit status and UTC timestamps. All dependencies
are rechecked. final-sources.sha256 records the copied source files.
The final module has 220 lines, SHA256
2e75b31a9935c4e171940113e07a7647158c0935a193d578347b3db6d022f164.

The earlier commands use the same command line, omitting --ignore-interfaces
for check01/check02. Before each command, the matching attemptNN.agda source
snapshot was copied to source/NormalizedSubstitution.agda.

- check01: exit 42, 01:42:12–01:42:22 UTC. The direct nested recursor needed
  an explicit motive for elimination into an equality proposition.
- check02: exit 0, zero warnings, 01:42:42–01:42:57 UTC. All original
  normalization, identity and associativity obligations check.
- check03: exit 0, zero warnings, 01:43:23–01:44:04 UTC. Fresh full dependency
  recheck after adding normalizeSub-reflects.
- check04: exit 0, zero warnings, 01:44:22–01:45:03 UTC. Final fresh full
  dependency recheck after adding only excerpt markers
  BEGINNORMALSUBCARRIER/ENDNORMALSUBCARRIER. The final live-to-copy comparison
  also passes (final-stability.exit.txt = 0).

The fix replaces the library binary recursor's product-equivalence expansion
with two direct applications of its proved rec→Set. Both witness-constancy
conditions are proved; no choice, axiom or typing-proof irrelevance is
assumed. This avoids the earlier typechecking heap blow-up without hiding
definitions or weakening goals.

SubNF stores original native substitution images, their normality, and a
propositionally truncated ORIGINAL TypedSub certificate. Normalizing images
changes their dependent types; sorting of those changed types is obtained
by ORIGINAL subject reduction on substituted lookup terms. The native
typing rules are unchanged. Composition normalizes the ordinary native
composition; literal SubNF identity/associativity paths, retraction and
native-beta coherence/reflection are proved. These equalities are
propositional, not judgmental. The construction is not a dependent IIRT,
normal-type action, comprehension model or QIIRT initiality theorem.

No repository file other than NormalizedSubstitution.agda was changed by
this finishing task. No commit, staging, CI relaxation or safety suppression
was performed.
