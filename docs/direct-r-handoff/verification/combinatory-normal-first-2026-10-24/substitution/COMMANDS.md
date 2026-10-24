# Normalized substitution verification archive

The final 220-line NormalizedSubstitution.agda passes a fresh safe Cubical
Agda dependency check, with no warnings, under a 1500 MiB heap cap. The
original native typing rules are unchanged. Literal SubNF identity and
associativity paths, normalization retraction, and native-beta
coherence/reflection are checked, not assumed.

This archive retains all eight attempts, including the interrupted and
heap-exhausted diagnostics. It excludes Agda interfaces, configuration/data
caches, and full copied dependency trees. Raw logs retain their original
absolute paths. SOURCE-SNAPSHOTS.sha256 hashes the seven preserved source
snapshots; ARTIFACTS.sha256 hashes the archive contents except itself.

## Final worker commands and result

The exact final command and scope are recorded in [final/COMMANDS.md](final/COMMANDS.md).
The pinned toolchain is Agda 2.8.0-3d04bac and Cubical v0.9 at
b150186d2544e7efeddd31e5d14a8b9ecbb100f7; the version/commit outputs are
recorded alongside this ledger. The final command is:

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

Checks 01/02 use the same command without --ignore-interfaces. Each
attemptNN.agda is the exact source copied to the command's input path for
that attempt. Checks 03/04 recheck all dependency interfaces. The final
live-to-copy comparison exits 0. Final source SHA256:
2e75b31a9935c4e171940113e07a7647158c0935a193d578347b3db6d022f164.

All times below are UTC on 2026-10-24.

| Worker attempt | Start | Finish | Exit | Result |
| --- | --- | --- | --- | --- |
| 01 | 01:42:12 | 01:42:22 | 42 | Missing explicit motive in nested truncation elimination |
| 02 | 01:42:42 | 01:42:57 | 0 | Safe, zero warnings; category laws checked |
| 03 | 01:43:23 | 01:44:04 | 0 | Fresh safe check including reflection |
| 04 | 01:44:22 | 01:45:03 | 0 | Final fresh safe check including excerpt markers |

The fix uses two point-computing rec→Set eliminations rather than the
library rec2→Set's product-equivalence expansion. Weak constancy is proved
from native normalization coherence; no typing-proof irrelevance, choice,
new axiom, or weakened theorem is used. The final laws are propositional
equalities, not judgmental equations. This is not a complete dependent
normal-form-first syntax, comprehension structure, or QIIRT initiality proof.

## Root-agent diagnostic attempts

Raw artifacts are in root-diagnostics. The source shared by checks 03/04
is preserved as attempt03-04.agda with SHA256
7a918b366987a1590f6dbd41da452009ffd8ddfcc0a017802703a48b6d52670f.
attempt01.agda and attempt02.agda are the original retained earlier snapshots.

| Root attempt | Start | Finish | Exit | Result |
| --- | --- | --- | --- | --- |
| 01 | 01:31:24 | 01:31:56 | 42 | Context metavariables; diagnostics preserved |
| 02 | 01:34:12 | 01:34:19 | 42 | Remaining context metavariables; diagnostics preserved |
| 03 | 01:36:26 | 01:38:41 | 143 | Interrupted after excessive memory use |
| 04 | 01:38:41 | 01:40:25 | 251 | Heap exhausted at 2048 MiB cap |

check03.resources.txt preserves the observed process arguments and an RSS
sample of 17,773,088 KiB after 2 minutes 15 seconds. That file records:

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i /tmp/pts-rk-normal-sub.JGiC6D/source \
  /tmp/pts-rk-normal-sub.JGiC6D/source/NormalizedSubstitution.agda
```

Evidence limitation: the complete shell commands and environment assignments
for the root attempts were not separately retained. Their exact spelling is
therefore not reconstructed here. The root agent reports that check04 used
the same safe check with a +RTS -M2G heap cap and tc.decl:10 verbosity; the
raw log independently records heap exhaustion at 2147483648 bytes. The
binary is a non-debug build, whose --verbose option does not emit the
requested declaration trace. Unlike these early diagnostics, all worker
commands and the final successful source are recorded exactly above.

No build failure was discarded or relabeled as verification. This evidence
archiving operation makes no source changes and creates no commit.
