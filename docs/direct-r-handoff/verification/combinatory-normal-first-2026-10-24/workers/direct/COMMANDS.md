# Direct SK evaluator worker verification — 2026-10-24

All compiler invocations below use pinned Agda
`/tmp/pts-rk-agda-2.8.0.MvVO53/agda`, Cubical
`/tmp/pts-rk-agda-2.8.0.MvVO53/cubical`, and isolated
`AGDA_DIR=/tmp/pts-rk-sk-direct.pmQ7rC/config`,
`XDG_DATA_HOME=/tmp/pts-rk-sk-direct.pmQ7rC/data`.
The exact compiler invocation for checks 01–05 is:

```sh
AGDA_DIR=/tmp/pts-rk-sk-direct.pmQ7rC/config XDG_DATA_HOME=/tmp/pts-rk-sk-direct.pmQ7rC/data /tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries -i /tmp/pts-rk-sk-direct.pmQ7rC/source -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical /tmp/pts-rk-sk-direct.pmQ7rC/source/TARGET.agda
```

`TARGET` is given below. Each invocation redirected both output streams to
`checkNN.log`; the numeric compiler status was captured immediately, before
printing any log tail. `checkNN-{started,finished,exit}.txt` preserve exact
UTC start/end and numeric exit. These are targeted worker checks, not a
full repository/assumptions/CI audit.

| Check | Target | Exit | Outcome |
| --- | --- | --- | --- |
| 01 | SKDirectGround | 0 | Initial direct soundness and ground canonical evaluator; zero warnings. |
| 02 | SKDirectBoundary | 143 | Terminated own compiler PID 83336 after old reference budget caused approximately 14 GiB RSS; no proof accepted. Memory observation and source snapshots retained. |
| 03 | SKDirectGround | 0 | Added native-to-weak completeness and direct native conversion decision; zero warnings. |
| 04 | SKDirectBoundary | 42 | New cheap rank budget removed memory problem; ordinary unsolved inference metas in `Canonical.coherent _ _` remained. Full failure retained. |
| 05 | SKDirectBoundary | 0 | Explicit operands discharge metas; checked canonical-input nonclosure counterexample; zero warnings. |
| 06 | SKDirectEverything | 0 | Fresh `--ignore-interfaces` aggregate of all three modules and dependencies; zero warnings; 2026-10-24T01:34:03Z–01:34:40Z. |

Before check 04, copied current `SKSourceRank.agda` and `SKSourceNormal.agda`
from the rank worker. The previous source normalizer is retained as
`check02-SKSourceNormal.agda`. Boundary versions used in checks 02 and 04
are retained separately. No previous source was silently retroactively
reclassified as checked. Existing shared Cubical interfaces may have been
reused in these targeted checks.

Final check 06 imports all three new modules through a temporary
`SKDirectEverything.agda` and adds `--ignore-interfaces`:

```sh
AGDA_DIR=/tmp/pts-rk-sk-direct.pmQ7rC/config-final XDG_DATA_HOME=/tmp/pts-rk-sk-direct.pmQ7rC/data-final /tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries --ignore-interfaces -i /tmp/pts-rk-sk-direct.pmQ7rC/source -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical /tmp/pts-rk-sk-direct.pmQ7rC/source/SKDirectEverything.agda
```

`check06.log` and its status/time companions preserve the outcome.
`source.sha256` identifies the copied source inputs before the final check;
`owned-source-after.sha256` identifies the unchanged three owned checkout
sources after it. Tool versions and a safety-marker scan are separate logs.

Scope: weak SK normalization has proved forward original annotated native
beta semantics at every simple type. At ground result type it is exactly
native-beta canonical and gives native conversion decision. The checked
function-result counterexample proves weak application of canonical inputs
does not preserve the canonical image. A general function-output direct
native-beta canonical evaluator, dependent QIIRT integration, and full PTS
coverage are not claimed.
