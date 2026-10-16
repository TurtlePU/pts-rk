Continue the Rocq formalization of the direct interpretation of classical
Tarski–Mostowski–Robinson arithmetic R in the existing PTS-rk repository.
The task is implementation and proof, not another high-level plan.

First read AGENTS.md, docs/direct-r-handoff/HANDOFF.md,
LATEST_DECISIONS.md, STATE.md, MATHEMATICS.md and BUILD.md in that directory,
then the actual split source and sections 1–5 of the included original TeX.
Identify the target by label thm:main and Kernel.Theorem5Target; the conversation
calls it Theorem 5.

Before editing, briefly report the exact target typing judgment, three most
important outstanding proof obligations, and which compiler/CI evidence is
actually present. Inspect git status and preserve all existing user changes.
If the modular source is absent, inspect the archived packages and patch base
and integrate it locally without overwriting work; do not publish anything.

Then obtain a real baseline build in the available toolchain, fix the first
actual compiler error, and continue through dependencies. Once the infrastructure
compiles, implement generic typed telescope/selector/table lemmas and the uniform
bounded-case invariant; finish all-index axiom realization, ground faithfulness,
and preservation of an independently defined first-order deduction system.

No Admitted, new axioms, hidden assumptions of the goal, changed PTS rules,
annotation-erasing bridge, or substitution of native Prop arithmetic for PTS
inhabitants. Finite successful examples do not establish Theorem5Target.
Keep finite observations/internal separation; omit set models. External Bottom
nontriviality and internal self-consistency are distinct and non-blocking here.

Compile after meaningful changes and retain exact commands/logs. If the toolchain
is unavailable, inspect the available CI logs and record that limitation without
claiming verification. Do not install gh or run publish.sh. No push, force-push,
merge or public PR update without authorization.

Maintain docs/direct-r-handoff/STATE.md and DECISIONS.md throughout, recording
what really compiled, the exact next goal, and the next command so a new session
can continue without this chat. Before concluding completion, show the final
unconditional theorem types, fresh successful build, and Print Assumptions.
