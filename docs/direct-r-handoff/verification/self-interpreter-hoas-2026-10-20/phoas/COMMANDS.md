# Brown--Palsberg single-family obstruction and indexed components

Working directory: `/Users/akuklev/air/pts-rk`.
Fresh build directory: `/tmp/pts-rk-brown-palsberg.KOiQg5/build`.
The implementing agent confirmed this exact command for each attempt,
with `NN` replaced by its two-digit number:

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-brown-palsberg.KOiQg5/build --display=short --no-buffer theories/self_interpreter/BrownPalsberg.vo > docs/direct-r-handoff/verification/self-interpreter-hoas-2026-10-20/phoas/attempt-NN.log 2>&1
```

The shell immediately captured `$?` in `build_status`, wrote its value to
the matching `.exit` file, displayed the log tail, and exited with that
status. Exact failures remain in the logs; no timeout was reported.

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | Tactic continued after its goal was already solved. |
| 02 | 1 | Nonexistent `rtc_Π` helper. |
| 03 | 1 | Reduction-congruence implicit argument mismatch. |
| 04 | 1 | Same reduction-congruence implicit argument mismatch. |
| 05 | 0 | Initial single-family obstruction and type translation compiled. |
| 06 | 1 | Application typing needed the explicit substitution equality. |
| 07 | 1 | Nonconvertible intermediate typing expression. |
| 08 | 1 | Polymorphic `var` passed without required instantiation. |
| 09 | 0 | Expanded indexed-handler development compiled. |
| 10 | 1 | Residual substitution/renaming in handler specialization. |
| 11 | 1 | Application-congruence arguments omitted. |
| 12 | 0 | Closed indexed identity handlers and their recovery compiled. |
| 13 | 1 | Hypothesis-name collision in finite-palette proof. |
| 14 | 0 | Final module, including finite-rank dependence; 18 closed reports. |

The module proves that the literal single family `F : U_a -> U_b` cannot
both support the nested arrow occurrence `F (F A -> F B)` and admit identity
specialization at the same family type. It also constructs separate indexed
STLC type interpretations and actual original-typed identity Abs/App
handlers. It does not claim a completed term-quotation package or a full
dependent self-interpreter. `TypedHOAS.v` is a distinct follow-on module.

The pinned toolchain is shared with the sibling HOAS build; exact version
output and installed-package inventory are retained in `../hoas/versions.log`
and `../hoas/packages.log`: Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2,
OCaml 4.14.2, Dune 3.23.1. The parent task handles the aggregate fresh audit
and recursive kernel check; these per-module logs do not claim either.
