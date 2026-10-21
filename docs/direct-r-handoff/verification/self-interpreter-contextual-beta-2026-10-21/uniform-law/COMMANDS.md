# Uniform contextual beta law — 21 October 2026

UniformContextualBeta closes TelescopeBetaFamily over the actual generated
domain-parameter telescope. External data are only a rank vector and a,b,d;
the annotations are object-language bound arguments. Its independent identity
program has original typing, full normality and substitution invariance.
The declaration rank is at most k+3 when all vector entries and a,b,d are
at most k. No length bound is needed for that rank inequality. This is not
the recursive full-source quoter or its open-body instantiation theorem.

## Commands and attempts

Pinned Rocq 9.2.0, Stdlib 9.1.0, Equations 1.3.2+9.2, OCaml 4.14.2,
Dune 3.23.1 and opam 2.6.1. Reused root's phase build directory
`/tmp/pts-rk-contextual-beta.Pp1d1l`; all attempts captured in ignored local
`_build/contextual-beta.DU87Uk/uniform-NN.log` and `.exit`.

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- dune build --build-dir=/tmp/pts-rk-contextual-beta.Pp1d1l --display=short --no-buffer theories/self_interpreter/UniformContextualBeta.vo > _build/contextual-beta.DU87Uk/uniform-NN.log 2>&1
status=$?
printf '%s\n' "$status" > _build/contextual-beta.DU87Uk/uniform-NN.exit
tail -n 35 _build/contextual-beta.DU87Uk/uniform-NN.log
exit "$status"
```

| Attempt | Exit | Result |
| --- | --- | --- |
| 01 | 1 | In-progress dependency TelescopeBetaFamily, focused proof error at line182. |
| 02 | 1 | Wrapper rank proof: unqualified app selected the term constructor. Fixed to List.app. |
| 03 | 1 | In-progress UniformTelescopeRecovery suffix proof referenced a removed binder todo. Owner fixed it. |
| 04 | 0 | Five formation/normality/substitution/rank reports closed. |
| 05 | 1 | In-progress TelescopeBetaFamily final identity specialization had an open reflexive goal. Owner fixed it. |
| 06 | 0 | All eight final reports closed, including actual identity typing/normality/replacement. |

The normality proof uses the exact closure iff, including annotations. The
first draft was corrected from the closure boolean equation before that
lemma was compiled. No theorem contract, calculus or check was weakened.

```sh
PATH=/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam opam exec --switch=pts-rk-ci -- rocq check -silent -o -Q /tmp/pts-rk-contextual-beta.Pp1d1l/default/theories PTSrk -Q /tmp/pts-rk-contextual-beta.Pp1d1l/default/theories/NormalizationComplexity PTSrk.NormalizationComplexity -Q /tmp/pts-rk-contextual-beta.Pp1d1l/default/theories/self_interpreter PTSrk.SelfInterpreter PTSrk.SelfInterpreter.UniformContextualBeta > _build/contextual-beta.DU87Uk/uniform-kernel.log 2>&1
```

Recursive kernel exit 0. Loaded inventory contains only the unchanged
upstream dependent functional extensionality, with no type-in-type,
unsafe fixpoints or assumed positivity; all eight theorem reports are closed.
Independent mathematical review passes at final SHA-256
`7f064a58f61e6e59a4f67de23ad1ec4fddf04cec58af7d6e07cdab2984a605a2`.
The final aggregate audit separately checks pristine inventory and stability.
No Git/index mutation or timeout.
