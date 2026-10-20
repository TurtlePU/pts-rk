# Actual Church-code application interface

The exact repeated command was, for NN from 01 through 09:

```sh
bash docs/direct-r-handoff/verification/self-interpreter-church-2026-10-20/fold/RUN.sh /tmp/pts-rk-church-fold.WSew8o NN
```

The absolute directory was freshly allocated by
`mktemp -d /tmp/pts-rk-church-fold.XXXXXX`. RUN.sh retains expanded commands,
each attempt's stdout/stderr and numeric status.tsv. No failed attempt was
overwritten. All use the pinned Rocq 9.2.0 switch.

- 01 exits 0: generic numeral/AST renaming and replacement lemmas.
- 02 exits 1: concurrent ChurchSyntax normality proof had an unsimplified
  Boolean conjunction; its owning worker corrected that dependency first.
- 03 exits 1: eight-step reduction elaborated, but final equality retained
  nested shifts and substitutions. Cleanup required the existing syntax
  rewrite library rather than only restricted cbn.
- 04 exits 0: actual run_fold recovery proved in eight original beta steps.
- 05 exits 1: manually expanded seven-product target had an unmatched
  parenthesis. Replaced the brittle expansion with the actual type of the
  original typ_app derivation.
- 06 exits 1: instantiate_typing still had nested renaming/shift equality.
- 07 exits 1: diagnostic Show retained that exact remaining equality.
- 08 exits 1: a second syntax simplification solved type instantiation;
  ordinary destruct of a dependent Fin 0 typing premise then failed.
- 09 exits 0: inversion eliminates that impossible Fin 0 premise. Both
  run_fold and run_typing Print Assumptions reports are closed. No Show,
  temporary proof, admitted goal or unsafe tactic remains.

Source frozen after 09. The final combined fresh build, recursive kernel
check, pristine comparison and full staged CI are recorded one directory
above. No compiler timeout/interruption occurred.
