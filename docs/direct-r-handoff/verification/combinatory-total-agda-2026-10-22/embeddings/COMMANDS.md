# Finite typed fragment embeddings

Working directory: `/Users/akuklev/air/pts-rk`.

Both incremental checks used:

```sh
/tmp/pts-rk-agda-2.8.0.MvVO53/agda --safe --no-default-libraries \
  -i /tmp/pts-rk-agda-2.8.0.MvVO53/cubical \
  -i theories/CombinatoryLogic-rk/agda \
  theories/CombinatoryLogic-rk/agda/FragmentEmbeddings.agda
```

The first redirected stdout/stderr to attempt-01.log; the second to
attempt-02.log. Both exit 0 without warnings. The latter adds packing
recovery, the decoded native node bound and reflection of fragment equality
through size inclusions. No failure or timeout occurred.

Only the new FragmentEmbeddings.agda source was edited. No axioms, postulates,
holes, unsafe options or disabled termination/positivity checks were used.
Root performs the separate fresh full-closure audit. Local checks use existing
ordinary interfaces.

Scoped `git diff --check` exits 0.
