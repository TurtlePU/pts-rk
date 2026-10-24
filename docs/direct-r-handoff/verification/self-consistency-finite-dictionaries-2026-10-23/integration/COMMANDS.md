# Dictionary rejection integration — preserved compiler iterations

All four attempts used the same pinned environment:

```sh
export PATH="/Users/akuklev/.local/share/pts-rk-ci/bin:$PATH"
export OPAMROOT=/Users/akuklev/.local/share/pts-rk-ci/opam
export OPAMSWITCH=pts-rk-ci
```

Exact compilation command, replacing N by 1, 2, 3, or 4:

```sh
opam exec -- timeout 300 dune build --build-dir /tmp/pts-rk-fragments-fresh.d7RHpo --display=short --no-buffer -j 2 theories/self_consistency/DictionaryRejection.vo > /tmp/pts-rk-dictionary-integration.rc27Fl/attempt-0N.log 2>&1
```

The caller captured the exit status, printed the final 65 log lines, and exited
with that same status. Explicit statuses are 1, 1, 1, and 0. None timed out.

Attempt 01 failed on conflicting Syntax notation. Attempt 02 failed on
closed-term lifting normalization; the proof was fixed with the existing
lift_closed laws. Attempt 03 exposed a missing explicit Fin type on a binder.
Attempt 04 compiles the final DictionaryRejection source successfully.

This reused prior build directory is incremental evidence only. The separate
fresh integrated audit rebuilt every dependency and recursively checked the
complete closure with pristine inventory comparison.
