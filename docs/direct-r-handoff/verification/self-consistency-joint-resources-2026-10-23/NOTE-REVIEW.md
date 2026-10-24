# Streamlined direct roadmap: build and review evidence

The exact build command for each attempt is:

```sh
bash theories/self_consistency/build-note.sh DIRECT_ROADMAP
```

Attempt01, temporary directory /tmp/pts-rk-consistency-note.QQydoK, exited 12.
An amsmath tag command was not supported in the Markdown display. It was
replaced with literal (BS) text. The failed logs and tool versions are kept
under note-01.

Attempt02, /tmp/pts-rk-consistency-note.6anAQL, finished TeX compilation but
failed the build driver's validation with exit 1: the wide Markdown summary
table produced an overfull box of roughly 514pt. The table was replaced by
six concise bullets. The older repository PDF was retained by the failed
driver. Logs are kept under note-02. Its build-exit-code.txt records the
underlying TeX exit 0, not the subsequent failed validation.

Attempt03, /tmp/pts-rk-consistency-note.PWR2gc, passed compilation and validation.
Its logs are preserved under note-03 as an intermediate success. A subsequent
review corrected the displayed ranks to distinguish pointwise predicate ranks
from ranks of whole families; this version is not the final reviewed note.

Attempt04, /tmp/pts-rk-consistency-note.0mBTXO, passed the exact build command
above with exit 0. The final source is 432 lines, versus 1390 before this
revision; the PDF is seven pages, versus 21. Its logs and versions are kept
under note-final, without caches or rendered images.

The root ran the exact inspection commands:

```sh
mkdir -p /tmp/pts-rk-consistency-note.0mBTXO/inspection
swift docs/direct-r-handoff/verification/self-consistency-direct-roadmap-2026-10-22/inspect.swift \
  theories/self_consistency/DIRECT_ROADMAP.pdf \
  /tmp/pts-rk-consistency-note.0mBTXO/inspection
```

Inspection exited 0: seven nonempty pages, seven links, required content and
all-page rendering passed. The root visually reviewed ALL seven rendered
pages and reported no clipped mathematical formulas or text. This records
the root's actual visual review, not a second independent visual review by
the audit worker. A separate worker reviewed the mathematics and claim scope.
The extracted text is preserved in note-final/text.txt.

Final SHA-256 values, independently matched by the audit worker:

- Source: 3599bbcdad1e50ce26aadfc16d6b7a81df127158a2df0f40c76009566b39d5e8.
- PDF: 5aa0f380f8258f7ea137ff3d7fa5bb610c3e6a4716e62de99ff629f068582e33.

The machine-readable manifest is note-final/source.sha256. Final light checks
verified these exact files again at 11:33:41 UTC after handoff documentation
settled; all ten final stages passed.
