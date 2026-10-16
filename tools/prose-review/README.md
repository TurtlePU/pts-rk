# Protected prose review

Repository-local snapshot of the `prose-review` add-on maintained in the
sibling Markdown package's `addons/prose-review`. The original add-on remains
there; this copy makes the saved PTS-rk review workflow available from Git
without that checkout. Read [SKILL.md](SKILL.md) and the linked service
workflow before cloud use. No browser profile or credentials are included.

Prepare protected, unwrapped prose, collect actual service outputs using the
documented adapters, then merge immutable provider results. Before publication,
inventory authors/cited people and mathematical vocabulary and inspect all
retained edits. Render BOTH services through the same filtering gate:

```sh
python3 tools/prose-review/scripts/review.py render \
  --source latex/PTS-rk.tex --results COMBINED.json \
  --names tools/grazie/protected-names.txt \
  --terms tools/grazie/protected-terms.txt \
  --output latex/WORDING_SUGGESTIONS.md
python3 -m unittest discover -s tools/prose-review/tests
```

The report is for discussion, not automatic application. Name identity changes
and terminology rewrites are rejected as whole proposals; punctuation around
unchanged names can remain. Oxford spelling and protected math/macros/code are
preserved. The audit records rejection categories; raw results are unchanged.
Finite inventories are not a substitute for inspecting final CriticMarkup:
extend them and rerender when another technical false positive is found.

Cloud collection may be partial; the report must retain its real coverage
statement, and IDE-local checks must not be labelled cloud. User review
decisions must not be overwritten by regenerating an edited report.

When explicitly authorized to implement minor changes, `scripts/split_minor.py`
emits an inspectable patch separating independent comma/article edits from
remaining wording. It resolves duplicate edits once and leaves non-minor
rewrites pending, rebased to the edited source. Review conflicting alternatives
before applying its patch. It refuses to overwrite an existing checked minor
report. `restore_minor` verifies every checked excerpt and edit category for
the splitting workflow. The paper checker compares source content directly
and does not depend on generated review reports.
