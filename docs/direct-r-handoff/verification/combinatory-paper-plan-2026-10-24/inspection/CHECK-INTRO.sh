#!/usr/bin/env bash
set -u
evidence=/Users/akuklev/air/pts-rk/docs/direct-r-handoff/verification/combinatory-paper-plan-2026-10-24/inspection
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$evidence/intro-started.txt"
perl -0777 -e '
  my $text = <>;
  $text =~ s/-\n//g;
  $text =~ s/\s+/ /g;
  my $position = index($text, "1 Introduction and goals");
  die "Missing introduction\n" if $position < 0;
  for my $needle (
    "1. A Church-encodable natural-model QIIRT.",
    "2. A normal-form-first presentation.",
    "3. A cumulative hierarchy of bounded fragments.",
    "4. A Hilbert-style logical theory.",
    "5. Partial finite models and internal bounded soundness.",
    "6. An indexed self-interpreter with source folds.",
    "Development order.",
    "new construction is deferred until this plan is resumed.",
    "1.1 The calculus and its logical reading"
  ) {
    my $found = index($text, $needle, $position);
    die "Missing or reordered introduction text: $needle\n" if $found < 0;
    $position = $found + length($needle);
    print "PASS: $needle\n";
  }
' "$evidence/pdf-text.txt" > "$evidence/intro-check.log" 2>&1
status=$?
printf '%s\n' "$status" > "$evidence/intro-exit-code.txt"
date -u '+%Y-%m-%d %H:%M:%S UTC' > "$evidence/intro-finished.txt"
printf '%s\n' 'bash docs/direct-r-handoff/verification/combinatory-paper-plan-2026-10-24/inspection/CHECK-INTRO.sh' > "$evidence/intro-command.txt"
tail -12 "$evidence/intro-check.log"
exit "$status"
