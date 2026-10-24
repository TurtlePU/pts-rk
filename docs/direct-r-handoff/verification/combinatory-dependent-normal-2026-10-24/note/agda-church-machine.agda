-- S bounds annotated source nodes; every target is a literal original PTS
-- term. The transition table computes ONE greedy pass, not normal answers.
passProgram : (a S r : Nat) → Term 0
passProgram a S r = compileMap r (greedy-state {a = a} {n = 0} {s = S})

applicationProgram : (a S r : Nat) → Term 0
applicationProgram a S r = compileMap2 r (application-state {a = a} {n = 0} {s = S})

reductionProgram : (a d N r : Nat) → Term 0
reductionProgram a d N r = repeatMap r (capacity a 0 (tower d N)) d
  (passProgram a (tower d N) r)

applyReductionProgram : (a d N r : Nat) → Term 0
applyReductionProgram a d N r = lam E (lam (shift E)
  (app (shift (shift (reductionProgram a d N r)))
    (app (app (shift (shift (applicationProgram a S r)))
      (var (fsuc fzero))) (var fzero))))
  where
  S = tower d N
  E = choiceType r (capacity a 0 S)
