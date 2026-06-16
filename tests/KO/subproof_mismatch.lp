// Fixture for --proof-state-on-error: a subproof-count mismatch.
// `induction` produces 2 subgoals but no subproofs are given, so the failure
// is detected AFTER the tactic ran — the rich diagnostic shows before+after.
constant symbol Prop : TYPE;
builtin "Prop" ≔ Prop;
injective symbol π : Prop → TYPE;
builtin "P" ≔ π;
inductive N : TYPE ≔ | z : N | succ : N → N;
symbol Q : N → Prop;
opaque symbol demo : Π n, π(Q n) ≔
begin
  induction
end;
