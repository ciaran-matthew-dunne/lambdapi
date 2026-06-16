// Fixture for the --proof-state-on-error flag (see tests/json).
// The `fail` tactic raises mid-proof; with the flag, the error carries the
// goal `π A`, without it the message is bare.
constant symbol Prop : TYPE;
builtin "Prop" ≔ Prop;
injective symbol π : Prop → TYPE;
builtin "P" ≔ π;
constant symbol A : Prop;
opaque symbol demo : π A ≔
begin
  fail
end;
