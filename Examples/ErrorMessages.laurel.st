-- Example demonstrating error messages on requires, ensures, and assert clauses.
-- Error messages are stored in metadata and surfaced in verification output.

procedure divide(x: int, y: int)
returns (result: int)
requires y != 0 errorMessage "divisor must be non-zero"
{
  assert y != 0 errorMessage "divisor is zero at call site";
  return x;
};

procedure checkPositive(n: int)
returns (ok: bool)
requires n >= 0 errorMessage "input must be non-negative"
{
  assert n >= 0 errorMessage "n became negative";
  return true;
};
