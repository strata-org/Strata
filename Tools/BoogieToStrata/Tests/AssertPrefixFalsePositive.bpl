// {:smack}
// Regression test: procedures starting with "assert_" but NOT matching
// SMACK's assert_.TYPE pattern should NOT get a synthetic requires.
// Only assert_.<type> (literal dot) is the SMACK pattern.

procedure assert_helper(p: int) returns (r: int);

procedure main() returns (r: int)
{
  // assert_helper is a normal procedure, passing 0 should be fine
  call r := assert_helper(0);
}
