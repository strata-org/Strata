// Test pipe-delimited identifiers in Boogie
program PipeIdentifiers;

// Test basic pipe-delimited identifier as variable name
var |special-name| : int;
var |name with spaces| : int;
var |name@with#special$chars| : int;
var |123numeric| : int;

// Test regular identifier (should still work)
var regularName : int;

procedure TestPipeIdentifiers()
{
  // Test assignment to pipe-delimited identifier
  |special-name| := 42;
  |name with spaces| := 10;
  |name@with#special$chars| := 5;
  |123numeric| := 99;
  
  // Test regular identifier
  regularName := 7;
  
  // Test that || operator works correctly (not confused with pipe identifiers)
  assert regularName == 7 || |special-name| == 42;
  
  // Test using pipe-delimited identifiers in expressions
  assert |special-name| + |name with spaces| == 52;
}
