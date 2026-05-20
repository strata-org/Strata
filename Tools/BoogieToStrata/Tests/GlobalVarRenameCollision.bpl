const $a.b: int;   axiom $a.b > 0;
var   $a_b: int;   // both sanitize to _a_b
procedure main() returns (r: int)
  modifies $a_b;
{
  $a_b := 1;
  havoc $a_b;
  r := $a.b + $a_b;
}
