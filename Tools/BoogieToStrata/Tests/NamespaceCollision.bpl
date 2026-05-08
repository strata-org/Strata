// Minimal reproduction: namespace collision bug in BoogieToStrata.
// Boogie allows a constant and procedure to share the same name
// because they live in separate namespaces. BoogieToStrata emits
// both into Strata Core's single namespace, causing:
//   "a declaration of this name already exists"

type ref = int;

const main: ref;
axiom (main == 1000);

var x: int;

procedure main()
  modifies x;
{
  x := 42;
  assert x == 42;
  // Use the constant so it isn't pruned
  assert main == 1000;
}
