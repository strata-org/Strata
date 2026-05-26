// Laurel translation of 01_assign_assert.py
// (showing only user procedure(s); shared Python runtime prelude omitted)

procedure main()
  returns (LaurelResult: (Core Any))
  opaque
  modifies *
{
  var nullcall_ret: (Core Any) := from_None();
  LaurelResult := from_None();
  var maybe_except: (Core Error) := NoError();
  var x: (Core Any) := <?>;
  x := from_int(1);
  assert Any..isfrom_int(x);
  assert Any_to_bool(PEq(x, from_int(1))) summary "x should be 1";
}

