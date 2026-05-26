// Laurel translation of 02_reassign.py
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
  assert !Any..isexception(PAdd(x, from_int(2))) summary "Check PAdd exception";
  x := PAdd(x, from_int(2));
  assert Any_to_bool(PEq(x, from_int(3))) summary "x should be 3";
}

