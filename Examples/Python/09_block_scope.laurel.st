// Laurel translation of 09_block_scope.py
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
  var y: (Core Any) := <?>;
  x := from_int(10);
  assert Any..isfrom_int(x);
  assert !Any..isexception(PGt(x, from_int(0))) summary "Check PGt exception";
  if Any_to_bool(PGt(x, from_int(0))) then {
    assert !Any..isexception(PAdd(x, from_int(1))) summary "Check PAdd exception";
    y := PAdd(x, from_int(1));
    assert Any..isfrom_int(y);
    x := y;
  };
  assert Any_to_bool(PEq(x, from_int(11))) summary "x should be 11";
}

