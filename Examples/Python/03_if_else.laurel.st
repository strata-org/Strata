// Laurel translation of 03_if_else.py
// (showing only user procedure(s); shared Python runtime prelude omitted)

procedure main()
  returns (LaurelResult: (Core Any))
  opaque
  modifies *
{
  var nullcall_ret: (Core Any) := from_None();
  LaurelResult := from_None();
  var maybe_except: (Core Error) := NoError();
  var flag: (Core Any) := <?>;
  var val: (Core Any) := <?>;
  flag := from_bool(true);
  assert Any..isfrom_bool(flag);
  val := from_int(0);
  assert Any..isfrom_int(val);
  if Any_to_bool(flag) then {
    val := from_int(10);
  }
   else {
    val := from_int(20);
  };
  assert Any_to_bool(PEq(val, from_int(10))) summary "val should be 10";
}

