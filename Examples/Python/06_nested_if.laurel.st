// Laurel translation of 06_nested_if.py
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
  var label: (Core Any) := <?>;
  x := from_int(5);
  assert Any..isfrom_int(x);
  label := from_int(0);
  assert Any..isfrom_int(label);
  assert !Any..isexception(PGt(x, from_int(0))) summary "Check PGt exception";
  if Any_to_bool(PGt(x, from_int(0))) then {
    assert !Any..isexception(PLt(x, from_int(10))) summary "Check PLt exception";
    if Any_to_bool(PLt(x, from_int(10))) then {
      label := from_int(1);
    }
     else {
      label := from_int(2);
    };
  }
   else {
    label := from_int(3);
  };
  assert Any_to_bool(PEq(label, from_int(1))) summary "label should be 1";
}

