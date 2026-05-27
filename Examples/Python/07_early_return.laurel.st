// Laurel translation of 07_early_return.py
// (showing only user procedure(s); shared Python runtime prelude omitted)

procedure abs_value($in_x: (Core Any))
  returns (LaurelResult: (Core Any))
  requires Any..isfrom_int($in_x)( summary "(abs_value requires) Type constraint of x")
  opaque
  ensures Any..isfrom_int(LaurelResult)( summary "(abs_value ensures) Return type constraint")
  modifies *
{
  var nullcall_ret: (Core Any) := from_None();
  LaurelResult := from_None();
  var x: (Core Any) := $in_x;
  var maybe_except: (Core Error) := NoError();
  assert !Any..isexception(PLt(x, from_int(0))) summary "Check PLt exception";
  if Any_to_bool(PLt(x, from_int(0))) then {
    assert !Any..isexception(PNeg(x)) summary "Check PNeg exception";
    LaurelResult := PNeg(x);
    exit $body;
  };
  LaurelResult := x;
  exit $body;
}

procedure main()
  returns (LaurelResult: (Core Any))
  opaque
  modifies *
{
  var nullcall_ret: (Core Any) := from_None();
  LaurelResult := from_None();
  var maybe_except: (Core Error) := NoError();
  var a: (Core Any) := <?>;
  assert !Any..isexception(PNeg(from_int(7))) summary "Check PNeg exception";
  a := abs_value(PNeg(from_int(7)));
  assert Any..isfrom_int(a);
  assert Any_to_bool(PEq(a, from_int(7))) summary "abs(-7) should be 7";
}

