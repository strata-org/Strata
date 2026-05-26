// Laurel translation of 05_procedure_call.py
// (showing only user procedure(s); shared Python runtime prelude omitted)

procedure add_one($in_x: (Core Any))
  returns (LaurelResult: (Core Any))
  requires Any..isfrom_int($in_x)( summary "(add_one requires) Type constraint of x")
  opaque
  ensures Any..isfrom_int(LaurelResult)( summary "(add_one ensures) Return type constraint")
  modifies *
{
  var nullcall_ret: (Core Any) := from_None();
  LaurelResult := from_None();
  var x: (Core Any) := $in_x;
  var maybe_except: (Core Error) := NoError();
  assert !Any..isexception(PAdd(x, from_int(1))) summary "Check PAdd exception";
  LaurelResult := PAdd(x, from_int(1));
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
  var y: (Core Any) := <?>;
  y := add_one(from_int(4));
  assert Any..isfrom_int(y);
  assert Any_to_bool(PEq(y, from_int(5))) summary "y should be 5";
}

