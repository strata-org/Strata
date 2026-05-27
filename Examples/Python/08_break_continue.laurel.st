// Laurel translation of 08_break_continue.py
// (showing only user procedure(s); shared Python runtime prelude omitted)

procedure main()
  returns (LaurelResult: (Core Any))
  opaque
  modifies *
{
  var nullcall_ret: (Core Any) := from_None();
  LaurelResult := from_None();
  var maybe_except: (Core Error) := NoError();
  var i: (Core Any) := <?>;
  var seen: (Core Any) := <?>;
  i := from_int(0);
  assert Any..isfrom_int(i);
  seen := from_int(0);
  assert Any..isfrom_int(seen);
  assert !Any..isexception(PLt(i, from_int(10))) summary "Check PLt exception";
  {
    while(Any_to_bool(PLt(i, from_int(10)))) {
      assert !Any..isexception(PAdd(i, from_int(1))) summary "Check PAdd exception";
      i := PAdd(i, from_int(1));
      if Any_to_bool(PEq(i, from_int(3))) then {
        exit loop_continue_55;
      };
      if Any_to_bool(PEq(i, from_int(6))) then {
        exit loop_break_55;
      };
      assert !Any..isexception(PAdd(seen, from_int(1))) summary "Check PAdd exception";
      seen := PAdd(seen, from_int(1));
    }loop_continue_55;
  }loop_break_55;
  assert Any_to_bool(PEq(seen, from_int(4))) summary "should have counted 1,2,4,5";
}

