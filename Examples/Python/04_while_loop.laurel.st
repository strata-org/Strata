// Laurel translation of 04_while_loop.py
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
  i := from_int(0);
  assert Any..isfrom_int(i);
  assert !Any..isexception(PLt(i, from_int(3))) summary "Check PLt exception";
  {
    while(Any_to_bool(PLt(i, from_int(3)))) {
      assert !Any..isexception(PAdd(i, from_int(1))) summary "Check PAdd exception";
      i := PAdd(i, from_int(1));
    }loop_continue_37;
  }loop_break_37;
  assert Any_to_bool(PEq(i, from_int(3))) summary "i should be 3";
}

