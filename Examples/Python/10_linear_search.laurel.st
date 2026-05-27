// Laurel translation of 10_linear_search.py
// (showing only user procedure(s); shared Python runtime prelude omitted)

procedure List_len_pos(l: ListAny)
  invokeOn List_len(l)
  opaque
  ensures List_len(l) >= 0;

procedure List_take_len(l: ListAny, i: int)
  invokeOn List_len(List_take(l, i))
  opaque
  ensures i >= 0 && i <= List_len(l) ==> List_len(List_take(l, i)) == i;

procedure List_drop_len(l: ListAny, i: int)
  invokeOn List_len(List_drop(l, i))
  opaque
  ensures i >= 0 && i <= List_len(l) ==> List_len(List_drop(l, i)) == List_len(l) - i;

procedure Any_len_pos(v: Any)
  invokeOn Any_len(v)
  opaque
  ensures Any_len(v) >= 0;

procedure linear_search($in_xs: (Core Any), $in_target: (Core Any))
  returns (LaurelResult: (Core Any))
  requires Any..isfrom_ListAny($in_xs)( summary "(linear_search requires) Type constraint of xs")
  requires Any..isfrom_int($in_target)( summary "(linear_search requires) Type constraint of target")
  opaque
  ensures Any..isfrom_int(LaurelResult)( summary "(linear_search ensures) Return type constraint")
  modifies *
{
  var nullcall_ret: (Core Any) := from_None();
  LaurelResult := from_None();
  var xs: (Core Any) := $in_xs;
  var target: (Core Any) := $in_target;
  var maybe_except: (Core Error) := NoError();
  var i: (Core Any) := <?>;
  var n: (Core Any) := <?>;
  i := from_int(0);
  assert Any..isfrom_int(i);
  n := Any_len_to_Any(xs);
  assert Any..isfrom_int(n);
  assert !Any..isexception(PLt(i, n)) summary "Check PLt exception";
  {
    while(Any_to_bool(PLt(i, n))) {
      if Any_to_bool(PEq(Any_get(xs, i), target)) then {
        LaurelResult := i;
        exit $body;
      };
      assert !Any..isexception(PAdd(i, from_int(1))) summary "Check PAdd exception";
      i := PAdd(i, from_int(1));
    }loop_continue_125;
  }loop_break_125;
  assert !Any..isexception(PNeg(from_int(1))) summary "Check PNeg exception";
  LaurelResult := PNeg(from_int(1));
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
  var xs: (Core Any) := <?>;
  var found: (Core Any) := <?>;
  var missing: (Core Any) := <?>;
  xs := from_ListAny(ListAny_cons(from_int(10), ListAny_cons(from_int(20), ListAny_cons(from_int(30), ListAny_cons(from_int(40), ListAny_cons(from_int(50), ListAny_nil()))))));
  found := linear_search(xs, from_int(30));
  assert Any..isfrom_int(found);
  assert Any_to_bool(PEq(found, from_int(2))) summary "30 is at index 2";
  missing := linear_search(xs, from_int(99));
  assert Any..isfrom_int(missing);
  assert !Any..isexception(PNeg(from_int(1))) summary "Check PNeg exception";
  assert Any_to_bool(PEq(missing, PNeg(from_int(1)))) summary "99 is not present";
}

