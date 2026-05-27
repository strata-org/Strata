// Laurel translation of 11_binary_search.py
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

procedure binary_search($in_xs: (Core Any), $in_target: (Core Any))
  returns (LaurelResult: (Core Any))
  requires Any..isfrom_ListAny($in_xs)( summary "(binary_search requires) Type constraint of xs")
  requires Any..isfrom_int($in_target)( summary "(binary_search requires) Type constraint of target")
  opaque
  ensures Any..isfrom_int(LaurelResult)( summary "(binary_search ensures) Return type constraint")
  modifies *
{
  var nullcall_ret: (Core Any) := from_None();
  LaurelResult := from_None();
  var xs: (Core Any) := $in_xs;
  var target: (Core Any) := $in_target;
  var maybe_except: (Core Error) := NoError();
  var lo: (Core Any) := <?>;
  var hi: (Core Any) := <?>;
  var mid: (Core Any) := <?>;
  lo := from_int(0);
  assert Any..isfrom_int(lo);
  assert !Any..isexception(PSub(Any_len_to_Any(xs), from_int(1))) summary "Check PSub exception";
  hi := PSub(Any_len_to_Any(xs), from_int(1));
  assert Any..isfrom_int(hi);
  assert !Any..isexception(PLe(lo, hi)) summary "Check PLe exception";
  {
    while(Any_to_bool(PLe(lo, hi))) {
      assert !Any..isexception(PFloorDiv(PAdd(lo, hi), from_int(2))) summary "Check PFloorDiv exception";
      mid := PFloorDiv(PAdd(lo, hi), from_int(2));
      assert Any..isfrom_int(mid);
      if Any_to_bool(PEq(Any_get(xs, mid), target)) then {
        LaurelResult := mid;
        exit $body;
      };
      assert !Any..isexception(PLt(Any_get(xs, mid), target)) summary "Check PLt exception";
      if Any_to_bool(PLt(Any_get(xs, mid), target)) then {
        assert !Any..isexception(PAdd(mid, from_int(1))) summary "Check PAdd exception";
        lo := PAdd(mid, from_int(1));
      }
       else {
        assert !Any..isexception(PSub(mid, from_int(1))) summary "Check PSub exception";
        hi := PSub(mid, from_int(1));
      };
    }loop_continue_131;
  }loop_break_131;
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
  xs := from_ListAny(ListAny_cons(from_int(1), ListAny_cons(from_int(3), ListAny_cons(from_int(5), ListAny_cons(from_int(7), ListAny_cons(from_int(9), ListAny_cons(from_int(11), ListAny_cons(from_int(13), ListAny_nil()))))))));
  found := binary_search(xs, from_int(7));
  assert Any..isfrom_int(found);
  assert Any_to_bool(PEq(found, from_int(3))) summary "7 is at index 3";
  missing := binary_search(xs, from_int(4));
  assert Any..isfrom_int(missing);
  assert !Any..isexception(PNeg(from_int(1))) summary "Check PNeg exception";
  assert Any_to_bool(PEq(missing, PNeg(from_int(1)))) summary "4 is not present";
}

