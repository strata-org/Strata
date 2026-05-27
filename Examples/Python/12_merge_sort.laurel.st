// Laurel translation of 12_merge_sort.py
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

procedure merge($in_left: (Core Any), $in_right: (Core Any))
  returns (LaurelResult: (Core Any))
  requires Any..isfrom_ListAny($in_left)( summary "(merge requires) Type constraint of left")
  requires Any..isfrom_ListAny($in_right)( summary "(merge requires) Type constraint of right")
  opaque
  ensures Any..isfrom_ListAny(LaurelResult)( summary "(merge ensures) Return type constraint")
  modifies *
{
  var nullcall_ret: (Core Any) := from_None();
  LaurelResult := from_None();
  var left: (Core Any) := $in_left;
  var right: (Core Any) := $in_right;
  var maybe_except: (Core Error) := NoError();
  var out: (Core Any) := <?>;
  var i: (Core Any) := <?>;
  var j: (Core Any) := <?>;
  out := from_ListAny(ListAny_nil());
  i := from_int(0);
  assert Any..isfrom_int(i);
  j := from_int(0);
  assert Any..isfrom_int(j);
  assert !Any..isexception(PAnd(PLt(i, Any_len_to_Any(left)), PLt(j, Any_len_to_Any(right)))) summary "Check PAnd exception";
  {
    while(Any_to_bool(PAnd(PLt(i, Any_len_to_Any(left)), PLt(j, Any_len_to_Any(right))))) {
      assert !Any..isexception(PLe(Any_get(left, i), Any_get(right, j))) summary "Check PLe exception";
      if Any_to_bool(PLe(Any_get(left, i), Any_get(right, j))) then {
        assert !Any..isexception(PAdd(out, from_ListAny(ListAny_cons(Any_get(left, i), ListAny_nil())))) summary "Check PAdd exception";
        out := PAdd(out, from_ListAny(ListAny_cons(Any_get(left, i), ListAny_nil())));
        assert !Any..isexception(PAdd(i, from_int(1))) summary "Check PAdd exception";
        i := PAdd(i, from_int(1));
      }
       else {
        assert !Any..isexception(PAdd(out, from_ListAny(ListAny_cons(Any_get(right, j), ListAny_nil())))) summary "Check PAdd exception";
        out := PAdd(out, from_ListAny(ListAny_cons(Any_get(right, j), ListAny_nil())));
        assert !Any..isexception(PAdd(j, from_int(1))) summary "Check PAdd exception";
        j := PAdd(j, from_int(1));
      };
    }loop_continue_148;
  }loop_break_148;
  assert !Any..isexception(PLt(i, Any_len_to_Any(left))) summary "Check PLt exception";
  {
    while(Any_to_bool(PLt(i, Any_len_to_Any(left)))) {
      assert !Any..isexception(PAdd(out, from_ListAny(ListAny_cons(Any_get(left, i), ListAny_nil())))) summary "Check PAdd exception";
      out := PAdd(out, from_ListAny(ListAny_cons(Any_get(left, i), ListAny_nil())));
      assert !Any..isexception(PAdd(i, from_int(1))) summary "Check PAdd exception";
      i := PAdd(i, from_int(1));
    }loop_continue_351;
  }loop_break_351;
  assert !Any..isexception(PLt(j, Any_len_to_Any(right))) summary "Check PLt exception";
  {
    while(Any_to_bool(PLt(j, Any_len_to_Any(right)))) {
      assert !Any..isexception(PAdd(out, from_ListAny(ListAny_cons(Any_get(right, j), ListAny_nil())))) summary "Check PAdd exception";
      out := PAdd(out, from_ListAny(ListAny_cons(Any_get(right, j), ListAny_nil())));
      assert !Any..isexception(PAdd(j, from_int(1))) summary "Check PAdd exception";
      j := PAdd(j, from_int(1));
    }loop_continue_424;
  }loop_break_424;
  LaurelResult := out;
  exit $body;
}

procedure merge_sort($in_xs: (Core Any))
  returns (LaurelResult: (Core Any))
  requires Any..isfrom_ListAny($in_xs)( summary "(merge_sort requires) Type constraint of xs")
  opaque
  ensures Any..isfrom_ListAny(LaurelResult)( summary "(merge_sort ensures) Return type constraint")
  modifies *
{
  var nullcall_ret: (Core Any) := from_None();
  LaurelResult := from_None();
  var xs: (Core Any) := $in_xs;
  var maybe_except: (Core Error) := NoError();
  var n: (Core Any) := <?>;
  var mid: (Core Any) := <?>;
  var left: (Core Any) := <?>;
  var right: (Core Any) := <?>;
  n := Any_len_to_Any(xs);
  assert Any..isfrom_int(n);
  assert !Any..isexception(PLe(n, from_int(1))) summary "Check PLe exception";
  if Any_to_bool(PLe(n, from_int(1))) then {
    LaurelResult := xs;
    exit $body;
  };
  assert !Any..isexception(PFloorDiv(n, from_int(2))) summary "Check PFloorDiv exception";
  mid := PFloorDiv(n, from_int(2));
  assert Any..isfrom_int(mid);
  left := merge_sort(Any_get_slice(xs, from_Slice(0, OptSome(Any..as_int!(mid)))));
  right := merge_sort(Any_get_slice(xs, from_Slice(Any..as_int!(mid), OptNone())));
  LaurelResult := merge(left, right);
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
  var sorted_xs: (Core Any) := <?>;
  xs := from_ListAny(ListAny_cons(from_int(5), ListAny_cons(from_int(2), ListAny_cons(from_int(8), ListAny_cons(from_int(1), ListAny_cons(from_int(9), ListAny_cons(from_int(3), ListAny_nil())))))));
  sorted_xs := merge_sort(xs);
  assert Any_to_bool(PEq(Any_len_to_Any(sorted_xs), from_int(6))) summary "length preserved";
  assert Any_to_bool(PEq(Any_get(sorted_xs, from_int(0)), from_int(1))) summary "first is 1";
  assert Any_to_bool(PEq(Any_get(sorted_xs, from_int(5)), from_int(9))) summary "last is 9";
}

