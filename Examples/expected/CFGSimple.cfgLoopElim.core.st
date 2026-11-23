program Core;

procedure Max (x : int, y : int, out m : int)
spec {
  ensures [Max_ensures_0]: int.ge(m, x);
  ensures [Max_ensures_1]: int.ge(m, y);
  ensures [Max_ensures_2]: m == x || m == y;
  } cfg entry {
  entry: {
    branch (int.ge(x, y)) goto then_branch else goto else_branch;
  }
  then_branch: {
    m := x;
    goto done;
  }
  else_branch: {
    m := y;
    goto done;
  }
  done: {
    return;
  }
};
procedure CountUp (n : int, out y : int)
spec {
  requires [CountUp_requires_0]: int.ge(n, 0);
  ensures [CountUp_ensures_1]: y == n;
  } cfg entry {
  entry: {
    y := 0;
    goto loopElim_pre_loop;
  }
  loop: {
    branch (int.lt(y, n)) goto body else goto done;
  }
  body: {
    y := int.add(y, 1);
    goto loopElim_back_body_loop;
  }
  done: {
    return;
  }
  loopElim_pre_loop: {
    assert [cfgLoopElimAssert_entry_loop_0]: int.le(y, n);
    assume [$__cfgLoopElimAssume_havoc_loop]: true;
    havoc y;
    assume [$__cfgLoopElimAssume_invariant_loop_0]: int.le(y, n);
    goto loop;
  }
  loopElim_back_body_loop: {
    assert [cfgLoopElimAssert_maintain_loop_body_0]: int.le(y, n);
    assume [$__cfgLoopElimAssume_cut_loop_body]: false;
    return;
  }
};
