program Core;

// Loop-free, call-free unstructured (CFG) procedure bodies. These are
// accepted by the passification VC generator (`--vcgen uwp` / `usp`).

// A diamond: branch on x >= y, join at `done`.
procedure Max(x : int, y : int, out m : int)
spec {
  ensures [max_ge_x]: (int.ge(m, x));
  ensures [max_ge_y]: (int.ge(m, y));
  ensures [max_is_arg]: (m == x || m == y);
}
cfg entry {
  entry: {
    branch (int.ge(x, y)) goto then_branch else goto else_branch;
  }
  then_branch: {
    m := x;
    goto done;
  }
  else_branch: {
    m := y;
    assert [else_m_gt_x]: (int.gt(m, x));
    goto done;
  }
  done: {
    return;
  }
};

// Two successive branches with three paths into the final join, plus a
// precondition used by an intermediate assertion.
procedure Clamp(lo : int, hi : int, x : int, out r : int)
spec {
  requires [lo_le_hi]: (int.le(lo, hi));
  ensures [clamp_ge_lo]: (int.ge(r, lo));
  ensures [clamp_le_hi]: (int.le(r, hi));
}
cfg entry {
  entry: {
    branch (int.lt(x, lo)) goto below else goto not_below;
  }
  below: {
    r := lo;
    assert [below_r_le_hi]: (int.le(r, hi));
    goto done;
  }
  not_below: {
    branch (int.gt(x, hi)) goto above else goto inside;
  }
  above: {
    r := hi;
    goto done;
  }
  inside: {
    r := x;
    goto done;
  }
  done: {
    return;
  }
};
