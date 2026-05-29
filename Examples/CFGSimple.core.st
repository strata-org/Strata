program Core;

// A simple deterministic CFG: compute max of two integers.
procedure Max(x : int, y : int, out m : int)
spec {
  ensures (m >= x);
  ensures (m >= y);
  ensures (m == x || m == y);
}
cfg entry {
  entry: {
    branch (x >= y) goto then_branch else goto else_branch;
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

// A CFG with a simple loop: increment y until it reaches n.
procedure CountUp(n : int, out y : int)
spec {
  requires (n >= 0);
  ensures (y == n);
}
cfg entry {
  entry: {
    y := 0;
    goto loop;
  }
  loop: {
    branch (y < n) goto body else goto done;
  }
  body: {
    y := y + 1;
    goto loop;
  }
  done: {
    return;
  }
};
