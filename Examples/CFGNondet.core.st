program Core;

// Nondeterministic CFG: y is set to either 1 or 2.
procedure NondetChoice(out y : int)
spec {
  ensures (y == 1 || y == 2);
}
cfg entry {
  entry: {
    goto left, right;
  }
  left: {
    y := 1;
    goto done;
  }
  right: {
    y := 2;
    goto done;
  }
  done: {
    return;
  }
};
