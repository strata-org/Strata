program Core;

procedure P1(x : int, out y : int)
spec { ensures (y >= 0); }
{}
cfg entry {
  entry: { branch (x >= 0) goto pos else neg; }
  pos: { y := x; goto done; }
  neg: { y := 0; goto done; }
  done: { return; }
};

procedure P2(x : int, out y : int)
spec { ensures (y >= 0); }
{}
cfg entry {
  entry: { branch (x >= 0) goto pos else neg; }
  pos: { y := x; goto done; }
  neg: { y := 0; goto done; }
  done: { return; }
};

procedure P3(x : int, out y : int)
spec { ensures (y >= 0); }
{}
cfg entry {
  entry: { branch (x >= 0) goto pos else neg; }
  pos: { y := x; goto done; }
  neg: { y := 0; goto done; }
  done: { return; }
};

procedure P4(x : int, out y : int)
spec { ensures (y >= 0); }
{}
cfg entry {
  entry: { branch (x >= 0) goto pos else neg; }
  pos: { y := x; goto done; }
  neg: { y := 0; goto done; }
  done: { return; }
};

procedure P5(x : int, out y : int)
spec { ensures (y >= 0); }
{}
cfg entry {
  entry: { branch (x >= 0) goto pos else neg; }
  pos: { y := x; goto done; }
  neg: { y := 0; goto done; }
  done: { return; }
};

procedure P6(x : int, out y : int)
spec { ensures (y >= 0); }
{}
cfg entry {
  entry: { branch (x >= 0) goto pos else neg; }
  pos: { y := x; goto done; }
  neg: { y := 0; goto done; }
  done: { return; }
};

procedure P7(x : int, out y : int)
spec { ensures (y >= 0); }
{}
cfg entry {
  entry: { branch (x >= 0) goto pos else neg; }
  pos: { y := x; goto done; }
  neg: { y := 0; goto done; }
  done: { return; }
};

procedure P8(x : int, out y : int)
spec { ensures (y >= 0); }
{}
cfg entry {
  entry: { branch (x >= 0) goto pos else neg; }
  pos: { y := x; goto done; }
  neg: { y := 0; goto done; }
  done: { return; }
};

procedure P9(x : int, out y : int)
spec { ensures (y >= 0); }
{}
cfg entry {
  entry: { branch (x >= 0) goto pos else neg; }
  pos: { y := x; goto done; }
  neg: { y := 0; goto done; }
  done: { return; }
};

procedure P10(x : int, out y : int)
spec { ensures (y >= 0); }
{}
cfg entry {
  entry: { branch (x >= 0) goto pos else neg; }
  pos: { y := x; goto done; }
  neg: { y := 0; goto done; }
  done: { return; }
};

procedure P11(x : int, out y : int)
spec { ensures (y >= 0); }
{}
cfg entry {
  entry: { branch (x >= 0) goto pos else neg; }
  pos: { y := x; goto done; }
  neg: { y := 0; goto done; }
  done: { return; }
};

procedure P12(x : int, out y : int)
spec { ensures (y >= 0); }
{}
cfg entry {
  entry: { branch (x >= 0) goto pos else neg; }
  pos: { y := x; goto done; }
  neg: { y := 0; goto done; }
  done: { return; }
};

procedure P13(x : int, out y : int)
spec { ensures (y >= 0); }
{}
cfg entry {
  entry: { branch (x >= 0) goto pos else neg; }
  pos: { y := x; goto done; }
  neg: { y := 0; goto done; }
  done: { return; }
};

procedure P14(x : int, out y : int)
spec { ensures (y >= 0); }
{}
cfg entry {
  entry: { branch (x >= 0) goto pos else neg; }
  pos: { y := x; goto done; }
  neg: { y := 0; goto done; }
  done: { return; }
};

procedure P15(x : int, out y : int)
spec { ensures (y >= 0); }
{}
cfg entry {
  entry: { branch (x >= 0) goto pos else neg; }
  pos: { y := x; goto done; }
  neg: { y := 0; goto done; }
  done: { return; }
};

