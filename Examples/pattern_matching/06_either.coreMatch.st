program CoreMatch;

// Either with heterogeneously-typed constructor fields.

datatype Either () { LeftI(v : int), RightB(b : bool) };

function isError(e : Either) : bool
{
  match e {
    arm LeftI(v : int)   => v < 0;
    arm RightB(b : bool) => !b;
  }
};

function describeKind(e : Either) : int
{
  match e {
    arm LeftI(v : int)   => 1;
    arm RightB(b : bool) => 2;
  }
};

function unwrapOr(e : Either, dflt : int) : int
{
  match e {
    arm LeftI(v : int)   => v;
    arm RightB(b : bool) => dflt;
  }
};
