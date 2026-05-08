program CoreMatch;

// Option-like enum: non-recursive datatype, simplest possible match.

datatype OptInt () { None(), Some(val : int) };

function getOr(o : OptInt, dflt : int) : int
{
  match o {
    arm None()              => dflt;
    arm Some(val : int)     => val;
  }
};

function isSome(o : OptInt) : bool
{
  match o {
    arm None()              => false;
    arm Some(val : int)     => true;
  }
};
