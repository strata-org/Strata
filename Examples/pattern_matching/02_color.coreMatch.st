program CoreMatch;

// Pure enum with wildcard arms covering uncovered constructors.

datatype Color () { Red(), Green(), Blue(), Yellow() };

function isWarm(c : Color) : bool
{
  match c {
    arm Red()    => true;
    arm Yellow() => true;
    arm _        => false;
  }
};

function isPrimary(c : Color) : bool
{
  match c {
    arm Red()   => true;
    arm Green() => true;
    arm Blue()  => true;
    arm _       => false;
  }
};

function rank(c : Color) : int
{
  match c {
    arm Red()    => 1;
    arm Green()  => 2;
    arm Blue()   => 3;
    arm Yellow() => 4;
  }
};
