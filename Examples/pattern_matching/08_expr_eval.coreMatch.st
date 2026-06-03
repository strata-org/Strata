program CoreMatch;

// Expression-tree evaluator: natural-style recursion on `l` and `r`.

datatype Op   () { Plus(), Times(), Minus() };
datatype Tree () { Lit(v : int), Bin(op : Op, l : Tree, r : Tree) };

rec function eval(t : Tree) : int
{
  match t {
    arm Lit(v : int) => v;
    arm Bin(op : Op, l : Tree, r : Tree) =>
      match op {
        arm Plus()  => eval(l) + eval(r);
        arm Times() => eval(l) * eval(r);
        arm Minus() => eval(l) - eval(r);
      };
  }
};

rec function size(t : Tree) : int
{
  match t {
    arm Lit(v : int) => 1;
    arm Bin(op : Op, l : Tree, r : Tree) => 1 + size(l) + size(r);
  }
};

rec function constantsOnly(t : Tree) : bool
{
  match t {
    arm Lit(v : int) => true;
    arm Bin(op : Op, l : Tree, r : Tree) => constantsOnly(l) && constantsOnly(r);
  }
};
