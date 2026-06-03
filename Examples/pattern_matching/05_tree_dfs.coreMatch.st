program CoreMatch;

// Binary tree DFS: natural-style recursion on `left` and `right`.

datatype Tree () { Leaf(), Node(value : int, left : Tree, right : Tree) };

rec function treeSum(t : Tree) : int
{
  match t {
    arm Leaf() => 0;
    arm Node(value : int, left : Tree, right : Tree) =>
      value + treeSum(left) + treeSum(right);
  }
};

rec function nodeCount(t : Tree) : int
{
  match t {
    arm Leaf() => 0;
    arm Node(value : int, left : Tree, right : Tree) =>
      1 + nodeCount(left) + nodeCount(right);
  }
};

rec function depth(t : Tree) : int
{
  match t {
    arm Leaf() => 0;
    arm Node(value : int, left : Tree, right : Tree) =>
      1 + (if depth(left) >= depth(right) then depth(left) else depth(right));
  }
};

rec function allNonNeg(t : Tree) : bool
{
  match t {
    arm Leaf() => true;
    arm Node(value : int, left : Tree, right : Tree) =>
      value >= 0 && allNonNeg(left) && allNonNeg(right);
  }
};

rec function containsZero(t : Tree) : bool
{
  match t {
    arm Leaf() => false;
    arm Node(value : int, left : Tree, right : Tree) =>
      value == 0 || containsZero(left) || containsZero(right);
  }
};
