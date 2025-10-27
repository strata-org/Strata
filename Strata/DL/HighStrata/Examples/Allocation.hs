-- Create immutable composite

composite Immutable {
  val x: int
  val y: int

  invariant x + y >= 5
}

val foo = function(): Immutable {
  var p: partial Immutable = create Immutable with x = 3;
  complete (p with y = 2)
}

-- Create mutable composite

composite ChainOfTwo {
  val other: ChainOfTwo
}

val completeChainOfTwo = procedure(first: partial ChainOfTwo): impure ChainOfTwo {
  var second = create ChainOfTwo;
  second.other = first;
  first.other = second;
  complete first, second
}

val foo = procedure() {
  var aChainOfTwo = completeChainOfTwo(create ChainOfTwo)
}
