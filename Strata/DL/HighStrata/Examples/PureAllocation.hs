composite Empty {}

val pureCompositeAllocator = function(): boolean {
  var i: partial pure Empty = create Empty -- calling create inside a pure context returns a pure type
  var j = create Empty
  i =&= j
--  ^^^ reference equality operator '=&=' can not be used on pure types
}