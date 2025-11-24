val foo = procedure() {
  assert true; -- pass
  assert false; -- error
  assert false; -- TODO: decide if this has an error
}

val bar = procedure() {
  assume false; -- pass
  assert true; -- pass
}