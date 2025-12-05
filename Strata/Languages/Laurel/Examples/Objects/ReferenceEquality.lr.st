-- Pure types
val impureTypeUser = procedure(i: pure Container, j: pure Container): boolean {
  i =&= j
--  ^^^ reference equality operator '=&=' can not be used on pure types
}
