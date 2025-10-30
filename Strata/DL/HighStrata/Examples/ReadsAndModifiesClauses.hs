/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
composite Container {
  var value: int
}

val permissionLessReader = function(c: Container): int
  { c.value }
--  ^^^^^^^ error: enclosing function 'permissionLessReader' does not have permission to read 'c.value'

val varReader = function(c: Container): int
  reads c
  { c.value }

composite ImmutableContainer {
  val value: int
}

val valReader = function(c: ImmutableContainer): int
  { c.value } -- no reads clause needed because value is immutable

val opaqueFunction = function(c: Container): int
  reads c
  ensures true 
  { 3 }

val foo = procedure(c: Container, d: Container) 
{
  var x = opaqueFunction(c);
  modifyContainer(d);
  var y = opaqueFunction(c);
  assert x == y; -- functions return the same result when the arguments and read objects are the same
  modifyContainer(c);
  c.value = c.value + 1;
  var z = opaqueFunction(c);
  assert x == z;
--         ^^ error: could not prove assert
}

val modifyContainer(c: Container) 
  modifies c
{
  c.value = c.value + 1;
}

val modifyContainerWithoutPermission(c: Container) 
{
  c.value = c.value + 1;
--        ^ error: enclosing function 'modifyContainerWithoutPermission' does not have permission to modify 'c.value'
}

-- Pure types
val impureTypeUser = function(i: pure Container, j: pure Container): boolean {
  i =&= j
--  ^^^ reference equality operator '=&=' can not be used on pure types
}