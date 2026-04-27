/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

namespace Strata.TypeParamsTest

-- Basic: two generic functions used together in arithmetic.
-- Tests that tvar names from different declarations don't clash.
def typeParamsPrg : Program :=
#strata
program Core;

function left<T, U>(t: T, u: U) : T {
  t
}

function right<T, U>(t: T, u: U) : U {
  u
}

function double(a: int) : int {
  right(a, a) + left(a, a)
}

#end

-- Identity function: single type parameter, called with int and bool.
def identityPrg : Program :=
#strata
program Core;

function id<T>(x: T) : T {
  x
}

function useId(a: int) : int {
  id(a) + id(a)
}

function useIdBool(b: bool) : bool {
  id(b) && id(b)
}

#end

-- Nested generic calls: id(id(x)) and id applied to a 2-arg generic.
def nestedGenericsPrg : Program :=
#strata
program Core;

function id<T>(x: T) : T {
  x
}

function left<T, U>(t: T, u: U) : T {
  t
}

function right<T, U>(t: T, u: U) : U {
  u
}

function doubleId(a: int) : int {
  id(id(a))
}

function idOfLeft(a: int, b: bool) : int {
  id(left(a, b))
}

function idOfRight(a: int, b: bool) : bool {
  id(right(a, b))
}

#end

-- Three type parameters.
def threeParamsPrg : Program :=
#strata
program Core;

function fst3<A, B, C>(a: A, b: B, c: C) : A {
  a
}

function snd3<A, B, C>(a: A, b: B, c: C) : B {
  b
}

function thd3<A, B, C>(a: A, b: B, c: C) : C {
  c
}

function useFst3(a: int, b: bool, c: int) : int {
  fst3(a, b, c) + thd3(a, b, c)
}

#end

-- Mixed concrete types: int and bool as distinct type arguments.
def mixedTypesPrg : Program :=
#strata
program Core;

function left<T, U>(t: T, u: U) : T {
  t
}

function right<T, U>(t: T, u: U) : U {
  u
}

function pickInt(a: int, b: bool) : int {
  left(a, b)
}

function pickBool(a: int, b: bool) : bool {
  right(a, b)
}

function compareProjections(a: int, b: int, flag: bool) : bool {
  left(a, flag) == right(b, a)
}

#end

-- Generic in conditional expressions.
def condPrg : Program :=
#strata
program Core;

function id<T>(x: T) : T {
  x
}

function left<T, U>(t: T, u: U) : T {
  t
}

function condSelect(cond: bool, a: int, b: int) : int {
  if cond then id(a) else left(b, cond)
}

#end

-- Same generic called multiple times in one expression.
def multiCallPrg : Program :=
#strata
program Core;

function id<T>(x: T) : T {
  x
}

function sumIds(a: int, b: int, c: int) : int {
  id(a) + id(b) + id(c)
}

function allTrue(p: bool, q: bool) : bool {
  id(p) && id(q)
}

#end

end Strata.TypeParamsTest
