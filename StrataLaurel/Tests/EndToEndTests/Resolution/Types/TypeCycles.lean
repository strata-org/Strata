/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # A type defined in terms of itself

Resolution rejects an alias or constrained type whose unfolding reaches itself, at each
declaration on the cycle. -/

#eval testLaurelResolution <|
#strata
program Laurel;
type M = TotalMap int M
//   ^ error: type 'M' is defined in terms of itself
// `E` refers to the cycle without being on it.
type E = M
type Q = P
//   ^ error: type 'Q' is defined in terms of itself
constrained P = x: Q where true witness 0
//          ^ error: type 'P' is defined in terms of itself
constrained A = x: B where true witness 0
//          ^ error: type 'A' is defined in terms of itself
constrained B = y: A where true witness 0
//          ^ error: type 'B' is defined in terms of itself
// Through a map: a generic datatype does not take a constrained type as an argument.
constrained U = x: TotalMap int U where true witness <?>
//          ^ error: type 'U' is defined in terms of itself
// `I` keeps its argument, however often it is applied.
type I<X> = X
type J = I<I<J>>
//   ^ error: type 'J' is defined in terms of itself
// `F` drops its second argument, also where it is applied to itself, so `H` is `int`.
type F<A, B> = A
type H = F<F<int, H>, int>
// `K` drops its argument through `F`, at every use, so `G` is `Map<int, int>`.
type K<X> = F<int, X>
type G = Map<K<G>, K<G>>
// `W` reaches itself, so it keeps its argument where `V` uses it.
type W<X> = W<X>
//   ^ error: type 'W' is defined in terms of itself
type V = W<V>
//   ^ error: type 'V' is defined in terms of itself
// `L`'s parameter is spelled like the alias `T`, whose target mentions `L`, but names only
// the parameter.
type T = L<int>
type L<T> = Set<T>
// `F` takes two arguments, so `R` is reported for that alone.
type R = F<R>
//       ^^^^ error: 'F' expects 2 type argument(s) but 1 were provided
// `S` names itself without arguments, which still defines it in terms of itself.
type S<T> = Set<S>
//   ^ error: type 'S' is defined in terms of itself
// A use of `M` gets the type error it causes besides the cycle error above.
procedure p() opaque { var x: M := 1; assert true };
//                                 ^ error: expected 'M', got 'int'
#end
