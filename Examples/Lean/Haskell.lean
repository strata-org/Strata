/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Very rough dialect with some Haskell-like code for example purposes.
import Strata

#dialect
dialect Haskell;
// This introduces natural numbers and a polymorphic list type.
// The dialect is functioning as hardcoding features of Haskell's prelude.
// It would be an interesting exersise to see if we can move away from this.
type List (tp : Type);
type Nat;

// Nil requires an explicit type.
fn emptyList (tp : Type) : List tp => "nil " tp;
fn consList (tp : Type, h : tp, r : List tp) : List tp
  => h ":" r;

// Fold syntax is currently hard-coded
fn foldl (a : Type, b : Type, f : b -> a -> a, init : b, l : List a) : b
  => "foldl " f init l;

// A variable binding in Strata.  Note that variable bindings require explicit
// types.  We do not have a way of inferring types in variable bindings.
category Binding;
@[declare(v, tp)]
op binding (v : Ident, tp : TypeP) : Binding => "(" v " : " tp ")";
// Bindings are a sequence of Binding.  The scope annotation makes
// the introduced variables visible to entities that use Bindings scope.
category Bindings;

@[scope(l)]
op mkBindings (l : Seq Binding) : Bindings => l;

// Strata has extensible syntax for defining your own Lambda
fn lambda (b : Bindings, tp : Type, @[scope(b)] rhs : tp) : fnOf(b, tp)
  => "\\" b "->" rhs;

// The declareFn line would declare a function with the given bindings and type.
//@[declareFn(name, b, tp)]
op typeDecl (name : Ident, b : Bindings, @[scope(b)] tp : Type)
  : Command => name b "::" tp ";";
// This is a type declaration
op eqDecl (name : Ident, bindings : Bindings, tp : Type, @[scope(bindings)] rhs : tp)
  : Command => name bindings "=" rhs ";";
#end

--Here is a Haskell program and its representation in Strata using the above dialect.
-- reverse :: [a] -> [a]
-- reverse l = foldl (\r a -> a : r) [] l

def example1 := #strata
program Haskell;
reverse (a : Type) (v : List a) :: List a;
reverse (a : Type) (l : List a) = foldl (\(r : List a) (h : a) -> (h : r)) (nil a) l;
#end
