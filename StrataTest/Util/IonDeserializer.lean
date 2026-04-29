/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Util.IonDeserializer

-- Test structure
structure Point where
  x : Nat
  y : Nat
deriving Repr, BEq

-- Verify the elaborator produces a well-typed function
def deserializePoint : ByteArray → Except Std.Format Point :=
  getIonDeserializer% Point

-- Test multi-constructor inductive
inductive Color where
  | red
  | green
  | blue
deriving Repr, BEq

def deserializeColor : ByteArray → Except Std.Format Color :=
  getIonDeserializer% Color

-- Test inductive with fields
inductive Shape where
  | circle (radius : Nat)
  | rect (width : Nat) (height : Nat)
deriving Repr, BEq

def deserializeShape : ByteArray → Except Std.Format Shape :=
  getIonDeserializer% Shape

-- Test structure with String and Bool
structure Person where
  name : String
  age : Nat
  active : Bool
deriving Repr, BEq

def deserializePerson : ByteArray → Except Std.Format Person :=
  getIonDeserializer% Person

-- Test structure with Int
structure Offset where
  dx : Int
  dy : Int
deriving Repr, BEq

def deserializeOffset : ByteArray → Except Std.Format Offset :=
  getIonDeserializer% Offset

-- Test structure with Float
structure Measurement where
  value : Float
  tolerance : Float
deriving Repr, BEq

def deserializeMeasurement : ByteArray → Except Std.Format Measurement :=
  getIonDeserializer% Measurement

-- Test nested structure (non-recursive)
structure Line where
  start : Point
  stop : Point
deriving Repr, BEq

def deserializeLine : ByteArray → Except Std.Format Line :=
  getIonDeserializer% Line

-- Test recursive type
inductive Tree where
  | leaf (value : Nat)
  | node (left : Tree) (right : Tree)
deriving Repr, BEq

partial def deserializeTree : ByteArray → Except Std.Format Tree :=
  getIonDeserializer% Tree

-- Verify type signatures
#check (deserializePoint : ByteArray → Except Std.Format Point)
#check (deserializeColor : ByteArray → Except Std.Format Color)
#check (deserializeShape : ByteArray → Except Std.Format Shape)
#check (deserializePerson : ByteArray → Except Std.Format Person)
#check (deserializeOffset : ByteArray → Except Std.Format Offset)
#check (deserializeMeasurement : ByteArray → Except Std.Format Measurement)
#check (deserializeLine : ByteArray → Except Std.Format Line)
#check (deserializeTree : ByteArray → Except Std.Format Tree)

-- Test structure with List fields
structure Polygon where
  vertices : List Point
deriving Repr, BEq

partial def deserializePolygon : ByteArray → Except Std.Format Polygon :=
  getIonDeserializer% Polygon

#check (deserializePolygon : ByteArray → Except Std.Format Polygon)

-- Test structure with Option fields
structure Config where
  name : String
  timeout : Option Nat
deriving Repr, BEq

def deserializeConfig : ByteArray → Except Std.Format Config :=
  getIonDeserializer% Config

#check (deserializeConfig : ByteArray → Except Std.Format Config)

-- Test structure with Decimal fields
structure Price where
  amount : Strata.Decimal
deriving Repr, BEq

def deserializePrice : ByteArray → Except Std.Format Price :=
  getIonDeserializer% Price

#check (deserializePrice : ByteArray → Except Std.Format Price)

-- Test structure with List of leaf types
structure Numbers where
  values : List Nat
deriving Repr, BEq

def deserializeNumbers : ByteArray → Except Std.Format Numbers :=
  getIonDeserializer% Numbers

#check (deserializeNumbers : ByteArray → Except Std.Format Numbers)

-- Test structure with Option of compound type
structure MaybeLine where
  line : Option Line
deriving Repr, BEq

partial def deserializeMaybeLine : ByteArray → Except Std.Format MaybeLine :=
  getIonDeserializer% MaybeLine

#check (deserializeMaybeLine : ByteArray → Except Std.Format MaybeLine)
