/- Authors(s):
Your Name <your.email@example.com>
-/

import Strata.DL.Lambda.LTy
import Lean

---------------------------------------------------------------------

namespace Heap

open Lambda (TyIdentifier LMonoTy LTy)

/-! ## Heap Types

Extension of the Lambda type system to include heap-related types.
We add an address type for heap references and object types for heap-allocated data.
-/

/--
Heap-specific mono-types extending the Lambda type system.
-/
inductive HMonoTy : Type where
  -- Include all Lambda types
  | lambda (ty : LMonoTy)
  -- New heap-specific types
  | addr                                    -- Address/pointer type
  | obj (fieldCount : Nat) (fieldType : HMonoTy)  -- Object with N fields of same type
  deriving Inhabited, Repr

abbrev HMonoTys := List HMonoTy

-- Convenience constructors
@[match_pattern]
def HMonoTy.bool : HMonoTy := .lambda LMonoTy.bool

@[match_pattern]
def HMonoTy.int : HMonoTy := .lambda LMonoTy.int

-- Helper function to create object types
def HMonoTy.mkObj (fieldCount : Nat) (fieldType : HMonoTy) : HMonoTy :=
  .obj fieldCount fieldType

-- Function types (arrows) - delegate to Lambda
def HMonoTy.arrow (t1 t2 : HMonoTy) : HMonoTy :=
  match t1, t2 with
  | .lambda lt1, .lambda lt2 => .lambda (LMonoTy.arrow lt1 lt2)
  | _, _ => .lambda (.tcons "arrow" []) -- Fallback for mixed types

/--
Heap type schemes (poly-types).
-/
inductive HTy : Type where
  | forAll (vars : List TyIdentifier) (ty : HMonoTy)
  deriving Inhabited, Repr

abbrev HTys := List HTy

-- Conversion functions between Lambda and Heap types
def LMonoTy.toHeap : LMonoTy → HMonoTy := HMonoTy.lambda

def HMonoTy.toLambda? : HMonoTy → Option LMonoTy
  | .lambda ty => some ty
  | _ => none

end Heap
