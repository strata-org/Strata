/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Backends.CBMC.GOTO.InstToJson

/-! # JSON serialisation of GOTO expressions, types and symbols

Pins the exact JSON text that `exprToJson`, `tyToJson` and the symbol
constructors produce for struct, pointer, array and global-variable shapes, as
read by CBMC's `symtab2gb`. -/

meta section

namespace CProverGOTO.InstToJsonTests

open CProverGOTO

private def u32 : Ty := .UnsignedBV 32

private def sTy : Ty := .StructTag "S"

private def sPtr : Ty := .Pointer sTy

private def p : Expr := Expr.symbol "main::1::p" sPtr

private def jsonText (e : Except String Lean.Json) : String :=
  match e with
  | .ok j => j.compress
  | .error msg => s!"error: {msg}"

-------------------------------------------------------------------------------

/-! ## `member` -/

/-- `p->a`, a member of a dereference. -/
private def pa : Expr := Expr.member (Expr.dereference p sTy) "a" u32

/-- info: "((member(a)((dereference(main::1::p : (pointer struct_tag(S)))) : struct_tag(S))) : unsignedbv[32])" -/
#guard_msgs in
#eval toString (Std.format pa)

/--
info: "{\"id\":\"member\",\"namedSub\":{\"component_name\":{\"id\":\"a\"},\"type\":{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}}},\"sourceLocation\":{},\"sub\":[{\"id\":\"dereference\",\"namedSub\":{\"type\":{\"id\":\"struct_tag\",\"namedSub\":{\"identifier\":{\"id\":\"tag-S\"}}}},\"sourceLocation\":{},\"sub\":[{\"id\":\"symbol\",\"namedSub\":{\"identifier\":{\"id\":\"main::1::p\"},\"type\":{\"id\":\"pointer\",\"namedSub\":{\"width\":{\"id\":\"64\"}},\"sub\":[{\"id\":\"struct_tag\",\"namedSub\":{\"identifier\":{\"id\":\"tag-S\"}}}]}},\"sourceLocation\":{}}]}]}"
-/
#guard_msgs in
#eval jsonText (exprToJson pa)

-------------------------------------------------------------------------------

/-! ## `address_of` -/

-- `&p->a` has the type `unsignedbv 32 *`.
#guard (Expr.addressOf pa).type == .Pointer u32

/--
info: "{\"id\":\"address_of\",\"namedSub\":{\"type\":{\"id\":\"pointer\",\"namedSub\":{\"width\":{\"id\":\"64\"}},\"sub\":[{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}}]}},\"sourceLocation\":{},\"sub\":[{\"id\":\"member\",\"namedSub\":{\"component_name\":{\"id\":\"a\"},\"type\":{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}}},\"sourceLocation\":{},\"sub\":[{\"id\":\"dereference\",\"namedSub\":{\"type\":{\"id\":\"struct_tag\",\"namedSub\":{\"identifier\":{\"id\":\"tag-S\"}}}},\"sourceLocation\":{},\"sub\":[{\"id\":\"symbol\",\"namedSub\":{\"identifier\":{\"id\":\"main::1::p\"},\"type\":{\"id\":\"pointer\",\"namedSub\":{\"width\":{\"id\":\"64\"}},\"sub\":[{\"id\":\"struct_tag\",\"namedSub\":{\"identifier\":{\"id\":\"tag-S\"}}}]}},\"sourceLocation\":{}}]}]}]}"
-/
#guard_msgs in
#eval jsonText (exprToJson (Expr.addressOf pa))

-------------------------------------------------------------------------------

/-! ## Struct type definitions -/

private def sDef : StructDef := { name := "S", components := [("a", u32), ("b", u32)] }

#guard sDef.ty == sTy

/--
info: "{\"id\":\"struct\",\"namedSub\":{\"components\":{\"id\":\"\",\"sub\":[{\"id\":\"\",\"namedSub\":{\"#pretty_name\":{\"id\":\"a\"},\"name\":{\"id\":\"a\"},\"type\":{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}}}},{\"id\":\"\",\"namedSub\":{\"#pretty_name\":{\"id\":\"b\"},\"name\":{\"id\":\"b\"},\"type\":{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}}}}]},\"tag\":{\"id\":\"S\"}}}"
-/
#guard_msgs in
#eval (structDefToJson sDef).compress

-- The symbol is the type symbol `tag-S`, which `Ty.StructTag "S"` refers to.
#guard
  let (key, sym) := createStructTypeSymbol sDef
  key == "tag-S" && sym.name == "tag-S" && sym.baseName == "S" && sym.isType &&
  !sym.isStaticLifetime && sym.prettyName == "struct S" &&
  sym.type == structDefToJson sDef && sym.value == Lean.Json.mkObj [("id", "nil")]

-------------------------------------------------------------------------------

/-! ## Array sizes and index types -/

private def tyText (ty : Ty) : String := (tyToJson ty).compress

-- An array without size or index type keeps the plain `array` shape.
/-- info: "{\"id\":\"array\",\"sub\":[{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}}]}" -/
#guard_msgs in
#eval tyText (.Array u32)

#guard tyText (Ty.mkArray u32 none) == tyText (.Array u32)

-- A constant size defaults to CBMC's index type `signedbv 64`, in hexadecimal.
/--
info: "{\"id\":\"array\",\"namedSub\":{\"size\":{\"id\":\"constant\",\"namedSub\":{\"type\":{\"id\":\"signedbv\",\"namedSub\":{\"width\":{\"id\":\"64\"}}},\"value\":{\"id\":\"1A\"}}}},\"sub\":[{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}}]}"
-/
#guard_msgs in
#eval tyText (Ty.mkArray u32 (some (.constant 26)))

-- The size 0 is written `0`.
/--
info: "{\"id\":\"array\",\"namedSub\":{\"size\":{\"id\":\"constant\",\"namedSub\":{\"type\":{\"id\":\"signedbv\",\"namedSub\":{\"width\":{\"id\":\"64\"}}},\"value\":{\"id\":\"0\"}}}},\"sub\":[{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}}]}"
-/
#guard_msgs in
#eval tyText (Ty.mkArray u32 (some (.constant 0)))

/--
info: "{\"id\":\"array\",\"namedSub\":{\"size\":{\"id\":\"infinity\",\"namedSub\":{\"type\":{\"id\":\"signedbv\",\"namedSub\":{\"width\":{\"id\":\"64\"}}}}}},\"sub\":[{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}}]}"
-/
#guard_msgs in
#eval tyText (Ty.mkArray u32 (some .infinity))

-- With an index type, the size has that type and `#index_type` is written.
/--
info: "{\"id\":\"array\",\"namedSub\":{\"#index_type\":{\"id\":\"integer\"},\"size\":{\"id\":\"infinity\",\"namedSub\":{\"type\":{\"id\":\"integer\"}}}},\"sub\":[{\"id\":\"integer\"}]}"
-/
#guard_msgs in
#eval tyText (Ty.mkArray .Integer (some .infinity) (some .Integer))

/--
info: "{\"id\":\"array\",\"namedSub\":{\"#index_type\":{\"id\":\"integer\"},\"size\":{\"id\":\"constant\",\"namedSub\":{\"type\":{\"id\":\"integer\"},\"value\":{\"id\":\"1048576\"}}}},\"sub\":[{\"id\":\"integer\"}]}"
-/
#guard_msgs in
#eval tyText (Ty.mkArray .Integer (some (.constant 1048576)) (some .Integer))

/--
info: "{\"id\":\"array\",\"namedSub\":{\"#index_type\":{\"id\":\"signedbv\",\"namedSub\":{\"width\":{\"id\":\"64\"}}}},\"sub\":[{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}}]}"
-/
#guard_msgs in
#eval tyText (Ty.mkArray u32 none (some (.SignedBV 64)))

-------------------------------------------------------------------------------

/-! ## Global variables -/

/--
info: "{\"baseName\":\"g\",\"isAuxiliary\":false,\"isExported\":false,\"isExtern\":false,\"isFileLocal\":false,\"isInput\":false,\"isLvalue\":true,\"isMacro\":false,\"isOutput\":false,\"isParameter\":false,\"isProperty\":false,\"isStateVar\":false,\"isStaticLifetime\":true,\"isThreadLocal\":false,\"isType\":false,\"isVolatile\":false,\"isWeak\":false,\"mode\":\"C\",\"module\":\"m\",\"name\":\"g\",\"prettyName\":\"g\",\"prettyType\":\"\",\"prettyValue\":\"\",\"type\":{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}},\"value\":{\"id\":\"constant\",\"namedSub\":{\"type\":{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}},\"value\":{\"id\":\"0\"}},\"sourceLocation\":{}}}"
-/
#guard_msgs in
#eval jsonText ((createGlobalSymbol "m" "g" u32 (Expr.constant "0" u32)).map
  fun (_, sym) => Lean.toJson sym)

#guard match createGlobalSymbol "m" "g" u32 (Expr.constant "0" u32) with
  | .ok (key, _) => key == "g"
  | .error _ => false

-- Local variables keep their thread-local, file-local, non-static entries.
#guard
  let (_, sym) := createGOTOSymbol "main" "x" "main::1::x" false false (some u32)
  sym.isThreadLocal && sym.isFileLocal && !sym.isStaticLifetime

-------------------------------------------------------------------------------

/-! ## `nil` -/

/-- info: "{\"id\":\"nil\"}" -/
#guard_msgs in
#eval jsonText (exprToJson Expr.nil)

-- A call whose result is discarded has `nil` as its left-hand side.
/--
info: "{\"id\":\"code\",\"namedSub\":{\"statement\":{\"id\":\"function_call\"},\"type\":{\"id\":\"empty\"}},\"sourceLocation\":{},\"sub\":[{\"id\":\"nil\"},{\"id\":\"symbol\",\"namedSub\":{\"identifier\":{\"id\":\"set_g\"},\"type\":{\"id\":\"code\",\"namedSub\":{\"parameters\":{\"sub\":[]},\"return_type\":{\"id\":\"empty\"}}}},\"sourceLocation\":{}},{\"id\":\"arguments\",\"sub\":[]}]}"
-/
#guard_msgs in
#eval jsonText (codeToJson
  (Code.functionCall Expr.nil (Expr.symbol "set_g" (Ty.mkFunctionType [] .Empty)) []))

-------------------------------------------------------------------------------

/-! ## Struct-typed call results -/

private def pairTy : Ty := .StructTag "Pair"

/-- `json` without its comment fields (names starting with `#`), which CBMC
    ignores when it compares types. -/
private partial def dropComments (json : Lean.Json) : Lean.Json :=
  match json with
  | .obj kvs => .obj (kvs.foldl (init := {}) fun acc k v =>
      if k.startsWith "#" then acc else acc.insert k (dropComments v))
  | .arr xs => .arr (xs.map dropComments)
  | j => j

-- The callee type of a call equals the callee's symbol table type, up to
-- parameter names, which is what `cbmc --validate-goto-model` checks.
#guard
  let (_, sym) := createFunctionSymbol "mk" [("x", u32)] pairTy
  dropComments sym.type == tyToJson (Ty.mkFunctionType [u32] pairTy)

-- Each parameter of a function type is a `parameter` irep.
/--
info: "{\"id\":\"code\",\"namedSub\":{\"parameters\":{\"sub\":[{\"id\":\"parameter\",\"namedSub\":{\"type\":{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}}}}]},\"return_type\":{\"id\":\"struct_tag\",\"namedSub\":{\"identifier\":{\"id\":\"tag-Pair\"}}}}}"
-/
#guard_msgs in
#eval tyText (Ty.mkFunctionType [u32] pairTy)

/-- `main::1::q := mk(7)`, with `q : Pair`. -/
private def callMk : Code :=
  Code.functionCall (Expr.symbol "main::1::q" pairTy)
    (Expr.symbol "mk" (Ty.mkFunctionType [u32] pairTy)) [Expr.constant "7" u32]

/--
info: "{\"id\":\"code\",\"namedSub\":{\"statement\":{\"id\":\"function_call\"},\"type\":{\"id\":\"empty\"}},\"sourceLocation\":{},\"sub\":[{\"id\":\"symbol\",\"namedSub\":{\"identifier\":{\"id\":\"main::1::q\"},\"type\":{\"id\":\"struct_tag\",\"namedSub\":{\"identifier\":{\"id\":\"tag-Pair\"}}}},\"sourceLocation\":{}},{\"id\":\"symbol\",\"namedSub\":{\"identifier\":{\"id\":\"mk\"},\"type\":{\"id\":\"code\",\"namedSub\":{\"parameters\":{\"sub\":[{\"id\":\"parameter\",\"namedSub\":{\"type\":{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}}}}]},\"return_type\":{\"id\":\"struct_tag\",\"namedSub\":{\"identifier\":{\"id\":\"tag-Pair\"}}}}}},\"sourceLocation\":{}},{\"id\":\"arguments\",\"sub\":[{\"id\":\"constant\",\"namedSub\":{\"type\":{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}},\"value\":{\"id\":\"7\"}},\"sourceLocation\":{}}]}]}"
-/
#guard_msgs in
#eval jsonText (codeToJson callMk)

-- `SET_RETURN_VALUE v`, with the local `v : Pair`.
/--
info: "{\"id\":\"code\",\"namedSub\":{\"statement\":{\"id\":\"return\"},\"type\":{\"id\":\"empty\"}},\"sourceLocation\":{},\"sub\":[{\"id\":\"symbol\",\"namedSub\":{\"identifier\":{\"id\":\"mk::1::v\"},\"type\":{\"id\":\"struct_tag\",\"namedSub\":{\"identifier\":{\"id\":\"tag-Pair\"}}}},\"sourceLocation\":{}}]}"
-/
#guard_msgs in
#eval jsonText (codeToJson (Code.set_return_value (Expr.symbol "mk::1::v" pairTy)))

-------------------------------------------------------------------------------

/-! ## `array` and `struct` values -/

/-- The array type `unsignedbv 32 [2]`. -/
private def u32x2 : Ty := Ty.mkArray u32 (some (.constant 2))

/-- The array value `{104, 105}`. -/
private def hi : Expr := Expr.array [Expr.constant "104" u32, Expr.constant "105" u32] u32x2

/-- info: "(array{(104 : unsignedbv[32]), (105 : unsignedbv[32])} : (array[2] unsignedbv[32]))" -/
#guard_msgs in
#eval toString (Std.format hi)

/--
info: "{\"id\":\"array\",\"namedSub\":{\"type\":{\"id\":\"array\",\"namedSub\":{\"size\":{\"id\":\"constant\",\"namedSub\":{\"type\":{\"id\":\"signedbv\",\"namedSub\":{\"width\":{\"id\":\"64\"}}},\"value\":{\"id\":\"2\"}}}},\"sub\":[{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}}]}},\"sourceLocation\":{},\"sub\":[{\"id\":\"constant\",\"namedSub\":{\"type\":{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}},\"value\":{\"id\":\"68\"}},\"sourceLocation\":{}},{\"id\":\"constant\",\"namedSub\":{\"type\":{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}},\"value\":{\"id\":\"69\"}},\"sourceLocation\":{}}]}"
-/
#guard_msgs in
#eval jsonText (exprToJson hi)

/-- The struct value `{2, &g[0]}` of type `Str`, with `g` the global array above. -/
private def strVal : Expr :=
  let g := Expr.symbol "g" u32x2
  Expr.struct [Expr.constant "2" (.UnsignedBV 64),
    Expr.addressOf (Expr.index g (Expr.constant "0" (.SignedBV 64)) u32)] (.StructTag "Str")

/--
info: "(struct{(2 : unsignedbv[64]), ((address_of(((g : (array[2] unsignedbv[32])) index (0 : signedbv[64])) : unsignedbv[32])) : (pointer unsignedbv[32]))} : struct_tag(Str))"
-/
#guard_msgs in
#eval toString (Std.format strVal)

/--
info: "{\"id\":\"struct\",\"namedSub\":{\"type\":{\"id\":\"struct_tag\",\"namedSub\":{\"identifier\":{\"id\":\"tag-Str\"}}}},\"sourceLocation\":{},\"sub\":[{\"id\":\"constant\",\"namedSub\":{\"type\":{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"64\"}}},\"value\":{\"id\":\"2\"}},\"sourceLocation\":{}},{\"id\":\"address_of\",\"namedSub\":{\"type\":{\"id\":\"pointer\",\"namedSub\":{\"width\":{\"id\":\"64\"}},\"sub\":[{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}}]}},\"sourceLocation\":{},\"sub\":[{\"id\":\"index\",\"namedSub\":{\"type\":{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}}},\"sourceLocation\":{},\"sub\":[{\"id\":\"symbol\",\"namedSub\":{\"identifier\":{\"id\":\"g\"},\"type\":{\"id\":\"array\",\"namedSub\":{\"size\":{\"id\":\"constant\",\"namedSub\":{\"type\":{\"id\":\"signedbv\",\"namedSub\":{\"width\":{\"id\":\"64\"}}},\"value\":{\"id\":\"2\"}}}},\"sub\":[{\"id\":\"unsignedbv\",\"namedSub\":{\"width\":{\"id\":\"32\"}}}]}},\"sourceLocation\":{}},{\"id\":\"constant\",\"namedSub\":{\"type\":{\"id\":\"signedbv\",\"namedSub\":{\"width\":{\"id\":\"64\"}}},\"value\":{\"id\":\"0\"}},\"sourceLocation\":{}}]}]}]}"
-/
#guard_msgs in
#eval jsonText (exprToJson strVal)

end CProverGOTO.InstToJsonTests

end
