/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.InstToJson

/-!
# CBMC Default Symbol Table

Generates the built-in symbols that CBMC expects in every symbol table.
These are normally provided by CBMC's C front-end; since we bypass it,
we must supply them ourselves.

The symbols fall into three groups:
1. **Architecture constants** (`__CPROVER_architecture_*`) — platform-specific
   integer/string values describing the target machine.
2. **Built-in functions** (`__CPROVER_assert`, `__CPROVER_assume`, etc.) —
   declarations for CBMC's internal operations.
3. **Built-in variables** (`__CPROVER_rounding_mode`, `__CPROVER_memory`, etc.)
   — global state that CBMC's analysis expects to exist.
-/

namespace CProverGOTO

public section

/-- Target architecture configuration.

Currently hardcoded to arm64/macOS/LP64 defaults. To support cross-platform
verification, this should be made configurable via a CLI flag (e.g.,
`--arch-config <file>`) or by detecting the target from the input program.
Key parameters that vary across platforms:
- `pointerWidth`: 32 on ILP32, 64 on LP64/LLP64
- `longIntWidth`: 32 on LLP64 (Windows), 64 on LP64 (Linux/macOS)
- `endianness`: 1 = little-endian, 2 = big-endian
- `arch`/`os`: string identifiers for the target platform

See also the "Hardcoded architecture configuration" section in
`docs/CoreToGOTO_Gaps.md`. -/
structure ArchConfig where
  arch : String := "arm64"
  os : String := "macos"
  nullIsZero : Nat := 1
  alignment : Nat := 1
  boolWidth : Nat := 8
  charIsUnsigned : Nat := 0
  charWidth : Nat := 8
  shortIntWidth : Nat := 16
  intWidth : Nat := 32
  longIntWidth : Nat := 64
  longLongIntWidth : Nat := 64
  singleWidth : Nat := 32
  doubleWidth : Nat := 64
  longDoubleWidth : Nat := 64
  pointerWidth : Nat := 64
  wordSize : Nat := 32
  memoryOperandSize : Nat := 4
  wcharTWidth : Nat := 32
  wcharTIsUnsigned : Nat := 0
  endianness : Nat := 1
  deriving Inhabited

/-- Default configuration matching the current defaults.json (arm64/macOS/LP64). -/
def ArchConfig.default : ArchConfig := {}

-- Helper JSON builders

private def mkSourceLoc (file : String) (line : String) : Lean.Json :=
  Lean.Json.mkObj [
    ("file", Lean.Json.mkObj [("id", file)]),
    ("line", Lean.Json.mkObj [("id", line)]),
    ("working_directory", Lean.Json.mkObj [("id", "")])
  ]

private def signedBvType (width : Nat) (cType : String) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", "signedbv"),
    ("namedSub", Lean.Json.mkObj [
      ("#c_type", Lean.Json.mkObj [("id", cType)]),
      ("width", Lean.Json.mkObj [("id", toString width)])
    ])
  ]

private def constSignedBvType (width : Nat) (cType : String) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", "signedbv"),
    ("namedSub", Lean.Json.mkObj [
      ("#c_type", Lean.Json.mkObj [("id", cType)]),
      ("#constant", Lean.Json.mkObj [("id", "1")]),
      ("width", Lean.Json.mkObj [("id", toString width)])
    ])
  ]

private def unsignedBvType (width : Nat) (cType : String) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", "unsignedbv"),
    ("namedSub", Lean.Json.mkObj [
      ("#c_type", Lean.Json.mkObj [("id", cType)]),
      ("width", Lean.Json.mkObj [("id", toString width)])
    ])
  ]

private def constUnsignedBvType (width : Nat) (cType : String) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", "unsignedbv"),
    ("namedSub", Lean.Json.mkObj [
      ("#c_type", Lean.Json.mkObj [("id", cType)]),
      ("#constant", Lean.Json.mkObj [("id", "1")]),
      ("width", Lean.Json.mkObj [("id", toString width)])
    ])
  ]

private def integerType : Lean.Json := Lean.Json.mkObj [("id", "integer")]

private def boolType : Lean.Json := Lean.Json.mkObj [("id", "bool")]

private def emptyType : Lean.Json := Lean.Json.mkObj [("id", "empty")]

private def nilValue : Lean.Json := Lean.Json.mkObj [("id", "nil")]

private def pointerTo (sub : Lean.Json) (width : Nat) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", "pointer"),
    ("namedSub", Lean.Json.mkObj [("width", Lean.Json.mkObj [("id", toString width)])]),
    ("sub", Lean.Json.arr #[sub])
  ]

private def constPointerToEmpty (width : Nat) : Lean.Json :=
  pointerTo (Lean.Json.mkObj [
    ("id", "empty"),
    ("namedSub", Lean.Json.mkObj [("#constant", Lean.Json.mkObj [("id", "1")])])
  ]) width

/-- Integer constant value wrapped in a typecast to `integer` type. -/
private def integerConstValue (n : Nat) (file : String) (line : String) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", "typecast"),
    ("namedSub", Lean.Json.mkObj [("type", integerType)]),
    ("sub", Lean.Json.arr #[
      Lean.Json.mkObj [
        ("id", "constant"),
        ("namedSub", Lean.Json.mkObj [
          ("#base", Lean.Json.mkObj [("id", "10")]),
          ("#source_location", Lean.Json.mkObj [("id", ""), ("namedSub", mkSourceLoc file line)]),
          ("type", signedBvType 32 "signed_int"),
          ("value", Lean.Json.mkObj [("id", Nat.toDigits 16 n |> String.ofList)])
        ])
      ]
    ])
  ]

/-- String constant value as a pointer to a string-constant array. -/
private def stringConstValue (s : String) (file : String) (line : String)
    (ptrWidth : Nat) : Lean.Json :=
  let len := s.length + 1
  let arrayType := Lean.Json.mkObj [
    ("id", "array"),
    ("namedSub", Lean.Json.mkObj [
      ("size", Lean.Json.mkObj [
        ("id", "constant"),
        ("namedSub", Lean.Json.mkObj [
          ("type", signedBvType ptrWidth "signed_long_int"),
          ("value", Lean.Json.mkObj [("id", Nat.toDigits 16 len |> String.ofList)])
        ])
      ])
    ]),
    ("sub", Lean.Json.arr #[signedBvType 8 "char"])
  ]
  Lean.Json.mkObj [
    ("id", "address_of"),
    ("namedSub", Lean.Json.mkObj [
      ("#source_location", Lean.Json.mkObj [("id", ""), ("namedSub", mkSourceLoc file line)]),
      ("type", pointerTo (signedBvType 8 "char") ptrWidth)
    ]),
    ("sub", Lean.Json.arr #[
      Lean.Json.mkObj [
        ("id", "index"),
        ("namedSub", Lean.Json.mkObj [
          ("type", signedBvType 8 "char")
        ]),
        ("sub", Lean.Json.arr #[
          Lean.Json.mkObj [
            ("id", "string_constant"),
            ("namedSub", Lean.Json.mkObj [
              ("#source_location", Lean.Json.mkObj [("id", ""), ("namedSub", mkSourceLoc file line)]),
              ("type", arrayType),
              ("value", Lean.Json.mkObj [("id", s)])
            ])
          ],
          Lean.Json.mkObj [
            ("id", "constant"),
            ("namedSub", Lean.Json.mkObj [
              ("type", signedBvType ptrWidth "signed_long_int"),
              ("value", Lean.Json.mkObj [("id", "0")])
            ])
          ]
        ])
      ]
    ])
  ]

/-- Signed BV constant. -/
private def signedBvConst (val : String) (width : Nat) (cType : String)
    (file : String) (line : String) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", "constant"),
    ("namedSub", Lean.Json.mkObj [
      ("#base", Lean.Json.mkObj [("id", "10")]),
      ("#source_location", Lean.Json.mkObj [("id", ""), ("namedSub", mkSourceLoc file line)]),
      ("type", signedBvType width cType),
      ("value", Lean.Json.mkObj [("id", val)])
    ])
  ]

/-- Unsigned BV constant. -/
private def unsignedBvConst (val : String) (width : Nat) (cType : String)
    (file : String) (line : String) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", "constant"),
    ("namedSub", Lean.Json.mkObj [
      ("#base", Lean.Json.mkObj [("id", "10")]),
      ("#source_location", Lean.Json.mkObj [("id", ""), ("namedSub", mkSourceLoc file line)]),
      ("type", unsignedBvType width cType),
      ("value", Lean.Json.mkObj [("id", val)])
    ])
  ]

/-- NULL pointer constant. -/
private def nullPointerConst (width : Nat) (file : String) (line : String) : Lean.Json :=
  let constEmpty := Lean.Json.mkObj [
    ("id", "empty"),
    ("namedSub", Lean.Json.mkObj [
      ("#constant", Lean.Json.mkObj [("id", "1")]),
      ("#source_location", Lean.Json.mkObj [("id", ""), ("namedSub", mkSourceLoc file line)])
    ])
  ]
  Lean.Json.mkObj [
    ("id", "constant"),
    ("namedSub", Lean.Json.mkObj [
      ("type", pointerTo constEmpty width),
      ("value", Lean.Json.mkObj [("id", "NULL")])
    ])
  ]

/-- Code (function) type with given parameters and void return. -/
private def voidCodeType (params : Array Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", "code"),
    ("namedSub", Lean.Json.mkObj [
      ("parameters", if params.isEmpty then Lean.Json.mkObj [("id", "")]
                     else Lean.Json.mkObj [("id", ""), ("sub", Lean.Json.arr params)]),
      ("return_type", emptyType)
    ])
  ]

/-- Code type returning bool with given parameters. -/
private def boolCodeType (params : Array Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", "code"),
    ("namedSub", Lean.Json.mkObj [
      ("parameters", Lean.Json.mkObj [("id", ""), ("sub", Lean.Json.arr params)]),
      ("return_type", boolType)
    ])
  ]

/-- A function parameter. -/
private def mkCodeParam (baseName : String) (ty : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", "parameter"),
    ("namedSub", Lean.Json.mkObj [
      ("#base_name", Lean.Json.mkObj [("id", baseName)]),
      ("#identifier", Lean.Json.mkObj [("id", "")]),
      ("type", ty)
    ])
  ]

/-- size_t type (unsigned, pointer-width). -/
private def sizeT (ptrWidth : Nat) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", "unsignedbv"),
    ("namedSub", Lean.Json.mkObj [
      ("#c_type", Lean.Json.mkObj [("id", "unsigned_long_int")]),
      ("#typedef", Lean.Json.mkObj [("id", "__CPROVER_size_t")]),
      ("width", Lean.Json.mkObj [("id", toString ptrWidth)])
    ])
  ]

/-- Generate architecture constant symbols. -/
private def architectureSymbols (cfg : ArchConfig) (moduleName : String)
    : List (String × CBMCSymbol) :=
  let file := "<builtin-architecture-strings>"
  let mkIntSym (name : String) (val : Nat) (line : String) : String × CBMCSymbol :=
    (name, {
      baseName := name, name := name, prettyName := name,
      mode := "C", module := moduleName,
      isLvalue := true, isStaticLifetime := true,
      prettyType := "integer",
      prettyValue := s!"(integer){val}",
      type := integerType,
      value := integerConstValue val file line
    })
  let mkStrSym (name : String) (val : String) (line : String) : String × CBMCSymbol :=
    (name, {
      baseName := name, name := name, prettyName := name,
      mode := "C", module := moduleName,
      isLvalue := true, isStaticLifetime := true,
      prettyType := "const char *",
      prettyValue := s!"\"{val}\"",
      type := pointerTo (constSignedBvType 8 "char") cfg.pointerWidth,
      value := stringConstValue val file line cfg.pointerWidth
    })
  [
    mkIntSym "__CPROVER_architecture_NULL_is_zero"       cfg.nullIsZero        "1",
    mkIntSym "__CPROVER_architecture_alignment"          cfg.alignment         "2",
    mkStrSym "__CPROVER_architecture_arch"               cfg.arch              "3",
    mkIntSym "__CPROVER_architecture_bool_width"         cfg.boolWidth         "4",
    mkIntSym "__CPROVER_architecture_char_is_unsigned"   cfg.charIsUnsigned    "5",
    mkIntSym "__CPROVER_architecture_char_width"         cfg.charWidth         "6",
    mkIntSym "__CPROVER_architecture_double_width"       cfg.doubleWidth       "7",
    mkIntSym "__CPROVER_architecture_endianness"         cfg.endianness        "8",
    mkIntSym "__CPROVER_architecture_int_width"          cfg.intWidth          "9",
    mkIntSym "__CPROVER_architecture_long_double_width"  cfg.longDoubleWidth   "10",
    mkIntSym "__CPROVER_architecture_long_int_width"     cfg.longIntWidth      "11",
    mkIntSym "__CPROVER_architecture_long_long_int_width" cfg.longLongIntWidth "12",
    mkIntSym "__CPROVER_architecture_memory_operand_size" cfg.memoryOperandSize "13",
    mkStrSym "__CPROVER_architecture_os"                 cfg.os                "14",
    mkIntSym "__CPROVER_architecture_pointer_width"      cfg.pointerWidth      "15",
    mkIntSym "__CPROVER_architecture_short_int_width"    cfg.shortIntWidth     "16",
    mkIntSym "__CPROVER_architecture_single_width"       cfg.singleWidth       "17",
    mkIntSym "__CPROVER_architecture_wchar_t_is_unsigned" cfg.wcharTIsUnsigned "18",
    mkIntSym "__CPROVER_architecture_wchar_t_width"      cfg.wcharTWidth       "19",
    mkIntSym "__CPROVER_architecture_word_size"          cfg.wordSize          "20"
  ]

/-- Generate built-in function symbols. -/
private def builtinFunctionSymbols (cfg : ArchConfig) (moduleName : String)
    : List (String × CBMCSymbol) :=
  let pw := cfg.pointerWidth
  let voidPtr := pointerTo emptyType pw
  let constCharPtr := pointerTo (signedBvType 8 "char") pw
  [
    -- __CPROVER_assert(bool assertion, const char *description)
    ("__CPROVER_assert", {
      baseName := "__CPROVER_assert", name := "__CPROVER_assert",
      prettyName := "__CPROVER_assert",
      mode := "C", module := "",
      isLvalue := true,
      prettyType := "void (__CPROVER_bool, const char *)",
      type := voidCodeType #[mkCodeParam "assertion" boolType, mkCodeParam "description" constCharPtr],
      value := nilValue
    }),
    -- __CPROVER_assume(bool assumption)
    ("__CPROVER_assume", {
      baseName := "__CPROVER_assume", name := "__CPROVER_assume",
      prettyName := "__CPROVER_assume",
      mode := "C", module := "",
      isLvalue := true,
      prettyType := "void (__CPROVER_bool)",
      type := voidCodeType #[mkCodeParam "assumption" boolType],
      value := nilValue
    }),
    -- __CPROVER_initialize(void)
    ("__CPROVER_initialize", {
      baseName := "__CPROVER_initialize", name := "__CPROVER_initialize",
      prettyName := "__CPROVER_initialize",
      mode := "C", module := moduleName,
      isLvalue := true,
      prettyType := "void (void)",
      type := voidCodeType #[],
      value := nilValue
    }),
    -- __CPROVER_assignable(void *ptr, size_t size, bool is_ptr_to_ptr)
    ("__CPROVER_assignable", {
      baseName := "__CPROVER_assignable", name := "__CPROVER_assignable",
      prettyName := "__CPROVER_assignable",
      mode := "C", module := moduleName,
      isLvalue := true,
      prettyType := "void (void *, __CPROVER_size_t, __CPROVER_bool)",
      type := voidCodeType #[mkCodeParam "ptr" voidPtr, mkCodeParam "size" (sizeT pw),
                              mkCodeParam "is_ptr_to_ptr" boolType],
      value := nilValue
    }),
    -- __CPROVER_object_whole(void *ptr)
    ("__CPROVER_object_whole", {
      baseName := "__CPROVER_object_whole", name := "__CPROVER_object_whole",
      prettyName := "__CPROVER_object_whole",
      mode := "C", module := moduleName,
      isLvalue := true,
      prettyType := "void (void *)",
      type := voidCodeType #[mkCodeParam "ptr" voidPtr],
      value := nilValue
    }),
    -- __CPROVER_object_upto(void *ptr, size_t size)
    ("__CPROVER_object_upto", {
      baseName := "__CPROVER_object_upto", name := "__CPROVER_object_upto",
      prettyName := "__CPROVER_object_upto",
      mode := "C", module := moduleName,
      isLvalue := true,
      prettyType := "void (void *, __CPROVER_size_t)",
      type := voidCodeType #[mkCodeParam "ptr" voidPtr, mkCodeParam "size" (sizeT pw)],
      value := nilValue
    }),
    -- __CPROVER_object_from(void *ptr)
    ("__CPROVER_object_from", {
      baseName := "__CPROVER_object_from", name := "__CPROVER_object_from",
      prettyName := "__CPROVER_object_from",
      mode := "C", module := moduleName,
      isLvalue := true,
      prettyType := "void (void *)",
      type := voidCodeType #[mkCodeParam "ptr" voidPtr],
      value := nilValue
    }),
    -- __CPROVER_freeable(void *ptr)
    ("__CPROVER_freeable", {
      baseName := "__CPROVER_freeable", name := "__CPROVER_freeable",
      prettyName := "__CPROVER_freeable",
      mode := "C", module := moduleName,
      isLvalue := true,
      prettyType := "void (void *)",
      type := voidCodeType #[mkCodeParam "ptr" voidPtr],
      value := nilValue
    }),
    -- __CPROVER_is_freeable(void *ptr) → bool
    ("__CPROVER_is_freeable", {
      baseName := "__CPROVER_is_freeable", name := "__CPROVER_is_freeable",
      prettyName := "__CPROVER_is_freeable",
      mode := "C", module := moduleName,
      isLvalue := true,
      prettyType := "__CPROVER_bool (void *)",
      type := boolCodeType #[mkCodeParam "ptr" voidPtr],
      value := nilValue
    }),
    -- __CPROVER_was_freed(void *ptr) → bool
    ("__CPROVER_was_freed", {
      baseName := "__CPROVER_was_freed", name := "__CPROVER_was_freed",
      prettyName := "__CPROVER_was_freed",
      mode := "C", module := moduleName,
      isLvalue := true,
      prettyType := "__CPROVER_bool (void *)",
      type := boolCodeType #[mkCodeParam "ptr" voidPtr],
      value := nilValue
    })
  ]

/-- Generate built-in variable and type symbols. -/
private def builtinVariableSymbols (cfg : ArchConfig) (moduleName : String)
    : List (String × CBMCSymbol) :=
  let pw := cfg.pointerWidth
  let file := "<built-in-additions>"
  [
    -- __CPROVER_size_t (type alias)
    ("__CPROVER_size_t", {
      baseName := "__CPROVER_size_t", name := "__CPROVER_size_t",
      prettyName := "__CPROVER_size_t",
      mode := "C", module := moduleName,
      isType := true, isMacro := true, isFileLocal := true, isThreadLocal := true,
      prettyType := "__CPROVER_size_t",
      type := sizeT pw,
      value := nilValue
    }),
    -- __CPROVER_rounding_mode : signed int = 0
    ("__CPROVER_rounding_mode", {
      baseName := "__CPROVER_rounding_mode", name := "__CPROVER_rounding_mode",
      prettyName := "__CPROVER_rounding_mode",
      mode := "C", module := moduleName,
      isLvalue := true, isStaticLifetime := true, isThreadLocal := true,
      prettyType := "signed int", prettyValue := "0",
      type := signedBvType cfg.intWidth "signed_int",
      value := signedBvConst "0" cfg.intWidth "signed_int" file "16"
    }),
    -- __CPROVER_constant_infinity_uint : const unsigned int
    ("__CPROVER_constant_infinity_uint", {
      baseName := "__CPROVER_constant_infinity_uint",
      name := "__CPROVER_constant_infinity_uint",
      prettyName := "__CPROVER_constant_infinity_uint",
      mode := "C", module := moduleName,
      isLvalue := true, isStaticLifetime := true,
      prettyType := "const unsigned int",
      type := constUnsignedBvType cfg.intWidth "unsigned_int",
      value := nilValue
    }),
    -- __CPROVER_dead_object : const void * = NULL
    ("__CPROVER_dead_object", {
      baseName := "__CPROVER_dead_object", name := "__CPROVER_dead_object",
      prettyName := "__CPROVER_dead_object",
      mode := "C", module := moduleName,
      isLvalue := true, isStaticLifetime := true,
      prettyType := "const void *", prettyValue := "NULL",
      type := constPointerToEmpty pw,
      value := nullPointerConst pw file "8"
    }),
    -- __CPROVER_deallocated : const void * = NULL
    ("__CPROVER_deallocated", {
      baseName := "__CPROVER_deallocated", name := "__CPROVER_deallocated",
      prettyName := "__CPROVER_deallocated",
      mode := "C", module := moduleName,
      isLvalue := true, isStaticLifetime := true,
      prettyType := "const void *", prettyValue := "NULL",
      type := constPointerToEmpty pw,
      value := nullPointerConst pw file "9"
    }),
    -- __CPROVER_memory_leak : const void * = NULL
    ("__CPROVER_memory_leak", {
      baseName := "__CPROVER_memory_leak", name := "__CPROVER_memory_leak",
      prettyName := "__CPROVER_memory_leak",
      mode := "C", module := moduleName,
      isLvalue := true, isStaticLifetime := true,
      prettyType := "const void *", prettyValue := "NULL",
      type := constPointerToEmpty pw,
      value := nullPointerConst pw file "10"
    }),
    -- __CPROVER_max_malloc_size : size_t = 0x80000000000000 (2^55)
    ("__CPROVER_max_malloc_size", {
      baseName := "__CPROVER_max_malloc_size", name := "__CPROVER_max_malloc_size",
      prettyName := "__CPROVER_max_malloc_size",
      mode := "C", module := moduleName,
      isLvalue := true, isStaticLifetime := true, isThreadLocal := true,
      prettyType := "__CPROVER_size_t",
      prettyValue := "36028797018963968ul",
      type := sizeT pw,
      value := unsignedBvConst "80000000000000" pw "unsigned_long_int" file "12"
    }),
    -- __CPROVER_memory : extern unsigned char[∞]
    ("__CPROVER_memory", {
      baseName := "__CPROVER_memory", name := "__CPROVER_memory",
      prettyName := "__CPROVER_memory",
      mode := "C", module := moduleName,
      isLvalue := true, isStaticLifetime := true, isExtern := true,
      prettyType := "unsigned char [INFINITY()]",
      type := Lean.Json.mkObj [
        ("id", "array"),
        ("namedSub", Lean.Json.mkObj [
          ("#index_type", signedBvType pw "signed_long_int"),
          ("size", Lean.Json.mkObj [
            ("id", "infinity"),
            ("namedSub", Lean.Json.mkObj [
              ("type", signedBvType pw "signed_long_int")
            ])
          ])
        ]),
        ("sub", Lean.Json.arr #[unsignedBvType 8 "unsigned_char"])
      ],
      value := nilValue
    })
  ]

/-- Generate all default symbols for a CBMC symbol table.
    `moduleName` should match the base name of the program being verified. -/
def defaultSymbols (cfg : ArchConfig := .default) (moduleName : String := "")
    : List (String × CBMCSymbol) :=
  architectureSymbols cfg moduleName ++
  builtinFunctionSymbols cfg moduleName ++
  builtinVariableSymbols cfg moduleName

/-- Add default symbols to a symbol-table object and wrap in `{"symbolTable": ...}`.
    Use this instead of manually iterating over `defaultSymbols` at each call site. -/
def wrapSymtab (symtabObj : Std.TreeMap.Raw String Lean.Json)
    (moduleName : String) (cfg : ArchConfig := .default) : Lean.Json :=
  let obj := (defaultSymbols cfg moduleName).foldl
    (fun acc (k, v) => acc.insert k (Lean.toJson v)) symtabObj
  Lean.Json.mkObj [("symbolTable", Lean.Json.obj obj)]

end -- public section

end CProverGOTO
