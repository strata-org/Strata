/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Integration.Lean
public import Strata.Languages.Python.Specs.Decls

import Strata.DDM.AST
import Strata.DDM.Util.ByteArray
import Strata.DDM.Format
import Strata.DDM.BuiltinDialects.Init
public import Strata.DDM.Integration.Lean.OfAstM
import Strata.DDM.Ion

public section
namespace Strata.Python.Specs
namespace DDM

#dialect
dialect PythonSpecs;

category Int;
op natInt (x : Num) : Int => x;
op negSuccInt (x : Num) : Int => "-" x;

category SpecType;
category FieldDecl;

op mkFieldDecl(name : Ident, fieldType : SpecType) : FieldDecl => name " : " fieldType;

op typeIdentNoArgs (x : Str) : SpecType => "ident" "(" x ")";
op typeIdent (x : Str, y : CommaSepBy SpecType) : SpecType => "ident" "(" x ", " y ")";
op typeClassNoArgs (x : Ident) : SpecType => "class" "(" x ")";
op typeClass (x : Ident, y : CommaSepBy SpecType) : SpecType => "class" "(" x ", " y ")";
op typeIntLiteral (x : Int) : SpecType => x;
op typeStringLiteral (x : Str) : SpecType => x;
op typeUnion (args : CommaSepBy SpecType) : SpecType => "union" "(" args ")";
op typeTypedDict (fields : CommaSepBy FieldDecl, isTotal : Bool): SpecType =>
  "dict" "(" fields ")" "[" "isTotal" "=" isTotal "]";

category ArgDecl;
op mkArgDecl (name : Ident, argType : SpecType, hasDefault : Bool) : ArgDecl =>
  name " : " argType " [" "hasDefault" ": " hasDefault "]\n";

category FunDecl;
op mkFunDecl (name : Str,
              args : Seq ArgDecl,
              kwonly : Seq ArgDecl,
              returnType : SpecType,
              isOverload : Bool) : FunDecl =>
  "function " name "{\n"
  indent(2,
    "args" ": " "[\n"
    indent(2, args)
    "]\n"
    "kwonly" ": " "[\n"
    indent(2, kwonly)
    "]\n"
    "return" ": " returnType "\n"
    "overload" ": " isOverload "\n")
  "}\n";

op externTypeDecl (name : Str, source : Str) : Command =>
  "extern " name " from " source ";\n";
op classDef (name : Str, methods : Seq FunDecl) : Command =>
  "class " name " {\n"
  indent(2, methods)
  "}\n";
op functionDecl (decl : FunDecl) : Command => decl;
op typeDef (name : Str, definition : SpecType) : Command =>
  "type " name " = " definition "\n";
#end

#strata_gen PythonSpecs

abbrev Signature := Command

end DDM

/-- Converts a Python identifier to an annotated string for DDM serialization. -/
private def PythonIdent.toDDM (d : PythonIdent) : Ann String SourceRange :=
  ⟨.none, toString d⟩

/-- Converts a Lean `Int` to the DDM representation which separates natural and negative cases. -/
private def toDDMInt {α} (ann : α) (i : Int) : DDM.Int α :=
  match i with
  | .ofNat n => .natInt ann ⟨ann, n⟩
  | .negSucc n => .negSuccInt ann ⟨ann, n⟩

private def DDM.Int.ofDDM : DDM.Int α → _root_.Int
| .natInt _ ⟨_, n⟩ => .ofNat n
| .negSuccInt _ ⟨_, n⟩ => .negSucc n

mutual

private def SpecAtomType.toDDM (d : SpecAtomType) (loc : SourceRange := .none) : DDM.SpecType SourceRange :=
  match d with
  | .ident nm args =>
    if args.isEmpty then
      .typeIdentNoArgs loc nm.toDDM
    else
      .typeIdent loc nm.toDDM ⟨.none, args.map (·.toDDM)⟩
  | .pyClass name args =>
    if args.isEmpty then
      .typeClassNoArgs loc ⟨.none, name⟩
    else
      .typeClass loc ⟨.none, name⟩ ⟨.none, args.map (·.toDDM)⟩
  | .intLiteral i => .typeIntLiteral loc (toDDMInt .none i)
  | .stringLiteral v => .typeStringLiteral loc ⟨.none, v⟩
  | .typedDict fields types isTotal =>
    assert! fields.size = types.size
    let argc := types.size
    let a := Array.ofFn fun (⟨i, ilt⟩ : Fin argc) =>
      .mkFieldDecl .none ⟨.none, fields[i]!⟩ types[i].toDDM
    .typeTypedDict loc ⟨.none, a⟩ ⟨.none, isTotal⟩
termination_by sizeOf d

private def SpecType.toDDM (d : SpecType) : DDM.SpecType SourceRange :=
  assert! d.atoms.size > 0
  if p : d.atoms.size = 1 then
    d.atoms[0].toDDM (loc := d.loc)
  else
    .typeUnion d.loc ⟨.none, d.atoms.map (·.toDDM)⟩
termination_by sizeOf d
decreasing_by
  all_goals {
    cases d
    decreasing_tactic
  }

end

private def Arg.toDDM (d : Arg) : DDM.ArgDecl SourceRange :=
  .mkArgDecl .none ⟨.none, d.name⟩ d.type.toDDM ⟨.none, d.hasDefault⟩

private def FunctionDecl.toDDM (d : FunctionDecl) : DDM.FunDecl SourceRange :=
  .mkFunDecl
    d.loc
    (name := .mk d.nameLoc d.name)
    (args := ⟨.none, d.args.args.map (·.toDDM)⟩)
    (kwonly := ⟨.none, d.args.kwonly.map (·.toDDM)⟩)
    (returnType := d.returnType.toDDM)
    (isOverload := ⟨.none, d.isOverload⟩)

private def Signature.toDDM (sig : Signature) : DDM.Signature SourceRange :=
  match sig with
  | .externTypeDecl name source =>
    .externTypeDecl .none ⟨.none, name⟩ source.toDDM
  | .classDef d =>
    .classDef d.loc (.mk .none d.name) ⟨.none, d.methods.map (·.toDDM)⟩
  | .functionDecl d =>
    .functionDecl d.loc d.toDDM
  | .typeDef d =>
    .typeDef d.loc (.mk d.nameLoc d.name) d.definition.toDDM

private def DDM.SpecType.fromDDM (d : DDM.SpecType SourceRange) : Specs.SpecType :=
  match d with
  | .typeClassNoArgs loc ⟨_, cl⟩ =>
    .ofAtom loc <| .pyClass cl #[]
  | .typeClass loc ⟨_, cl⟩ ⟨_, args⟩ =>
    let a := args.map (·.fromDDM)
    .ofAtom loc <| .pyClass cl a
  | .typeIdentNoArgs loc ⟨_, ident⟩ =>
    if let some pyIdent := PythonIdent.ofString ident then
      .ident loc pyIdent #[]
    else
      panic! "Bad identifier"
  | .typeIdent loc ⟨_, ident⟩ ⟨_, args⟩ =>
    let a := args.map (·.fromDDM)
    if let some pyIdent := PythonIdent.ofString ident then
      .ident loc pyIdent a
    else
      panic! "Bad identifier"
  | .typeIntLiteral loc i => .ofAtom loc <| .intLiteral i.ofDDM
  | .typeStringLiteral loc ⟨_, s⟩ => .ofAtom loc <| .stringLiteral s
  | .typeTypedDict loc ⟨_, fields⟩ ⟨_, isTotal⟩ =>
    let names := fields.map fun (.mkFieldDecl _ ⟨_, name⟩ _) => name
    let types := fields.attach.map fun ⟨.mkFieldDecl _ _ tp, mem⟩ => tp.fromDDM
    .ofAtom loc <| .typedDict names types isTotal
  | .typeUnion loc ⟨_, args⟩ =>
    if p : args.size > 0 then
      args.attach.foldl (init := args[0].fromDDM) (start := 1)
        fun a ⟨b, mem⟩ => SpecType.union loc a b.fromDDM
    else
      panic! "Expected non-empty union"
termination_by sizeOf d
decreasing_by
  · decreasing_tactic
  · decreasing_tactic
  · rename_i _ ann nm
    have szp : 1 + sizeOf ann + sizeOf nm + sizeOf tp < sizeOf fields :=
       Array.sizeOf_lt_of_mem mem
    decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic

private def DDM.ArgDecl.fromDDM (d : DDM.ArgDecl SourceRange) : Specs.Arg :=
  let .mkArgDecl _ ⟨_, name⟩ type ⟨_, hasDefault⟩ := d
  {
    name := name
    type := type.fromDDM
    hasDefault := hasDefault
  }

private def DDM.FunDecl.fromDDM (d : DDM.FunDecl SourceRange) : Specs.FunctionDecl :=
  let .mkFunDecl loc ⟨nameLoc, name⟩ ⟨_, args⟩ ⟨_, kwonly⟩
                 returnType ⟨_, isOverload⟩ := d
  {
    loc := loc
    nameLoc := nameLoc
    name := name
    args := {
      args := args.map (·.fromDDM)
      kwonly := kwonly.map (·.fromDDM)
    }
    returnType := returnType.fromDDM
    isOverload := isOverload
    preconditions := #[] -- FIXME
    postconditions := #[] -- FIXME
  }

private def DDM.Command.fromDDM (cmd : DDM.Command SourceRange) : Specs.Signature :=
  match cmd with
  | .externTypeDecl _ ⟨_, name⟩ ⟨_, ddmDefinition⟩ =>
    if let some definition := PythonIdent.ofString ddmDefinition then
      .externTypeDecl name definition
    else
      panic! "Extern type decl definition has bad format."
  | .classDef ann ⟨_, name⟩ ⟨_, methods⟩ =>
    let d : ClassDef := {
      loc := ann
      name := name
      methods := methods.map (·.fromDDM)
    }
    .classDef d
  | .functionDecl _ d => .functionDecl d.fromDDM
  | .typeDef loc ⟨nameLoc, name⟩ definition =>
    let d : TypeDef := {
      loc := loc
      nameLoc := nameLoc
      name := name
      definition := definition.fromDDM
    }
    .typeDef d

/-- Reads Python spec signatures from a DDM Ion file. -/
def readDDM (path : System.FilePath) : EIO String (Array Signature) := do
  let contents ←
        match ← IO.FS.readBinFile path |>.toBaseIO with
        | .ok r => pure r
        | .error msg => throw s!"Error reading {path}: {msg}"
  match Program.fromIon DDM.PythonSpecs_map DDM.PythonSpecs.name contents with
  | .ok pgm =>
    let r :=
          pgm.commands.mapM fun cmd => do
            let pySig ← DDM.Command.ofAst cmd
            return pySig.fromDDM
    match r with
    | .ok r => pure r
    | .error msg => throw msg
  | .error msg => throw msg

/-- Converts Python spec signatures to a DDM program for serialization. -/
def toDDMProgram (sigs : Array Signature) : Strata.Program := {
    dialects := DDM.PythonSpecs_map
    dialect := DDM.PythonSpecs.name
    commands := sigs.map fun s => s.toDDM.toAst
  }

/-- Writes Python spec signatures to a DDM Ion file. -/
def writeDDM (path : System.FilePath) (sigs : Array Signature) : IO Unit := do
  let pgm := toDDMProgram sigs
  IO.FS.writeBinFile path <| pgm.toIon

end Strata.Python.Specs
end
