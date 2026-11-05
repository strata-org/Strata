/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Cortex

meta section

namespace Cortex.Test

open Imperative

def exnTy : Lambda.LTy := .forAll [] (.tcons "Exn" [])

def composites : List CompositeDecl :=
  [ { name := "Exn", extending := [], fields := [] },
    { name := "IOExn", extending := ["Exn"],
      fields := [{ name := "code", ty := .forAll [] .int }] },
    { name := "Other", extending := [], fields := [] } ]

def e : Core.Expression.Expr := .fvar () "e" none

def body : Body :=
  { cfg :=
      { entry := "try",
        blocks :=
          [ ("try",
              { cmds := [.new "e" "IOExn" .empty, .throw e .empty],
                transfer := .goto "done" }),
            ("handler",
              { cmds := [.readField "c" e ⟨"IOExn", "code"⟩ .empty],
                transfer := .goto "done" }),
            ("done", { cmds := [], transfer := .finish .empty }) ] },
    handlers :=
      [ { covered := ["try"], catchType := some "Exn", binder := "e",
          target := "handler", md := .empty } ] }

def prog : Program :=
  { composites,
    procedures := [{ name := "main", inputs := [], outputs := [], throws := none, body := some body }] }

#guard prog.isSubtype "IOExn" "Exn"
#guard !prog.isSubtype "Exn" "IOExn"
#guard !prog.isSubtype "Other" "Exn"
#guard (body.handlerFor? prog "try" "IOExn").map (·.target) == some "handler"
#guard (body.handlerFor? prog "try" "Other").isNone
#guard (body.handlerFor? prog "handler" "IOExn").isNone
#guard (prog.findField? ⟨"IOExn", "code"⟩).map (·.name) == some "code"
#guard (prog.findField? ⟨"IOExn", "nope"⟩).isNone
#guard (prog.findField? ⟨"Other", "code"⟩).isNone
#guard prog.checkHandlers matches .ok ()

def badBody : Body :=
  { body with handlers := [{ covered := ["nope"], catchType := none, binder := "e",
                             target := "handler", md := .empty }] }

#guard ({ prog with procedures := [{ name := "main", inputs := [], outputs := [],
                                     throws := none, body := some badBody }] } : Program).checkHandlers
  matches .error "exception handler covers unknown block 'nope'"

def cid (n : String) : Core.Expression.Ident := ⟨n, ()⟩

def interpBody : Body :=
  { cfg :=
      { entry := "start",
        blocks :=
          [ ("start",
              { cmds := [.cmd (.init (cid "e") (.forAll [] (.tcons "IOExn" [])) .nondet .empty),
                         .cmd (.init (cid "c") (.forAll [] .int) .nondet .empty)],
                transfer := .goto "try" }),
            ("try",
              { cmds := [.new (cid "e") "IOExn" .empty,
                         .writeField e ⟨"IOExn", "code"⟩ (.const () (.intConst 7)) .empty,
                         .throw e .empty],
                transfer := .goto "done" }),
            ("handler",
              { cmds := [.readField (cid "c") e ⟨"IOExn", "code"⟩ .empty],
                transfer := .goto "done" }),
            ("done", { cmds := [], transfer := .finish .empty }) ] },
    handlers :=
      [ { covered := ["try"], catchType := some "Exn", binder := cid "e",
          target := "handler", md := .empty } ] }

def interpModule : Module :=
  { program := { composites, procedures :=
      [{ name := "main", inputs := [], outputs := [], throws := none, body := some interpBody }] } }

def interpResult : Option Core.Expression.Expr :=
  match interpModule.program.procedures with
  | p :: _ =>
    match Interp.runEntry interpModule 100 p with
    | .ok (.terminal ρ, _) => ρ.store (cid "c")
    | _ => none
  | [] => none

#guard interpResult == some (.const () (.intConst 7))

def refTy (n : String) : Lambda.LTy := .forAll [] (.tcons n [])
def intTy : Lambda.LTy := .forAll [] .int
def intC (i : Int) : Core.Expression.Expr := .const () (.intConst i)
def fv (n : String) : Core.Expression.Expr := .fvar () (cid n) none

def getBody (v : Int) : Body :=
  { cfg := { entry := "b", blocks := [("b", { cmds := [.cmd (.set (cid "r") (.det (intC v)) .empty)],
                                                transfer := .finish .empty })] },
    handlers := [] }

def getProc (owner : String) (v : Int) : Procedure :=
  { name := s!"{owner}$get", inputs := [(cid "this", refTy "Base")], outputs := [(cid "r", intTy)],
    throws := none, body := some (getBody v) }

def vcallBody (ty : String) : Body :=
  { cfg :=
      { entry := "start",
        blocks :=
          [ ("start",
              { cmds := [.cmd (.init (cid "o") (refTy ty) .nondet .empty),
                         .cmd (.init (cid "r") intTy .nondet .empty),
                         .new (cid "o") ty .empty,
                         .virtualCall [cid "r"] "Base" "get" [fv "o"] .empty],
                transfer := .finish .empty }) ] },
    handlers := [] }

def vcallModule (ty : String) : Module :=
  { program :=
      { composites := [ { name := "Base", extending := [], fields := [] },
                        { name := "Sub", extending := ["Base"], fields := [] } ],
        procedures :=
          [ { name := "main", inputs := [], outputs := [], throws := none, body := some (vcallBody ty) },
            getProc "Base" 1, getProc "Sub" 2 ] } }

def runMain (m : Module) : Option Core.Expression.Expr :=
  match m.program.procedures with
  | p :: _ =>
    match Interp.runEntry m 100 p with
    | .ok (.terminal ρ, _) => ρ.store (cid "r")
    | _ => none
  | [] => none

#guard (vcallModule "Sub").program.overriders "Base" "get" == ["Sub"]
#guard (vcallModule "Sub").program.dispatch "Base" "get" "Sub" == "Sub$get"
#guard (vcallModule "Sub").program.dispatch "Base" "get" "Base" == "Base$get"
#guard runMain (vcallModule "Sub") == some (intC 2)
#guard runMain (vcallModule "Base") == some (intC 1)

def lowered (ty : String) : Option Module :=
  match LowerDispatch.run (vcallModule ty) with
  | .ok m => some m
  | .error _ => none

def loweredCalls (m : Module) : List IRCmd :=
  m.program.procedures.flatMap fun p => match p.body with
    | some b => b.cfg.blocks.flatMap fun (_, blk) => blk.cmds.filter fun
      | .call .. | .virtualCall .. => true
      | _ => false
    | none => []

#guard (lowered "Sub").any fun m => !m.program.hasVirtualCall
#guard (lowered "Sub").any fun m =>
  let qs := (loweredCalls m).map fun
    | .call _ q _ _ => q
    | _ => ""
  qs.length == 2 && qs.contains "Sub$get" && qs.contains "Base$get"
#guard ((lowered "Sub").bind runMain) == some (intC 2)
#guard ((lowered "Base").bind runMain) == some (intC 1)

def diamonds (n : Nat) : Program :=
  { composites := { name := "C0", extending := [], fields := [] } ::
      (List.range n).flatMap fun i =>
        [ { name := s!"A{i+1}", extending := [s!"C{i}"], fields := [] },
          { name := s!"B{i+1}", extending := [s!"C{i}"], fields := [] },
          { name := s!"C{i+1}", extending := [s!"A{i+1}", s!"B{i+1}"], fields := [] } ],
    procedures := [] }

#guard (diamonds 1).ancestors "C1" == ["A1", "B1", "C0"]
#guard (diamonds 40).isSubtype "C40" "C0"
#guard !(diamonds 40).isSubtype "C40" "Other"
#guard ((diamonds 40).ancestors "C40").length == 120

end Cortex.Test

end
