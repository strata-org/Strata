import Strata.Languages.Core.StatementType
import Strata.Languages.Core.FunctionType
open Lambda Strata Core

/-- Probe: run the REAL Function.typeCheck unify path and read off `v_unify`'s range.
    Decisive question: can `v_unify` (= `S` at FunctionType.lean:87) map anything
    INTO a user typeArg? Build a minimal clean LContext (no `.default`). -/

def kts : KnownTypes :=
  makeKnownTypes [{ name := "arrow", metadata := 2 }, { name := "int", metadata := 0 }]

def cleanCtx : LContext CoreLParams :=
  { functions := default, datatypes := #[], knownTypes := kts, idents := default, rigidTypeVars := [] }

-- Polymorphic identity: f<a>(x:a) : a, body = x  (bvar 0 under the formal).
def fIdent : Function :=
  { name := ⟨"f", ()⟩, typeArgs := ["a"], isConstr := false,
    inputs := [(⟨"x", ()⟩, (.ftvar "a" : LMonoTy))],
    output := (.ftvar "a" : LMonoTy),
    body := some (.fvar () ⟨"x", ()⟩ none),
    attr := #[], concreteEval := none, axioms := [],
    isRecursive := false, preconditions := [], measure := none }

-- Re-run the typeCheck prefix to extract `S` (= v_unify) and inspect its range.
def probeUnify : String := Id.run do
  match LFunc.type fIdent with
  | .error e => return s!"type ERR: {e}"
  | .ok type =>
    match LTy.instantiateWithCheck (T := CoreLParams) type cleanCtx TEnv.default with
    | .error e => return s!"inst ERR: {e}"
    | .ok (monoty, Env1) =>
      let numInputs := fIdent.inputs.keys.length
      let monotys := monoty.destructArrow
      let remaining := monotys.drop numInputs
      let output_mty : LMonoTy :=
        let last := remaining.getLast?.getD (monotys.getLast?.getD (.ftvar "BUG"))
        LMonoTy.mkArrow' last remaining.dropLast
      let newTypeArgs := monoty.freeVars.eraseDups
      let newInputs := fIdent.inputs.keys.zip (monotys.take numInputs)
      let func2 : Function := { fIdent with typeArgs := newTypeArgs, inputs := newInputs, output := output_mty }
      let Env2 := (Env1.pushEmptyContext).addInNewestContext (LFunc.inputMonoSignature func2)
      match fIdent.body with
      | none => return "no body"
      | some body =>
        match LExpr.resolve cleanCtx Env2 body with
        | .error e => return s!"resolve ERR: {e}"
        | .ok (bodya, Env3) =>
          let bodyty := bodya.toLMonoTy
          match Constraints.unify [(func2.output, bodyty)] (TEnv.stateSubstInfo Env3) with
          | .error _ => return "unify ERR"
          | .ok S =>
            return s!"monoty={repr monoty}\noutput_mty={repr output_mty}\nbodyty={repr bodyty}\n"
                    ++ s!"v_unify.subst = {repr S.subst}\nrange freeVars = {repr (Subst.freeVars S.subst)}\n"
                    ++ s!"keys = {repr (Maps.keys S.subst)}\nuser typeArgs = {repr fIdent.typeArgs}"

#eval probeUnify

-- Generalized probe over an arbitrary Function, returning v_unify range + keys.
def runUnify (f : Function) : String := Id.run do
  match LFunc.type f with
  | .error _ => return "type ERR"
  | .ok type =>
    match LTy.instantiateWithCheck (T := CoreLParams) type cleanCtx TEnv.default with
    | .error _ => return "inst ERR"
    | .ok (monoty, Env1) =>
      let numInputs := f.inputs.keys.length
      let monotys := monoty.destructArrow
      let remaining := monotys.drop numInputs
      let last := remaining.getLast?.getD (monotys.getLast?.getD (.ftvar "BUG"))
      let output_mty := LMonoTy.mkArrow' last remaining.dropLast
      let func2 : Function := { f with typeArgs := monoty.freeVars.eraseDups,
                                       inputs := f.inputs.keys.zip (monotys.take numInputs), output := output_mty }
      let Env2 := (Env1.pushEmptyContext).addInNewestContext (LFunc.inputMonoSignature func2)
      match f.body with
      | none => return "no body"
      | some body =>
        match LExpr.resolve cleanCtx Env2 body with
        | .error _ => return "resolve ERR"
        | .ok (bodya, Env3) =>
          match Constraints.unify [(func2.output, bodya.toLMonoTy)] (TEnv.stateSubstInfo Env3) with
          | .error _ => return "unify ERR"
          | .ok S =>
            let rangeFv := Subst.freeVars S.subst
            let userArgs := f.typeArgs
            let clash := rangeFv.filter (· ∈ userArgs)
            return s!"f={f.name.1}: v_unify range={repr rangeFv} keys={repr (Maps.keys S.subst)} "
                    ++ s!"userArgs={repr userArgs} CLASH={repr clash}"

-- Case A: f<a>(x:a):a, body = x  (identity)
-- Case B: f<a>(x:a):a, body = (λ z:a. z) x   -- forces unify through an abs
def fB : Function :=
  { fIdent with body := some (.app () (.abs () "z" (some (.ftvar "a")) (.bvar () 0)) (.fvar () ⟨"x",()⟩ none)) }
-- Case C: f<a b>(x:a)(y:b):a, body = x
def fC : Function :=
  { name := ⟨"fc", ()⟩, typeArgs := ["a","b"], isConstr := false,
    inputs := [(⟨"x",()⟩, (.ftvar "a":LMonoTy)), (⟨"y",()⟩, (.ftvar "b":LMonoTy))],
    output := (.ftvar "a":LMonoTy), body := some (.fvar () ⟨"x",()⟩ none),
    attr := #[], concreteEval := none, axioms := [], isRecursive := false, preconditions := [], measure := none }

#eval runUnify fIdent
#eval runUnify fB
#eval runUnify fC

-- ADVERSARIAL: try to force a user typeArg into v_unify's range.
-- D: f<a>(x:a):a, body annotated with the typeArg `a` itself: (λz:a.z) applied — z:a forces a?
def fD : Function :=
  { fIdent with body := some (.abs () "z" (some (.ftvar "a")) (.bvar () 0)) }  -- output would be a→a vs a: mismatch
-- E: higher-order f<a>(x:a):(a→a), body = λz:a. x   (returns a function in `a`)
def fE : Function :=
  { name := ⟨"fe",()⟩, typeArgs := ["a"], isConstr := false,
    inputs := [(⟨"x",()⟩,(.ftvar "a":LMonoTy))],
    output := (.tcons "arrow" [.ftvar "a", .ftvar "a"] : LMonoTy),
    body := some (.abs () "z" (some (.ftvar "a")) (.fvar () ⟨"x",()⟩ none)),
    attr := #[], concreteEval := none, axioms := [], isRecursive := false, preconditions := [], measure := none }
-- F: f<a>(x:a):int, body annotated z:a but returns int constant — unify int with output
def fF : Function :=
  { name := ⟨"ff",()⟩, typeArgs := ["a"], isConstr := false,
    inputs := [(⟨"x",()⟩,(.ftvar "a":LMonoTy))], output := (.tcons "int" []:LMonoTy),
    body := some (.intConst () 5),
    attr := #[], concreteEval := none, axioms := [], isRecursive := false, preconditions := [], measure := none }

#eval runUnify fD
#eval runUnify fE
#eval runUnify fF

-- ★ THE PREDICTED COUNTEREXAMPLE: output annotation instantiated to $__ty,
-- but body type stays user `a` (never unified against gen) ⟹ outer unify binds $__ty ↦ a.
-- f<a>(d:a):(a→a), body = λz:a. z   (input d:a just to satisfy non-empty; body ignores it)
def fCEX : Function :=
  { name := ⟨"cex",()⟩, typeArgs := ["a"], isConstr := false,
    inputs := [(⟨"d",()⟩,(.ftvar "a":LMonoTy))],
    output := (.tcons "arrow" [.ftvar "a", .ftvar "a"] : LMonoTy),
    body := some (.abs () "z" (some (.ftvar "a")) (.bvar () 0)),  -- λz:a. z  : a→a, annotation a survives
    attr := #[], concreteEval := none, axioms := [], isRecursive := false, preconditions := [], measure := none }

#eval runUnify fCEX

-- WHY (b) holds: does LMonoTy.instantiateWithCheck rename a FREE annotation var `a` to fresh?
def probeAnnInst : String :=
  match LMonoTy.instantiateWithCheck (.ftvar "a") cleanCtx TEnv.default with
  | .error _ => "ann inst ERR"
  | .ok (mty, _) => s!"instantiateWithCheck (ftvar a) = {repr mty}"
#eval probeAnnInst
