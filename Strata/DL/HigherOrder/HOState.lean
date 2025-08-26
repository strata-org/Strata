import Strata.DL.Lambda.LState
import Strata.DL.Lambda.IntBoolFactory

namespace HigherOrder

-- State for higher-order function evaluation (extends Lambda state)
structure HOState where
  lambdaState : Lambda.LState String

-- Create empty higher-order state with basic Lambda factory
def HOState.empty : HOState :=
  let lambdaState := Lambda.LState.init
  -- Add IntBool factory for arithmetic and boolean operations
  let lambdaStateWithFactory := match lambdaState.addFactory Lambda.IntBoolFactory with
    | .ok state => state
    | .error _ => lambdaState  -- Fallback to basic state if factory addition fails
  { lambdaState := lambdaStateWithFactory }

-- Helper function to add a variable to HOState (Lambda state)
private def addToHOState (state : HOState) (name : String) (ty : Option Lambda.LMonoTy) (expr : Lambda.LExpr String) : HOState :=
  -- Add to the top scope (most recent scope)
  match state.lambdaState.state with
  | [] =>
    -- No scopes exist, create a new one
    { state with lambdaState := { state.lambdaState with state := [[(name, (ty, expr))]] } }
  | topScope :: restScopes =>
    -- Add to the top scope
    let newTopScope := topScope.insert name (ty, expr)
    { state with lambdaState := { state.lambdaState with state := newTopScope :: restScopes } }

-- Helper function to set variable in HOState
def HOState.setVar (state : HOState) (name : String) (value : Lambda.LExpr String) : HOState :=
  -- Store Lambda expression directly in Lambda state
  addToHOState state name none value

-- Helper function to get variable from HOState
def HOState.getVar (state : HOState) (name : String) : Option (Lambda.LExpr String) :=
  -- Search through the scope stack (most recent first)
  state.lambdaState.state.findSome? fun scope =>
    match scope.find? name with
    | some (_, expr) => some expr
    | none => none

-- Helper function to get variable type from HOState
def HOState.getVarType (state : HOState) (name : String) : Option Lambda.LMonoTy :=
  -- Search through the scope stack (most recent first)
  state.lambdaState.state.findSome? fun scope =>
    match scope.find? name with
    | some (some ty, _) => some ty
    | some (none, _) => none
    | none => none

end HigherOrder
