import Strata.DL.Call.CallCmd
import Strata.DL.HigherOrder.HigherOrder

namespace CallHigherOrder

open HigherOrder
open Call

-- Define our expression system using HigherOrder dialect
abbrev CallHigherOrderStrataExpression : Imperative.PureExpr := HigherOrderStrataExpression

-- Generic statements that combine Call dialect with HigherOrder expressions
abbrev CallHigherOrderStrataStatement := Imperative.Stmt HigherOrderStrataExpression (CallCmd HigherOrderStrataExpression)
abbrev CallHigherOrderStrataStatements := List CallHigherOrderStrataStatement
abbrev CallHigherOrderStrataCommand := CallCmd HigherOrderStrataExpression

-- CallHigherOrder-specific function and translation context
abbrev CallHigherOrderStrataFunction := Generic.StrataFunction CallHigherOrderStrataStatement Lambda.LMonoTy
abbrev CallHigherOrderTranslationContext := Generic.TranslationContext CallHigherOrderStrataStatement Lambda.LMonoTy

end CallHigherOrder
