/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.DDM.Integration.Lean

namespace Strata.Python
#load_dialect "../../../Tools/Python/dialects/Python.dialect.st.ion"

#strata_gen Python

instance {α} [Inhabited α] : ToString (Strata.Python.constant α) where
  toString s := toString (eformat s.toAst)

deriving instance DecidableEq for operator

def alias.ann {α} : alias α → α
| .mk_alias ann _ _ => ann

def alias.name {α} : alias α → String
| .mk_alias _ name _ => name.val

def alias.asname {α} : alias α → Option String
| .mk_alias _ _ asname => asname.val.map (·.val)

def constant.ann {α} : constant α → α
| ConTrue ann .. => ann
| ConFalse ann .. => ann
| ConPos ann .. => ann
| ConNeg ann .. => ann
| ConString ann .. => ann
| ConFloat ann .. => ann
| ConComplex ann .. => ann
| ConNone ann .. => ann
| ConEllipsis ann .. => ann
| ConBytes ann .. => ann

def keyword.ann {α} : keyword α → α
| .mk_keyword ann _ _ => ann

def keyword.arg {α} : keyword α → Ann (Option (Ann String α)) α
| .mk_keyword _ arg _ => arg

def keyword.value {α} : keyword α → expr α
| .mk_keyword _ _ value => value

namespace int

def value {α} (i : int α) : Int :=
  match i with
  | IntPos _ n => n.val
  | IntNeg _ n => - (n.val : Int)

end int


namespace expr

def ann {α} : expr α → α
| BoolOp a .. => a
| NamedExpr a .. => a
| BinOp a .. => a
| UnaryOp a .. => a
| Lambda a .. => a
| IfExp a .. => a
| Dict a .. => a
| Set a .. => a
| ListComp a .. => a
| SetComp a .. => a
| DictComp a .. => a
| GeneratorExp a .. => a
| Await a .. => a
| Yield a .. => a
| YieldFrom a .. => a
| Compare a .. => a
| Call a .. => a
| FormattedValue a .. => a
| Interpolation a .. => a
| JoinedStr a .. => a
| TemplateStr a .. => a
| Constant a .. => a
| Attribute a .. => a
| Subscript a .. => a
| Starred a .. => a
| Name a .. => a
| List a .. => a
| Tuple a .. => a
| Slice a .. => a

end expr

namespace stmt

def ann {α} : stmt α → α
| AnnAssign a .. => a
| Assert a .. => a
| Assign a .. => a
| AsyncFor a .. => a
| AsyncFunctionDef a .. => a
| AsyncWith a .. => a
| AugAssign a .. => a
| Break a .. => a
| ClassDef a .. => a
| Continue a .. => a
| Delete a .. => a
| Expr a .. => a
| For a .. => a
| FunctionDef a .. => a
| Global a .. => a
| If a .. => a
| Import a .. => a
| ImportFrom a .. => a
| Match a .. => a
| Nonlocal a .. => a
| Pass a .. => a
| Raise a .. => a
| Return a .. => a
| Try a .. => a
| TryStar a .. => a
| TypeAlias a .. => a
| While a .. => a
| With a .. => a

end stmt

instance {α} [Inhabited α] : ToString (Strata.Python.expr α) where
  toString s := toString (eformat s.toAst)

def stmt.format {α} [Inhabited α] : ToString (Strata.Python.stmt α) where
  toString s := toString (mformat s.toAst (.ofDialects Python_map) .empty |>.format)

instance {α} [Inhabited α] : ToString (Strata.Python.stmt α) where
  toString s := toString (mformat s.toAst (.ofDialects Python_map) .empty |>.format)

end Strata.Python
