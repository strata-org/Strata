import Strata.DDM.Elab
import Strata.DDM.AST

import Strata.Languages.Boogie.Boogie
import StrataTest.Internal.FunctionSignatures
import Strata.Languages.Python.PythonSSADialect

namespace Strata
open Lambda.LTy.Syntax


-- #print PythonSSA.Value
-- #print PythonSSA.Bool
-- #print PythonSSA.ValueList
-- #print PythonSSA.JumpTarget
-- #print PythonSSA.ExcHandler
-- #print PythonSSA.DictBinding
-- #print PythonSSA.Reg
-- #print PythonSSA.DictEntries
-- #print PythonSSA.Statement
-- #print PythonSSA.TermStatement
#print PythonSSA.Block

def toPyCommands (a : Array Operation) : Array (PythonSSA.Command SourceRange) :=
  a.map (λ op => match PythonSSA.Command.ofAst op with
    | .error e => panic! s!"Failed to translate to Python.Command: {e}"
    | .ok cmd => cmd)

def PyStmtToBoogie (s : PythonSSA.Statement SourceRange) : List Boogie.Statement :=
  match s with
  | .mk_tuple l reg SourceRange => [.assume "mk_tuple" (.const "true" mty[bool])]
  | _ => [.assume "other" (.const "true" mty[bool])]


def PyBlockArrayToBoogie (blocks : (Array (PythonSSA.Block SourceRange))) : List Boogie.Statement := Id.run do
  let mut counter := 0
  let mut ret : List Boogie.Statement := []
  for b in blocks do
    let b_stmt : Boogie.Statement := match b with
    | .mk_block SourceRange idx inputs stmts t_stmt => (Imperative.Stmt.block s!"block_{counter}" {ss := stmts.val.toList.flatMap PyStmtToBoogie})
    ret := b_stmt :: ret
    counter := counter + 1
  ret.reverse

def PyBodyToBoogie (body: Ann (Array (PythonSSA.Block SourceRange)) SourceRange) : Boogie.Decl :=
  .proc {header := {name := "__main__", typeArgs:= [], inputs := [], outputs := []},
         spec := {modifies := [], preconditions:= [], postconditions := []},
         body := PyBlockArrayToBoogie body.val}

def PyCommandToBoogie (c : PythonSSA.Command SourceRange) : Boogie.Decl :=
  match c with
  | PythonSSA.Command.mk_function _name _args _types body => PyBodyToBoogie body

def pythonSSAToBoogie (pgm: Strata.Program): Boogie.Program :=
  let pyCmds := toPyCommands pgm.commands
  assert! pyCmds.size == 1
  {decls := (pyCmds.map PyCommandToBoogie).toList}

end Strata
