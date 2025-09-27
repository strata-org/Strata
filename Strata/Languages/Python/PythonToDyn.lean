import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Dyn.Dyn

namespace Strata

mutual
partial def pyArgToDynArg (c: Arg) : Arg :=
  match c with
  | .op o =>
    match o.name with
    | {dialect := "Python", name:= "FunctionDef"} => .op {name := {dialect := "Python", name:= "FunctionDef"}, args := o.args.map pyArgToDynArg}
    | {dialect := "Python", name:= "mk_arguments"} => .op {name := {dialect := "Python", name:= "mk_arguments"}, args := o.args.map pyArgToDynArg}
    | {dialect := "Python", name:= "mk_arg"} => .op {name := {dialect := "Python", name:= "mk_arg"}, args := o.args.map pyArgToDynArg}
    | {dialect := "Python", name:= "Name"} => .op {name := {dialect := "Python", name:= "Name"}, args := o.args.map pyArgToDynArg}
    | {dialect := "Python", name:= "Load"} => .op {name := {dialect := "Python", name:= "Load"}, args := o.args.map pyArgToDynArg}
    | {dialect := "Python", name:= "Pass"} => .op {name := {dialect := "Python", name:= "Pass"}, args := o.args.map pyArgToDynArg}
    | {dialect := "Python", name:= "Constant"} => .op {name := {dialect := "Python", name:= "Constant"}, args := o.args.map pyArgToDynArg}
    | {dialect := "Python", name:= "ConNone"} => .op {name := {dialect := "Python", name:= "ConNone"}, args := o.args.map pyArgToDynArg}
    | {dialect := "Python", name:= "Store"} => .op {name := {dialect := "Python", name:= "Store"}, args := o.args.map pyArgToDynArg}
    | {dialect := "Python", name:= "BinOp"} => .op {name := {dialect := "Python", name:= "BinOp"}, args := o.args.map pyArgToDynArg}
    | {dialect := "Python", name:= "Add"} => .op {name := {dialect := "Python", name:= "Add"}, args := o.args.map pyArgToDynArg}
    | {dialect := "Python", name:= "IntPos"} => .op {name := {dialect := "Python", name:= "IntPos"}, args := o.args.map pyArgToDynArg}
    | {dialect := "Python", name:= "Return"} => .op {name := {dialect := "Python", name:= "Return"}, args := o.args.map pyArgToDynArg}
    | {dialect := "Python", name:= "ConPos"} => .op {name := {dialect := "Python", name:= "ConPos"}, args := o.args.map pyArgToDynArg}
    | {dialect := "Python", name:= "AnnAssign"} => .op {name := {dialect := "Python", name:= "AnnAssign"}, args := o.args.map pyArgToDynArg}
    | _ => panic! s!"Unimplemented: {o.name}"
  | .cat cat => panic! "Unsupported: cat"
  | .expr e => panic! "Unsupported: expr"
  | .type e => panic! "Unsupported: type"
  | .ident i => panic! "Unsupported: ident"
  | .num _ | .decimal _ | .strlit _ => c
  | .option l => .option (l.map pyArgToDynArg)
  | .seq l => .seq (l.map pyArgToDynArg)
  | .commaSepList l => panic! "Unsupported: commaSepList"


partial def pyCmdToDynCmd (c: Operation) : Operation :=
  match c.name with
  | {dialect := "Python", name:= "Module"} =>
    {c with args := c.args.map pyArgToDynArg}
  | _ => c
end


def pythonToDyn (pgm: Strata.Program): Strata.Program :=
  -- {pgm with dialect := "Dyn"}
  {pgm with dialect := "Dyn", commands := pgm.commands.map pyCmdToDynCmd}


end Strata
