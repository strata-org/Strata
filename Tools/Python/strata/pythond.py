import typing
import strata
from strata import ArgDecl, Init
import dis
from dataclasses import dataclass

@dataclass
class InstructionDecl:
    code : int
    name : str
    hasarg : bool

class InstructionMap:
    idxmap : list[InstructionDecl|None]
    instructions : list[InstructionDecl]

    def __init__(self):
        size = max(v for (_, v) in dis.opmap.items()) + 1
        assert all(isinstance(a, int) and 0 <= a and a < size for a in dis.hasarg)
        hasarg = set(dis.hasarg)

        idxmap : list[InstructionDecl|None] = [None] * size
        instructions = []
        for (name, code) in dis.opmap.items():
            assert isinstance(code, int)
            assert idxmap[code] is None
            decl = InstructionDecl(code, name, code in hasarg)
            idxmap[code] = decl
            instructions.append(decl)

        self.idxmap = idxmap
        self.instructions = instructions

PythonD : typing.Any = strata.Dialect('PythonD')
PythonD.add_import("Init")
const = PythonD.add_syncat("Const")()
PythonD.add_syncat("Code")
PythonD.add_op("constCode", [ArgDecl("value", PythonD.Code())], const)
PythonD.add_op("constInt", [ArgDecl("value", Init.Num())], const)
PythonD.add_op("constNone", [], const)
PythonD.add_op("constStr", [ArgDecl("value", Init.Str())], const)

def initd():
    m = InstructionMap()
    inst = PythonD.add_syncat("Instruction")()
    for d in m.instructions:
        args = [ArgDecl("arg", PythonD.Const())] if d.hasarg else []
        PythonD.add_op(d.name, args, inst)

initd()

PythonD.add_op("mkCode",
    args=[
        ArgDecl("name", Init.Str()),
        ArgDecl("constants", Init.Seq(PythonD.Const())),
        ArgDecl("instructions", Init.Seq(PythonD.Instruction()))
    ],
    result=PythonD.Code())