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

PythonDis : typing.Any = strata.Dialect('PythonDis')
PythonDis.add_import("Init")
const = PythonDis.add_syncat("Const")()
PythonDis.add_syncat("Code")
PythonDis.add_op("constCode", [ArgDecl("value", PythonDis.Code())], const)
PythonDis.add_op("constInt", [ArgDecl("value", Init.Num())], const)
PythonDis.add_op("constNone", [], const)
PythonDis.add_op("constStr", [ArgDecl("value", Init.Str())], const)

def initd():
    m = InstructionMap()
    inst = PythonDis.add_syncat("Instruction")()
    for d in m.instructions:
        args = [ArgDecl("arg", PythonDis.Const())] if d.hasarg else []
        PythonDis.add_op(d.name, args, inst)

initd()

PythonDis.add_op("mkCode",
    args=[
        ArgDecl("name", Init.Str()),
        ArgDecl("constants", Init.Seq(PythonDis.Const())),
        ArgDecl("instructions", Init.Seq(PythonDis.Instruction()))
    ],
    result=PythonDis.Code())