import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def QuantTypeAliases : Environment :=
#strata
open Boogie;

type Ref;
type Field;
type Box;

type Struct := Map Field Box;
type Heap := Map Ref Struct;

axiom forall m: Struct, okk: Field, kk: Field, vv: Box :: okk != kk ==> m[okk] == m[kk := vv][okk];
axiom forall m: Struct, kk: Field, vv: Box :: m[kk := vv][kk] == vv;

axiom forall m: Heap, okk: Ref, kk: Ref, vv: Struct :: okk != kk ==> m[okk] == m[kk := vv][okk];
axiom forall m: Heap, kk: Ref, vv: Struct :: m[kk := vv][kk] == vv;


#end

#eval TransM.run (translateProgram (QuantTypeAliases.commands)) |>.snd |>.isEmpty

#eval TransM.run (translateProgram (QuantTypeAliases.commands))

#eval verify "cvc5" QuantTypeAliases
