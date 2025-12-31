/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format
import Strata.Languages.BoogieMinimal.DDMTransform.DatatypeConfig

---------------------------------------------------------------------

namespace Strata

---------------------------------------------------------------------
---------------------------------------------------------------------

/- DDM support for parsing and pretty-printing BoogieMinimal -/

#dialect
dialect BoogieMinimal;

// Declare BoogieMinimal-specific metadata for datatype declarations
// Arguments: name index, typeParams index, constructors index, followed by function templates
// Unlike Boogie, BoogieMinimal only has indexer template (no field accessors)
metadata declareDatatype (name : Ident, typeParams : Ident, constructors : Ident,
                          indexerTemplate : FunctionTemplate);

// Primitive types
type bool;
type int;

// Type arguments for polymorphic types
category TypeArgs;
op type_args (args : CommaSepBy Ident) : TypeArgs => "<" args ">";

// Bindings for type parameters
category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] name ":" tp;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

// Basic expressions
fn btrue : bool => "true";
fn bfalse : bool => "false";
fn natToInt (n : Num) : int => n;

// Equality
fn equal (tp : Type, a : tp, b : tp) : bool => @[prec(15)] a "==" b;

// Boolean operations
fn and (a : bool, b : bool) : bool => @[prec(10), leftassoc] a "&&" b;
fn or (a : bool, b : bool) : bool => @[prec(8), leftassoc] a "||" b;
fn not (b : bool) : bool => "!" b;

// Arithmetic operations
fn add_expr (tp : Type, a : tp, b : tp) : tp => @[prec(25), leftassoc] a "+" b;
fn sub_expr (tp : Type, a : tp, b : tp) : tp => @[prec(25), leftassoc] a "-" b;

// =====================================================================
// Datatype Syntax Categories
// =====================================================================

// Field syntax for datatype constructors
category Field;
category FieldList;

// @[field(name, tp)] marks this operation as a field definition
// @[declare(name, tp)] adds the field to the binding context
@[declare(name, tp), field(name, tp)]
op field_mk (name : Ident, tp : Type) : Field => name ":" tp;

op fieldListAtom (f : Field) : FieldList => f;
@[scope(fl)]
op fieldListPush (fl : FieldList, @[scope(fl)] f : Field) : FieldList => fl "," f;

// Constructor syntax for datatypes
category Constructor;
category ConstructorList;

// @[constructor(name, fields)] marks this operation as a constructor definition
@[constructor(name, fields)]
op constructor_mk (name : Ident, fields : Option FieldList) : Constructor =>
  name "(" fields ")";

op constructorListAtom (c : Constructor) : ConstructorList => c;
op constructorListPush (cl : ConstructorList, c : Constructor) : ConstructorList =>
  cl "," c;

// Datatype command with function templates
// BoogieMinimal uses indexer pattern (returns int) instead of tester pattern (returns bool)
// NO perField template - BoogieMinimal does not generate field accessors
@[declareDatatype(name, typeParams, constructors,
    perConstructor([.datatype, .literal "$idx$", .constructor], [.datatype], .builtin "int"))]
op command_datatype (name : Ident,
                     typeParams : Option Bindings,
                     @[scopeDatatype(name, typeParams)] constructors : ConstructorList) : Command =>
  "datatype " name typeParams " {" constructors "}" ";\n";

#end

namespace BoogieMinimalDDM

--#strata_gen BoogieMinimal

end BoogieMinimalDDM

---------------------------------------------------------------------

end Strata
