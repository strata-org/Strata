#!/usr/bin/env python3
import argparse
import json
from dataclasses import dataclass
import os
import amazon.ion.simpleion as ion
import sys

# Add the pythonStrata directory to path to import strata module
sys.path.append('../pythonStrata')
import strata
from strata import ArgDecl, QualifiedIdent, SyntaxCat

init_num_cat = SyntaxCat(QualifiedIdent("Init.Num"))
init_str_cat = SyntaxCat(QualifiedIdent("Init.Str"))
init_option = QualifiedIdent("Init.Option")
init_seq = QualifiedIdent("Init.Seq")

@dataclass
class OpArg:
    name : str
    ddm_name : str
    cat : SyntaxCat

class Op:
    def __init__(self, name: str, args: list[OpArg], category: SyntaxCat):
        self.name = name
        self.args = args
        self.category = category

    def op_decl(self) -> strata.OpDecl:
        op_args = [ ArgDecl(a.ddm_name, a.cat) for a in self.args ]
        return strata.OpDecl(self.name, op_args, self.category)

def gen_cats(metadata: dict, dialect_name: str) -> dict[str, SyntaxCat]:
    cats = {}
    
    # Create categories for Strata categories (Expression, Statement, etc.)
    for category in metadata.get('strataCategories', []):
        if category == 'Expression':
            cats['Expression'] = SyntaxCat(QualifiedIdent(dialect_name, "expr"))
        elif category == 'Statement':
            cats['Statement'] = SyntaxCat(QualifiedIdent(dialect_name, "stmt"))
        elif category == 'Declaration':
            cats['Declaration'] = SyntaxCat(QualifiedIdent(dialect_name, "decl"))
        elif category == 'Pattern':
            cats['Pattern'] = SyntaxCat(QualifiedIdent(dialect_name, "pattern"))
        else:
            cats[category] = SyntaxCat(QualifiedIdent(dialect_name, category.lower()))
    
    # Create categories for concrete node types
    for node_type in metadata['nodeTypes']:
        if node_type == 'Program':
            cats[node_type] = SyntaxCat(QualifiedIdent("Init.Command"))
        else:
            cats[node_type] = SyntaxCat(QualifiedIdent(dialect_name, node_type))
    
    return cats

def map_babel_type_to_strata(babel_type: str, cats: dict[str, SyntaxCat], dialect_name: str) -> SyntaxCat:
    """Map Babel validation types to Strata categories"""
    if babel_type in cats:
        return cats[babel_type]
    elif babel_type == 'boolean':
        return SyntaxCat(QualifiedIdent(dialect_name, "bool"))
    elif babel_type == 'string':
        return init_str_cat
    elif babel_type == 'number':
        return init_num_cat
    else:
        # Fallback - create a new category
        return SyntaxCat(QualifiedIdent(dialect_name, babel_type))

def extract_field_type(field_info: dict, cats: dict[str, SyntaxCat], dialect_name: str) -> SyntaxCat:
    """Extract Strata type from full field info (validation + optional flag)"""
    validation = field_info.get('validation')
    is_optional = field_info.get('optional', False)
    
    # Handle the base type first
    base_type = None
    
    if not validation:
        base_type = init_str_cat
    elif validation.get('type'):
        base_type = map_babel_type_to_strata(validation['type'], cats, dialect_name)
    elif validation.get('oneOfNodeTypes'):
        node_types = validation['oneOfNodeTypes']
        if len(node_types) == 1:
            base_type = map_babel_type_to_strata(node_types[0], cats, dialect_name)
        else:
            # Multiple types - use first one for now
            # TODO: Handle union types properly
            base_type = map_babel_type_to_strata(node_types[0], cats, dialect_name)
    elif validation.get('chainOf'):
        # Array type
        chain = validation['chainOf']
        if len(chain) >= 2 and chain[0] and chain[1]:
            if chain[0].get('type') == 'array' and chain[1].get('each'):
                element_validation = {'validation': chain[1]['each'], 'optional': False}
                element_type = extract_field_type(element_validation, cats, dialect_name)
                base_type = SyntaxCat(init_seq, [element_type])
    elif validation.get('oneOf'):
        # Literal values - treat as string
        base_type = init_str_cat
    
    if base_type is None:
        base_type = init_str_cat
    
    # Now handle optional - create flat type, not nested
    if is_optional:
        # For arrays, just return the array (drop optional - arrays are never truly optional)
        if base_type.ident == init_seq:
            return base_type  # Already Seq T
        else:
            # Optional single type: create "Option T" 
            return SyntaxCat(QualifiedIdent("Init.Option"), [base_type])
    
    return base_type

def gen_ops(cats: dict[str, SyntaxCat], metadata: dict, dialect_name: str) -> dict[str, Op]:
    ops = {}
    
    for node_type in metadata['nodeTypes']:
        if node_type not in metadata.get('nodeFields', {}):
            # Node with no fields
            ops[node_type] = Op(node_type, [], cats[node_type])
            continue
        
        node_fields = metadata['nodeFields'][node_type]
        op_args = []
        used_names = { "category", "op", "type", "fn", "metadata" }
        
        for field_name, field_info in node_fields.items():
            # Handle name conflicts
            ddm_name = field_name
            if field_name in used_names:
                idx = 0
                while f"{field_name}{idx}" in used_names:
                    idx += 1
                ddm_name = f"{field_name}{idx}"
            
            # Extract field type (handles optional + validation together)
            field_cat = extract_field_type(field_info, cats, dialect_name)
            
            op_args.append(OpArg(field_name, ddm_name, field_cat))
        
        ops[node_type] = Op(node_type, op_args, cats[node_type])
    
    return ops

def gen_dialect(cats: dict[str, SyntaxCat], ops: dict[str, Op], dialect_name: str):
    d = strata.Dialect(dialect_name)
    d.add_import("Init")
    
    # Add categories
    added_cats = set()
    for cat_name, cat in cats.items():
        if cat_name in ['Program']:  # Skip special cases
            continue
        if cat.ident.name not in added_cats:
            d.add(strata.SynCatDecl(cat.ident.name, []))
            added_cats.add(cat.ident.name)
    
    # Add operators
    for op in ops.values():
        d.add(op.op_decl())
    
    return d

def gen_dialect_imp(args):
    with open(args.json_file, 'r') as f:
        metadata = json.load(f)
    
    dialect_name = args.dialect_name or "TypeScript"
    cats = gen_cats(metadata, dialect_name)
    ops = gen_ops(cats, metadata, dialect_name)
    d = gen_dialect(cats, ops, dialect_name)
    
    if not os.path.isdir(args.output_dir):
        print(f"Directory {args.output_dir} does not exist.", file=sys.stderr)
        exit(1)
    
    output = f"{args.output_dir}/{dialect_name}.dialect.st.ion"
    with open(output, 'wb') as w:
        ion.dump(d.to_ion(), w, binary=True)
    print(f"Wrote {dialect_name} dialect to {output}")

def main():
    parser = argparse.ArgumentParser(
                    prog='gen_typescript',
                    description='Generate Strata dialect from Babel AST metadata JSON')
    subparsers = parser.add_subparsers(help="subcommand help")

    gen_dialect_command = subparsers.add_parser('gen_dialect', help='Create Strata dialect file from JSON')
    gen_dialect_command.add_argument('json_file', help='JSON file with Babel AST metadata')
    gen_dialect_command.add_argument('output_dir', help='Directory to write Strata dialect to')
    gen_dialect_command.add_argument('--dialect-name', default='TypeScript', 
                                   help='Name for the dialect (default: TypeScript)')
    gen_dialect_command.set_defaults(func=gen_dialect_imp)

    args = parser.parse_args()
    if hasattr(args, 'func'):
        args.func(args)
    else:
        parser.print_help()

if __name__ == '__main__':
    main()
