#!/usr/bin/env python3
import argparse
import json
import sys

# Converts a Python AST.json file into Lean-compatible.json file
# The Lean-compatible version differs in two ways:
# 1. Enum's become tagged unions (e.g., {"_type": "Add"} -> {"Add": {...}})
# 2. Handles optional fields and nested structures properly

def add_missing_node_info(source_j, target_j):
    """Copy all fields from source to target that aren't already present"""
    for source_key in source_j:
        if source_key not in target_j:
            target_j[source_key] = source_j[source_key]

def parse_context(j):
    """Parse Python context (Load/Store)"""
    match j.get('_type'):
        case "Load":
            return {"Load": j}
        case "Store":
            return {"Store": j}
        case _:
            print(f"Unsupported context type: {j.get('_type')}", file=sys.stderr)
            return j

def parse_operator(j):
    """Parse Python operators (Add, Sub, Mult, Div, etc.)"""
    match j.get('_type'):
        case "Add":
            return {"Add": j}
        case "Sub":
            return {"Sub": j}
        case "Mult":
            return {"Mult": j}
        case "Div":
            return {"Div": j}
        case "Lt":
            return {"Lt": j}
        case "Gt":
            return {"Gt": j}
        case "Eq":
            return {"Eq": j}
        case _:
            print(f"Unsupported operator type: {j.get('_type')}", file=sys.stderr)
            return j

def parse_constant(j):
    """Parse Python constant values"""
    target_j = {}
    add_missing_node_info(j, target_j)
    return target_j

def parse_name(j):
    """Parse Python Name (variable identifier)"""
    target_j = {
        "id": j['id'],
        "ctx": parse_context(j['ctx'])
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_subscript(j):
    """Parse Python Subscript (array/dict access)"""
    target_j = {
        "value": parse_expression(j['value']),
        "slice": parse_expression(j['slice']),
        "ctx": parse_context(j['ctx'])
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_binop(j):
    """Parse Python BinOp (binary operation)"""
    target_j = {
        "left": parse_expression(j['left']),
        "op": parse_operator(j['op']),
        "right": parse_expression(j['right'])
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_dict(j):
    """Parse Python Dict"""
    target_j = {
        "keys": [parse_expression(key) for key in j['keys']],
        "values": [parse_expression(value) for value in j['values']]
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_compare(j):
    """Parse Python Compare (comparison operation)"""
    target_j = {
        "left": parse_expression(j['left']),
        "ops": [parse_operator(op) for op in j['ops']],
        "comparators": [parse_expression(comp) for comp in j['comparators']]
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_expression(j):
    """Parse Python expressions and convert to tagged unions"""
    match j.get('_type'):
        case "Constant":
            return {"Py_Constant": parse_constant(j)}
        case "Name":
            return {"Py_Name": parse_name(j)}
        case "BinOp":
            return {"Py_BinOp": parse_binop(j)}
        case "Subscript":
            return {"Py_Subscript": parse_subscript(j)}
        case "Dict":
            return {"Py_Dict": parse_dict(j)}
        case "Compare":
            return {"Py_Compare": parse_compare(j)}
        case _:
            print(f"Unsupported expression type: {j.get('_type')}", file=sys.stderr)
            return j

def parse_assign(j):
    """Parse Python assignment statement"""
    target_j = {
        "targets": [parse_expression(target) for target in j['targets']],
        "value": parse_expression(j['value']),
        "type_comment": j.get('type_comment')
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_if(j):
    """Parse Python if statement"""
    target_j = {
        "test": parse_expression(j['test']),
        "body": [parse_statement(stmt) for stmt in j['body']],
        "orelse": [parse_statement(stmt) for stmt in j.get('orelse', [])]
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_statement(j):
    """Parse Python statements and convert to tagged unions"""
    match j.get('_type'):
        case "Assign":
            return {"Py_Assign": parse_assign(j)}
        case "If":
            return {"Py_If": parse_if(j)}
        case _:
            print(f"Unsupported statement type: {j.get('_type')}", file=sys.stderr)
            return j

def parse_module(j):
    """Parse Python Module (top-level)"""
    assert j.get('_type') == "Module", "Assuming root node is a Module"
    target_j = {
        "_type": j['_type'],
        "body": [parse_statement(stmt) for stmt in j['body']],
        "type_ignores": j.get('type_ignores', [])
    }
    return target_j

def modify(j):
    """
    Transform Python's AST.json into Lean-compatible JSON
    """
    return parse_module(j)

def main():
    parser = argparse.ArgumentParser(description="Takes a Python AST and prepares it for ingestion into Lean.")
    parser.add_argument("filename", type=str, help="Path to the Python AST")
    args = vars(parser.parse_args())

    filename = args['filename']
    try:
        # Read the file
        with open(filename, 'r') as file:
            s = file.read()
            j = json.loads(s)
            modified_j = modify(j)
            print(json.dumps(modified_j, indent=2))

    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
        sys.exit(1)

if __name__ == "__main__":
    main()
