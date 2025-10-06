#!/usr/bin/env python3
import argparse
import json
import sys

# Converts a Babel AST.json file into Lean-compatible.json file
# The Lean-compatible version differs in two ways
# 1. `start` -> `start_loc` and `end` -> `end_loc` because `end` is a reserved word
# 2. Enum's become tagged

def add_missing_node_info(source_j, target_j):
    for source_key in source_j:
        if source_key not in target_j:
            target_j[source_key] = source_j[source_key]

def parse_type_annotation(j):
    innerTypeAnnotation = None
    match j['typeAnnotation'].get('type'):
        case "TSNumberKeyword":
            innerTypeAnnotation = {"TS_TSNumberKeyword": j['typeAnnotation']}
        case "TSBooleanKeyword":
            innerTypeAnnotation = {"TS_TSBooleanKeyword": j['typeAnnotation']}
        case "TSAnyKeyword":
            # TODO: Is TSAnyKeyword different than not stating any type?
            innerTypeAnnotation = None
        case None:
            innerTypeAnnotation = None
        case _:
            print("Unsupported type annotation type: " + j['typeAnnotation'].get('type'), file=sys.stderr)
    target_j = {
        "typeAnnotation": innerTypeAnnotation
    }
    add_missing_node_info(j, target_j)
    return target_j
    

def parse_binary_expression(j):
    target_j = {
        "left": parse_expression(j['left']),
        "right": parse_expression(j['right']),
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_unary_expression(j):
    target_j = {
        "argument": parse_expression(j['argument'])
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_conditional_expression(j):
    target_j = {
        "test": parse_expression(j['test']),
        "consequent": parse_expression(j['consequent']),
        "alternate": parse_expression(j['alternate'])
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_call_expression(j):
    target_j = {
        "callee": parse_identifier(j['callee']),
        "arguments": [parse_expression(arg) for arg in j['arguments']]
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_logical_expression(j):
    target_j = {
        "left": parse_expression(j['left']),
        "right": parse_expression(j['right'])
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_assignment_identifier(j):
    match j["type"]:
        case "Identifier":
            return {"TS_Identifier": parse_identifier(j)}
        case "MemberExpression":
            return {"TS_MemberExpression": parse_member_expression(j)}
        case _:
            print("Unsupported assignment identifier type: " + j["type"], file=sys.stderr)
            return j

def parse_assignment_expression(j):
    target_j = {
        'left': parse_assignment_identifier(j['left']),
        'right': parse_expression(j['right'])
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_object_property(j):
    target_j = {
        'key': parse_expression(j['key']),
        'value': parse_expression(j['value'])
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_object_expression(j):
    target_j = {
        'properties': [parse_object_property(ji) for ji in j['properties']]
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_member_expression(j):
    target_j = {
        'object': parse_expression(j['object']),
        'property': parse_expression(j['property'])
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_function_expression(j):
    target_j = {
        'params': [parse_identifier(ji) for ji in j['params']],
        'body': parse_statement(j['body'])
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_arrow_function_expression(j):
    target_j = {
        'params': [parse_identifier(ji) for ji in j['params']],
        'body': parse_statement(j['body'])
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_expression(j):
    match j['type']:
        case "Identifier":
            return {"TS_IdExpression": parse_identifier(j)}
        case "UnaryExpression":
            return {"TS_UnaryExpression": parse_unary_expression(j)}
        case "BinaryExpression":
            return {"TS_BinaryExpression": parse_binary_expression(j)}
        case "ConditionalExpression":
            return {"TS_ConditionalExpression": parse_conditional_expression(j)}
        case "CallExpression":
            return {"TS_CallExpression": parse_call_expression(j)}
        case "LogicalExpression":
            return {"TS_LogicalExpression": parse_logical_expression(j)}
        case "NumericLiteral":
            return {"TS_NumericLiteral": j}
        case "StringLiteral":
            return {"TS_StringLiteral": j}
        case "BooleanLiteral":
            return {"TS_BooleanLiteral": j}
        case "NullLiteral":
            return {"TS_NullLiteral": j}
        case "AssignmentExpression":
            return {"TS_AssignmentExpression": parse_assignment_expression(j)}
        case "ObjectExpression":
            return {"TS_ObjectExpression": parse_object_expression(j)}
        case "MemberExpression":
            return {"TS_MemberExpression": parse_member_expression(j)}

        # case "ThisExpression":
        case "ArrowFunctionExpression":
            return {"TS_ArrowFunctionExpression": parse_function_expression(j)}
        # case "YieldExpression":
        # case "AwaitExpression":
        # case "ArrayExpression":
        # case "RecordExpression":
        # case "TupleExpression":
        case "FunctionExpression":
            return {"TS_FunctionExpression": parse_function_expression(j)}
        # case "UnaryExpression":
        # case "UpdateExpression":
        # case "BindExpression":
        # case "NewExpression":
        # case "SequenceExpression":
        # case "ParenthesizedExpression":
        # case "DoExpression":
        # case "TemplateLiteral":
        # case "TaggedTemplateExpression":
        # case "ClassExpression":
        # case "MetaProperty":
        # case "Literal":
        # case "RegExpr":
        # case "BigIntLiteral":
        case _:
            print("Unsupported expression type: " + j['type'], file=sys.stderr)
            return j

def parse_variable_declarator(j):
    source_init = j.get('init')
    target_init = None
    if source_init is not None:
        target_init = parse_expression(source_init)


    target_j = {
        "id": parse_identifier(j['id']),
        "init": target_init
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_variable_declaration(j):
    target_declarations = [parse_variable_declarator(ji) for ji in j['declarations']]
    target_j = {
        "declarations": target_declarations
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_if_statement(j):
    source_alternate = j.get("alternate")
    target_alternate = None
    if source_alternate is not None:
        target_alternate = parse_statement(source_alternate)

    target_j = {
        "test": parse_expression(j['test']),
        "consequent": parse_statement(j['consequent']),
        "alternate": target_alternate
    }
    add_missing_node_info(j, target_j)
    return target_j


def parse_return_statement(j):
    source_argument = j.get("argument")
    target_argument = None
    if source_argument is not None:
        target_argument = parse_expression(source_argument)

    target_j = {
        "argument": target_argument
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_expression_statement(j):
    target_j = {
        "expression": parse_expression(j['expression'])
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_block_statement(j):
    target_body = [parse_statement(ji) for ji in j['body']]
    target_j = {
        "body": target_body
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_throw_statement(j):
    target_j = {
        "argument": parse_expression(j['argument'])
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_while_statement(j):
    target_body = parse_statement(j['body'])
    target_j = {
        "test": parse_expression(j['test']),
        "body": target_body
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_continue_statement(j):
    label = j.get("label")
    target_j = {
        "label": None if label is None else parse_identifier(label)
    }
    add_missing_node_info(j, target_j)
    return target_j
    
def parse_for_statement(j):
    target_body = parse_statement(j['body'])
    target_j = {
        "init": parse_variable_declaration(j['init']),
        "test": parse_expression(j['test']),
        "update": parse_assignment_expression(j['update']),
        "body": target_body
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_break_statement(j):
    target_j = {
        "label": parse_identifier(j['label']) if j.get('label') else None
    }
    add_missing_node_info(j, target_j)
    return target_j
    
def parse_for_statement(j):
    target_body = parse_statement(j['body'])
    target_j = {
        "init": parse_variable_declaration(j['init']),
        "test": parse_expression(j['test']),
        "update": parse_assignment_expression(j['update']),
        "body": target_body
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_statement(j):
    match j['type']:
        case "ExpressionStatement":
            return {"TS_ExpressionStatement": parse_expression_statement(j)}
        case "BlockStatement":
            return {"TS_BlockStatement": parse_block_statement(j)}
        case "ReturnStatement":
            return {"TS_ReturnStatement": parse_return_statement(j)}
        case "IfStatement":
            return {"TS_IfStatement": parse_if_statement(j)}
        case "VariableDeclaration":
            return {"TS_VariableDeclaration": parse_variable_declaration(j)}
        case "ThrowStatement":
            return {"TS_ThrowStatement": parse_throw_statement(j)}
        case "FunctionDeclaration":
            return {"TS_FunctionDeclaration": parse_function_declarations(j)}
        # case "SwitchStatement":
        case "BreakStatement":
            return {"TS_BreakStatement": parse_break_statement(j)}
        # case "EmptyStatement":
        # case "DebuggerStatement":
        # case "WithStatement":
        # case "LabeledStatement":
        case "ContinueStatement":
            return {"TS_ContinueStatement": parse_continue_statement(j)}
        # case "TryStatement":
        case "WhileStatement":
            return {"TS_WhileStatement": parse_while_statement(j)}
        # case "DoWhileStatement":
        case "ForStatement":
            return {"TS_ForStatement": parse_for_statement(j)}
        # case "ForInStatement":
        # case "ForOfStatement":
        # case "ClassDeclaration":
        case _:
            print("Unsupported statement type: " + j['type'], file=sys.stderr)
            return j


def parse_identifier(j):
    assert j['type'] == "Identifier", "Node expected to be an identifier"
    target_j = {}
    if "typeAnnotation" in j:
        target_j["typeAnnotation"] = parse_type_annotation(j["typeAnnotation"])
    add_missing_node_info(j, target_j)
    return target_j

def parse_function_params(j):
    return [parse_identifier(ji) for ji in j]

def parse_function_declarations(j):
    assert j.get("type") == "FunctionDeclaration", "Assuming program body is an array of functions"
    target_j = {
        "id": parse_identifier(j['id']),
        "params": parse_function_params(j['params']),
        "returnType": parse_type_annotation(j['returnType']),
        "body": parse_statement(j['body'])
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_body(j):
    assert isinstance(j, list), "Assuming program body is an array of statements"
    target_j = []
    for f in j:
        target_j.append(parse_statement(f))
    return target_j

def parse_program(j):
    assert j['type'] == "Program", "Assuming node is a program"
    target_j = {
        "body": parse_body(j['body'])
    }
    add_missing_node_info(j, target_j)
    return target_j

def parse_file(j):
    assert j['type'] == "File", "Assuming root node is a file"
    target_j = {
        "program": parse_program(j['program'])
    }
    add_missing_node_info(j, target_j)
    return target_j

def rename_start_and_end(j):
    """
    Renames all occurrences of 'start' to 'start_loc' and 'end' to 'end_loc' in the given JSON
    """
    if isinstance(j, dict):
        res = {}
        for (k, v) in j.items():
            if k == "start":
                res["start_loc"] = rename_start_and_end(v)
            elif k == "end":
                res["end_loc"] = rename_start_and_end(v)
            else:
                res[k] = rename_start_and_end(v)
        return res
    elif isinstance(j, list):
        return [rename_start_and_end(n) for n in j]
    else:
        return j


def modify(j):
    """
    Transform Babel's AST.json into Lean-compatible JSON
    """
    return rename_start_and_end(parse_file(j))

def main():
    parser  = argparse.ArgumentParser(description="Takes a Typescript AST and prepares it for ingestion into Lean.")
    parser.add_argument("filename", type=str, help="Path to the Typescript AST")
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