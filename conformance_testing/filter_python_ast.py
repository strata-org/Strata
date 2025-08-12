#!/usr/bin/env python3
"""
Validate Python AST nodes against supported list.
Similar to filter_ast.js but for Python.
"""

import ast
import json
import sys
import os
from pathlib import Path

def main():
    # Read supported nodes
    ast_nodes_file = os.environ.get("AST_NODES_FILE", "python_ast_nodes.txt")
    supported_file = Path(__file__).parent / ast_nodes_file
    if not supported_file.exists():
        print(json.dumps([f"MISSING_AST_NODES_FILE_{ast_nodes_file}"]))
        return
    
    supported = set()
    with open(supported_file, 'r') as f:
        for line in f:
            line = line.strip()
            if line and line.startswith('Py_'):
                # Remove Py_ prefix for comparison
                supported.add(line[3:])
    
    # Read Python code from stdin
    code = sys.stdin.read()
    
    try:
        tree = ast.parse(code)
        invalid_nodes = set()
        
        for node in ast.walk(tree):
            node_type = node.__class__.__name__
            if node_type not in supported:
                invalid_nodes.add(node_type)
        
        print(json.dumps(list(invalid_nodes)))
        
    except SyntaxError:
        print(json.dumps(["PARSING_ERROR"]))
    except Exception:
        print(json.dumps(["PARSE_ERROR"]))

if __name__ == "__main__":
    main()
