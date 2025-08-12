#!/usr/bin/env python3
"""
Convert Python source code to AST JSON.
Similar to js_to_ast.js but for Python.
"""

import ast
import json
import sys
from pathlib import Path

def ast_to_dict(node):
    """Convert AST node to dictionary representation."""
    if isinstance(node, ast.AST):
        result = {'_type': node.__class__.__name__}
        
        # Add position information
        if hasattr(node, 'lineno'):
            result['lineno'] = node.lineno
        if hasattr(node, 'col_offset'):
            result['col_offset'] = node.col_offset
        if hasattr(node, 'end_lineno'):
            result['end_lineno'] = node.end_lineno
        if hasattr(node, 'end_col_offset'):
            result['end_col_offset'] = node.end_col_offset
            
        # Convert all fields
        for field, value in ast.iter_fields(node):
            if isinstance(value, list):
                result[field] = [ast_to_dict(item) for item in value]
            elif isinstance(value, ast.AST):
                result[field] = ast_to_dict(value)
            else:
                result[field] = value
                
        return result
    else:
        return node

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 python_to_ast.py <python_file>", file=sys.stderr)
        sys.exit(1)
    
    input_path = Path(sys.argv[1])
    
    try:
        code = input_path.read_text()
        tree = ast.parse(code)
        ast_dict = ast_to_dict(tree)
        print(json.dumps(ast_dict, indent=2))
    except Exception as e:
        print(f"Error parsing {input_path}: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()
