import ast
import json
import sys
from ast2json import ast2json

python_file = sys.argv[1]
with open(python_file, 'r') as f:
    code = f.read()

tree = ast.parse(code)

# Optionally, walk or visualize it
import astpretty
print(json.dumps(ast2json(tree),indent=2))
