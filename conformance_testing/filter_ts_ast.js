// check_ast.js
const fs = require("fs");
const parser = require('@babel/parser');
const traverse = require('@babel/traverse').default;
const path = require('path');

const supportedFile = path.resolve(__dirname, process.env.AST_NODES_FILE || 'typescript_ast_nodes.txt');

// Read JS source code from stdin
let code = "";
process.stdin.setEncoding("utf8");
process.stdin.on("data", chunk => {
  code += chunk;
});
process.stdin.on("end", () => {
  let ast;
  try {
    ast = parser.parse(`function __wrapper__() { ${code} }`, {
      sourceType: 'module',
      ecmaVersion: 'latest',
      strictMode: false,
      plugins: ['jsx', 'typescript'],
    });
  } catch (err) {
    console.error("PARSING_ERROR");
    process.exit(1);
  }

  // Read supported nodes and remove TS_ prefix for comparison
  const supported = new Set();
  if (fs.existsSync(supportedFile)) {
    fs.readFileSync(supportedFile, 'utf8')
      .split('\n')
      .map(s => s.trim())
      .filter(Boolean)
      .forEach(line => {
        if (line.startsWith('TS_')) {
          // Remove TS_ prefix for comparison with Babel AST node types
          supported.add(line.substring(3));
        } else {
          supported.add(line);
        }
      });
  }

  const disallowedBuiltins = new Set(['String', 'Object', 'Boolean', 'Array', 'Function', 'Number', 'Math']);
  let invalidNodesSet = new Set();

  traverse(ast, {
    enter(path) {
      const type = path.node.type;
      if (!supported.has(type)) {
        invalidNodesSet.add(type);
      }
      if (type === 'Identifier' && disallowedBuiltins.has(path.node.name)) {
        invalidNodesSet.add(type);
      }
    },
  });

  console.log(JSON.stringify([...invalidNodesSet]));
});
