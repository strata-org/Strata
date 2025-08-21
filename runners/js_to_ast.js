const fs = require('fs');
const path = require('path');
const parser = require('@babel/parser');

const inputPath = process.argv[2];


if (!inputPath) {
  console.error('Usage: node generate-ast.js <path-to-js-file>');
  process.exit(1);
}

const code = fs.readFileSync(inputPath, 'utf-8');

const ast = parser.parse(code, {
  sourceType: 'module',
  plugins: ['jsx', 'typescript'], // include as needed,
  strictMode: false
});

console.log(JSON.stringify(ast, null, 2));
