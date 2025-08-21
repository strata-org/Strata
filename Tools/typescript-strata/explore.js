import * as t from '@babel/types';

console.log('=== BABEL AST STRUCTURE METADATA ===\n');

// 1. All node types
console.log('1. All AST Node Types:');
console.log('BUILDER_KEYS keys:', Object.keys(t.BUILDER_KEYS).slice(0, 10), '... (showing first 10)');
console.log('Total node types:', Object.keys(t.BUILDER_KEYS).length);
console.log();

// 2. Field information for specific nodes
console.log('2. Field Structure Examples:');

console.log('FunctionDeclaration fields:');
console.log('  BUILDER_KEYS:', t.BUILDER_KEYS.FunctionDeclaration);
if (t.NODE_FIELDS && t.NODE_FIELDS.FunctionDeclaration) {
  console.log('  NODE_FIELDS:', t.NODE_FIELDS.FunctionDeclaration);
}
console.log();

console.log('IfStatement fields:');
console.log('  BUILDER_KEYS:', t.BUILDER_KEYS.IfStatement);
if (t.NODE_FIELDS && t.NODE_FIELDS.IfStatement) {
  console.log('  NODE_FIELDS:', t.NODE_FIELDS.IfStatement);
}
console.log();

console.log('BinaryExpression fields:');
console.log('  BUILDER_KEYS:', t.BUILDER_KEYS.BinaryExpression);
if (t.NODE_FIELDS && t.NODE_FIELDS.BinaryExpression) {
  console.log('  NODE_FIELDS:', t.NODE_FIELDS.BinaryExpression);
}
console.log();

// 3. What other metadata is available?
console.log('3. Available Metadata Objects:');
console.log('Available exports:', Object.keys(t).filter(k => k.includes('FIELD') || k.includes('KEY') || k.includes('TYPE')));
console.log();

// 4. TypeScript-specific nodes
console.log('4. TypeScript-specific nodes:');
const tsNodes = Object.keys(t.BUILDER_KEYS).filter(k => 
  k.includes('TS') || k.includes('Type') || k.includes('Interface')
);
console.log('TS nodes:', tsNodes.slice(0, 10));
console.log();

// 5. Detailed look at one node's metadata
console.log('5. Detailed FunctionDeclaration metadata:');
if (t.VISITOR_KEYS && t.VISITOR_KEYS.FunctionDeclaration) {
  console.log('  VISITOR_KEYS:', t.VISITOR_KEYS.FunctionDeclaration);
}
if (t.ALIAS_KEYS && t.ALIAS_KEYS.FunctionDeclaration) {
  console.log('  ALIAS_KEYS:', t.ALIAS_KEYS.FunctionDeclaration);
}
