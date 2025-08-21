import * as t from '@babel/types';

console.log('=== EXPLORING BABEL TYPE ALIASES ===\n');

// Let's see what LVal actually represents
console.log('1. What is LVal?');
if (t.LVAL_TYPES) {
  console.log('LVAL_TYPES:', t.LVAL_TYPES);
} else {
  console.log('LVAL_TYPES not found directly');
}

// Let's check all the type category exports
console.log('\n2. All type categories:');
const typeCategories = Object.keys(t).filter(key => key.endsWith('_TYPES'));
console.log('Type categories:', typeCategories.slice(0, 10), '... (showing first 10)');

// Let's look at some key ones
const importantCategories = ['LVAL_TYPES', 'EXPRESSION_TYPES', 'STATEMENT_TYPES', 'PATTERN_TYPES'];
for (const category of importantCategories) {
  if (t[category]) {
    console.log(`\n${category}:`, t[category]);
  }
}

// Let's also check FLIPPED_ALIAS_KEYS to understand the reverse mapping
console.log('\n3. Flipped alias keys (what aliases each node belongs to):');
if (t.FLIPPED_ALIAS_KEYS) {
  console.log('Identifier aliases:', t.FLIPPED_ALIAS_KEYS.Identifier);
  console.log('FunctionDeclaration aliases:', t.FLIPPED_ALIAS_KEYS.FunctionDeclaration);
  console.log('BinaryExpression aliases:', t.FLIPPED_ALIAS_KEYS.BinaryExpression);
}

// Let's see what happens when we try to validate against LVal
console.log('\n4. Testing LVal validation:');
try {
  // This should tell us what concrete types are accepted for LVal
  const identifier = t.identifier('test');
  console.log('Is identifier an LVal?', t.isLVal(identifier));
  
  const binaryExpr = t.binaryExpression('+', t.identifier('a'), t.identifier('b'));
  console.log('Is binaryExpression an LVal?', t.isLVal(binaryExpr));
} catch (e) {
  console.log('Error testing LVal:', e.message);
}
