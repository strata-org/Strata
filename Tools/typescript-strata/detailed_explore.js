import * as t from '@babel/types';

console.log('=== DETAILED BABEL METADATA EXPLORATION ===\n');

// 1. What are BUILDER_KEYS?
console.log('1. BUILDER_KEYS explanation:');
console.log('BUILDER_KEYS are the fields needed to construct a node using t.functionDeclaration(), etc.');
console.log('Example: t.functionDeclaration(id, params, body, generator, async)');
console.log('FunctionDeclaration BUILDER_KEYS:', t.BUILDER_KEYS.FunctionDeclaration);
console.log();

// 2. Let's see the actual oneOfNodeTypes arrays
console.log('2. Actual field type information:');

function exploreField(nodeType, fieldName) {
  const field = t.NODE_FIELDS[nodeType]?.[fieldName];
  if (!field) return;
  
  console.log(`${nodeType}.${fieldName}:`);
  console.log('  validate function:', field.validate);
  
  // Try to access the validation info
  if (field.validate.oneOfNodeTypes) {
    console.log('  oneOfNodeTypes:', field.validate.oneOfNodeTypes);
  }
  if (field.validate.chainOf) {
    console.log('  chainOf:', field.validate.chainOf);
  }
  if (field.validate.type) {
    console.log('  type:', field.validate.type);
  }
  if (field.validate.oneOf) {
    console.log('  oneOf:', field.validate.oneOf);
  }
  console.log('  optional:', field.optional);
  console.log('  default:', field.default);
  console.log();
}

exploreField('FunctionDeclaration', 'id');
exploreField('FunctionDeclaration', 'params');
exploreField('FunctionDeclaration', 'body');
exploreField('IfStatement', 'test');
exploreField('IfStatement', 'consequent');
exploreField('BinaryExpression', 'left');
exploreField('BinaryExpression', 'operator');

// 3. Let's try to create some nodes and see what happens
console.log('3. Testing node creation:');
try {
  // This should show us what types are expected
  const func = t.functionDeclaration(
    t.identifier('test'),
    [],
    t.blockStatement([])
  );
  console.log('Created FunctionDeclaration successfully');
  console.log('func.type:', func.type);
  console.log('func keys:', Object.keys(func));
} catch (e) {
  console.log('Error creating function:', e.message);
}

// 4. Let's look at some validation functions more closely
console.log('\n4. Validation function details:');
const bodyField = t.NODE_FIELDS.FunctionDeclaration.body;
console.log('FunctionDeclaration.body validate:', bodyField.validate.toString());

const testField = t.NODE_FIELDS.IfStatement.test;
console.log('IfStatement.test validate:', testField.validate.toString());
