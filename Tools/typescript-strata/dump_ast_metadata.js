import * as t from '@babel/types';
import fs from 'fs';

console.log('Extracting Babel AST metadata...');

function extractFieldType(validate) {
  if (!validate) return null;
  
  const result = {};
  
  // Simple type validation
  if (validate.type) {
    result.type = validate.type;
  }
  
  // Node type validation
  if (validate.oneOfNodeTypes) {
    result.oneOfNodeTypes = validate.oneOfNodeTypes;
  }
  
  // Literal value validation
  if (validate.oneOf) {
    result.oneOf = validate.oneOf;
  }
  
  // Array validation (chainOf)
  if (validate.chainOf) {
    result.chainOf = [];
    for (const validator of validate.chainOf) {
      result.chainOf.push(extractFieldType(validator));
    }
  }
  
  // Array element validation
  if (validate.each) {
    result.each = extractFieldType(validate.each);
  }
  
  return Object.keys(result).length > 0 ? result : null;
}

function extractNodeMetadata() {
  const metadata = {
    nodeTypes: [],
    nodeFields: {},
    builderKeys: {},
    visitorKeys: {},
    aliasKeys: {},
    typeCategories: {}
  };
  
  // Get all node types
  metadata.nodeTypes = Object.keys(t.BUILDER_KEYS);
  
  // Extract field information for each node type
  for (const nodeType of metadata.nodeTypes) {
    // Builder keys (constructor parameters)
    metadata.builderKeys[nodeType] = t.BUILDER_KEYS[nodeType] || [];
    
    // Visitor keys (child node fields)
    metadata.visitorKeys[nodeType] = t.VISITOR_KEYS[nodeType] || [];
    
    // Alias keys (node categories)
    metadata.aliasKeys[nodeType] = t.ALIAS_KEYS[nodeType] || [];
    
    // Field definitions
    const nodeFields = t.NODE_FIELDS[nodeType];
    if (nodeFields) {
      metadata.nodeFields[nodeType] = {};
      
      for (const [fieldName, fieldDef] of Object.entries(nodeFields)) {
        metadata.nodeFields[nodeType][fieldName] = {
          optional: fieldDef.optional || false,
          default: fieldDef.default,
          validation: extractFieldType(fieldDef.validate)
        };
      }
    }
  }
  
  // Extract type categories (useful for understanding node hierarchies)
  const typeCategories = [
    'EXPRESSION_TYPES', 'STATEMENT_TYPES', 'DECLARATION_TYPES',
    'TYPESCRIPT_TYPES', 'FUNCTION_TYPES', 'LITERAL_TYPES',
    'PATTERN_TYPES', 'LOOP_TYPES', 'CONDITIONAL_TYPES'
  ];
  
  for (const category of typeCategories) {
    if (t[category]) {
      metadata.typeCategories[category] = t[category];
    }
  }
  
  return metadata;
}

// Extract all metadata
const astMetadata = extractNodeMetadata();

// Add some summary statistics
astMetadata.summary = {
  totalNodeTypes: astMetadata.nodeTypes.length,
  typescriptNodes: astMetadata.nodeTypes.filter(type => 
    type.startsWith('TS') || astMetadata.typeCategories.TYPESCRIPT_TYPES?.includes(type)
  ).length,
  extractedAt: new Date().toISOString()
};

// Write to JSON file
const outputFile = 'babel_ast_metadata.json';
fs.writeFileSync(outputFile, JSON.stringify(astMetadata, null, 2));

console.log(`✅ Extracted metadata for ${astMetadata.summary.totalNodeTypes} node types`);
console.log(`📝 Written to ${outputFile}`);
console.log(`🔧 TypeScript nodes: ${astMetadata.summary.typescriptNodes}`);

// Show a sample of what we extracted
console.log('\n📋 Sample extracted data:');
console.log('FunctionDeclaration fields:', Object.keys(astMetadata.nodeFields.FunctionDeclaration || {}));
console.log('IfStatement fields:', Object.keys(astMetadata.nodeFields.IfStatement || {}));
console.log('First 10 node types:', astMetadata.nodeTypes.slice(0, 10));
