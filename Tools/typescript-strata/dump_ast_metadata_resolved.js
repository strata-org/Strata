import * as t from '@babel/types';
import fs from 'fs';

console.log('Extracting Babel AST metadata with resolved aliases...');

// Define which aliases should be treated as Strata categories vs expanded
const STRATA_CATEGORIES = new Set([
  'Expression',
  'Statement', 
  'Declaration',
  'Pattern',
  'FunctionParameter',
  'PatternLike',
  'TSType',
  'TSEntityName'
]);

// Function to resolve type aliases to concrete node types
function resolveTypeAlias(typeName) {
  // If it's a Strata category, keep it as-is
  if (STRATA_CATEGORIES.has(typeName)) {
    return [typeName];
  }
  
  // Check if it's a type alias by looking for corresponding _TYPES export
  const aliasKey = `${typeName.toUpperCase()}_TYPES`;
  if (t[aliasKey]) {
    return t[aliasKey];
  }
  
  // If not an alias, return as-is
  return [typeName];
}

function resolveNodeTypes(nodeTypes) {
  if (!nodeTypes) return null;
  
  const resolved = [];
  for (const nodeType of nodeTypes) {
    resolved.push(...resolveTypeAlias(nodeType));
  }
  
  // Remove duplicates and return
  return [...new Set(resolved)];
}

function extractFieldType(validate) {
  if (!validate) return null;
  
  const result = {};
  
  // Simple type validation
  if (validate.type) {
    result.type = validate.type;
  }
  
  // Node type validation - RESOLVE ALIASES HERE
  if (validate.oneOfNodeTypes) {
    result.oneOfNodeTypes = resolveNodeTypes(validate.oneOfNodeTypes);
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

function categorizeNodeTypes(nodeTypes) {
  const categories = {
    expressions: [],
    statements: [],
    declarations: [],
    patterns: [],
    typescript: [],
    other: []
  };
  
  for (const nodeType of nodeTypes) {
    if (t.EXPRESSION_TYPES?.includes(nodeType)) {
      categories.expressions.push(nodeType);
    } else if (t.STATEMENT_TYPES?.includes(nodeType)) {
      categories.statements.push(nodeType);
    } else if (t.DECLARATION_TYPES?.includes(nodeType)) {
      categories.declarations.push(nodeType);
    } else if (t.PATTERN_TYPES?.includes(nodeType)) {
      categories.patterns.push(nodeType);
    } else if (t.TYPESCRIPT_TYPES?.includes(nodeType)) {
      categories.typescript.push(nodeType);
    } else {
      categories.other.push(nodeType);
    }
  }
  
  return categories;
}

function extractNodeMetadata() {
  const metadata = {
    nodeTypes: [],
    nodeCategories: {},
    nodeFields: {},
    builderKeys: {},
    visitorKeys: {},
    aliasKeys: {},
    typeCategories: {},
    typeAliases: {},
    strataCategories: Array.from(STRATA_CATEGORIES)
  };
  
  // Get all concrete node types (not aliases)
  metadata.nodeTypes = Object.keys(t.BUILDER_KEYS);
  
  // Categorize node types
  metadata.nodeCategories = categorizeNodeTypes(metadata.nodeTypes);
  
  // Extract type aliases for reference
  const typeCategories = Object.keys(t).filter(key => key.endsWith('_TYPES'));
  for (const category of typeCategories) {
    const aliasName = category.replace('_TYPES', '');
    metadata.typeAliases[aliasName] = t[category];
  }
  
  // Extract field information for each node type
  for (const nodeType of metadata.nodeTypes) {
    // Builder keys (constructor parameters)
    metadata.builderKeys[nodeType] = t.BUILDER_KEYS[nodeType] || [];
    
    // Visitor keys (child node fields)
    metadata.visitorKeys[nodeType] = t.VISITOR_KEYS[nodeType] || [];
    
    // Alias keys (node categories)
    metadata.aliasKeys[nodeType] = t.ALIAS_KEYS[nodeType] || [];
    
    // Field definitions with resolved aliases
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
  
  // Keep type categories for reference
  metadata.typeCategories = {};
  for (const category of typeCategories) {
    metadata.typeCategories[category] = t[category];
  }
  
  return metadata;
}

// Extract all metadata
const astMetadata = extractNodeMetadata();

// Add some summary statistics
astMetadata.summary = {
  totalNodeTypes: astMetadata.nodeTypes.length,
  totalTypeAliases: Object.keys(astMetadata.typeAliases).length,
  expressionTypes: astMetadata.nodeCategories.expressions.length,
  statementTypes: astMetadata.nodeCategories.statements.length,
  strataCategories: astMetadata.strataCategories.length,
  typescriptNodes: astMetadata.nodeTypes.filter(type => 
    type.startsWith('TS') || astMetadata.typeCategories.TYPESCRIPT_TYPES?.includes(type)
  ).length,
  extractedAt: new Date().toISOString()
};

// Write to JSON file
const outputFile = 'babel_ast_metadata_resolved.json';
fs.writeFileSync(outputFile, JSON.stringify(astMetadata, null, 2));

console.log(`✅ Extracted metadata for ${astMetadata.summary.totalNodeTypes} node types`);
console.log(`🔗 Resolved ${astMetadata.summary.totalTypeAliases} type aliases`);
console.log(`📊 Categories: ${astMetadata.summary.expressionTypes} expressions, ${astMetadata.summary.statementTypes} statements`);
console.log(`🏷️  Strata categories: ${astMetadata.summary.strataCategories}`);
console.log(`📝 Written to ${outputFile}`);
console.log(`🔧 TypeScript nodes: ${astMetadata.summary.typescriptNodes}`);

// Show example of alias resolution
console.log('\n📋 Example category handling:');
console.log('Expression stays as "Expression" (not expanded)');
console.log('LVal resolves to:', astMetadata.typeAliases.LVAL?.slice(0, 3), '... (first 3)');
