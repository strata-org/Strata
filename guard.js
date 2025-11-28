#!/usr/bin/env node

const fs = require('fs');
const path = require('path');

/**
 * Generate a unique guard command for a specific file
 */
function generateGuardCommand(filePath) {
  // Create a unique identifier from the file path
  const uniqueId = filePath
    .replace(/[^a-zA-Z0-9]/g, '_')  // Replace non-alphanumeric with underscore
    .replace(/_+/g, '_')           // Replace multiple underscores with single
    .replace(/^_|_$/g, '')         // Remove leading/trailing underscores
    .toLowerCase();
  
  return `--GUARD_TOGGLE_START
import Lean.Elab.Command
@[command_elab Lean.guardMsgsCmd] def disableGuardMsgs_${uniqueId} : Lean.Elab.Command.CommandElab := fun _ => pure ()
--GUARD_TOGGLE_END`;
}

const GUARD_START_MARKER = '--GUARD_TOGGLE_START';
const GUARD_END_MARKER = '--GUARD_TOGGLE_END';
const NO_TOGGLE_MARKER = '--NO-GUARD_TOGGLE';

/**
 * Recursively find all .lean files, excluding root directory files
 */
function findLeanFiles(dir, rootDir = dir) {
  const files = [];
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  
  for (const entry of entries) {
    const fullPath = path.join(dir, entry.name);
    
    if (entry.isDirectory()) {
      // Skip .git, .lake and other hidden directories
      if (!entry.name.startsWith('.')) {
        files.push(...findLeanFiles(fullPath, rootDir));
      }
    } else if (entry.isFile() && entry.name.endsWith('.lean')) {
      // Only include files that are NOT in the root directory
      if (dir !== rootDir) {
        files.push(fullPath);
      }
    }
  }
  
  return files;
}

/**
 * Check if file contains guard messages (#guard_msgs)
 */
function hasGuardMessages(content) {
  return content.includes('#guard_msgs in');
}

/**
 * Check if file should be excluded from toggle operations
 */
function shouldSkipFile(content) {
  return content.includes(NO_TOGGLE_MARKER);
}

/**
 * Check if file already has guard toggle command
 */
function hasGuardToggle(content) {
  return content.includes(GUARD_START_MARKER) && content.includes(GUARD_END_MARKER);
}

/**
 * Remove guard toggle command from content
 */
function removeGuardToggle(content) {
  const lines = content.split('\n');
  const result = [];
  let inToggleBlock = false;
  let skipNextEmptyLine = false;
  
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    
    if (line.trim() === GUARD_START_MARKER) {
      inToggleBlock = true;
      // Also skip the empty line before the toggle block if it exists
      if (result.length > 0 && result[result.length - 1].trim() === '') {
        result.pop();
      }
      continue;
    }
    if (line.trim() === GUARD_END_MARKER) {
      inToggleBlock = false;
      skipNextEmptyLine = true;
      continue;
    }
    if (!inToggleBlock) {
      // Skip the empty line immediately after the toggle block
      if (skipNextEmptyLine && line.trim() === '') {
        skipNextEmptyLine = false;
        continue;
      }
      skipNextEmptyLine = false;
      result.push(line);
    }
  }
  
  return result.join('\n');
}

/**
 * Add guard toggle command to the beginning of file content
 */
function addGuardToggle(content, filePath) {
  // Remove any existing toggle first
  content = removeGuardToggle(content);
  
  const lines = content.split('\n');
  let insertIndex = 0;
  let inMultilineComment = false;
  let lastImportIndex = -1;
  
  // Find where imports end
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    
    // Handle multiline comments
    if (line.startsWith('/-')) {
      inMultilineComment = true;
      continue;
    }
    if (line.endsWith('-/') || line === '-/') {
      inMultilineComment = false;
      continue;
    }
    if (inMultilineComment) {
      continue;
    }
    
    // Skip single line comments and empty lines
    if (line === '' || line.startsWith('--')) {
      continue;
    }
    
    // Check if this is an import line
    if (line.startsWith('import ')) {
      lastImportIndex = i;
      continue;
    }
    
    // If we've found imports, insert after the last one
    if (lastImportIndex >= 0) {
      insertIndex = lastImportIndex + 1;
      break;
    }
    
    // If no imports found, insert at first non-comment line
    insertIndex = i;
    break;
  }
  
  // Generate unique guard command for this file
  const guardCommand = generateGuardCommand(filePath);
  
  // Insert the guard command at the appropriate position
  lines.splice(insertIndex, 0, '', guardCommand, '');
  
  return lines.join('\n');
}

/**
 * Process a single file
 */
function processFile(filePath, enableGuards) {
  try {
    const content = fs.readFileSync(filePath, 'utf8');
    
    // Skip files marked with NO_TOGGLE_MARKER
    if (shouldSkipFile(content)) {
      console.log(`Skipping ${filePath} (marked with ${NO_TOGGLE_MARKER})`);
      return { processed: false, reason: 'marked to skip' };
    }
    
    // Only process files that have guard messages
    if (!hasGuardMessages(content)) {
      return { processed: false, reason: 'no guard messages' };
    }
    
    const hasToggle = hasGuardToggle(content);
    let newContent = content;
    let action = 'no change';
    
    if (enableGuards) {
      // Remove guard toggle command (enable guards)
      if (hasToggle) {
        newContent = removeGuardToggle(content);
        action = 'removed guard disable command';
      }
    } else {
      // Add guard toggle command (disable guards)
      if (!hasToggle) {
        newContent = addGuardToggle(content, filePath);
        action = 'added guard disable command';
      }
    }
    
    if (newContent !== content) {
      fs.writeFileSync(filePath, newContent, 'utf8');
      console.log(`✓ ${filePath}: ${action}`);
      return { processed: true, action };
    } else {
      return { processed: false, reason: 'already in desired state' };
    }
    
  } catch (error) {
    console.error(`Error processing ${filePath}: ${error.message}`);
    return { processed: false, reason: 'error', error: error.message };
  }
}

/**
 * Main function
 */
function main() {
  const args = process.argv.slice(2);
  
  if (args.length === 0) {
    console.log('Usage: node guard.js <on|off|true|false|1|0|yes|no>');
    console.log('');
    console.log('  on/true/1/yes  - Enable guards (remove disable command)');
    console.log('  off/false/0/no - Disable guards (add disable command)');
    console.log('');
    console.log('This script will:');
    console.log('- Find all .lean files with guard messages (excluding root directory)');
    console.log('- Skip files marked with --NO-GUARD_TOGGLE');
    console.log('- Add/remove guard disable commands wrapped in toggle markers');
    process.exit(1);
  }
  
  const arg = args[0].toLowerCase();
  const enableGuards = ['on', 'true', '1', 'yes'].includes(arg);
  const disableGuards = ['off', 'false', '0', 'no'].includes(arg);
  
  if (!enableGuards && !disableGuards) {
    console.error('Invalid argument. Use: on/off, true/false, 1/0, or yes/no');
    process.exit(1);
  }
  
  console.log(`${enableGuards ? 'Enabling' : 'Disabling'} guards in Lean files...`);
  console.log('');
  
  // Find all lean files (excluding root)
  const leanFiles = findLeanFiles('.');
  console.log(`Found ${leanFiles.length} .lean files to check`);
  console.log('');
  
  let processedCount = 0;
  let skippedCount = 0;
  let errorCount = 0;
  
  for (const file of leanFiles) {
    const result = processFile(file, enableGuards);
    
    if (result.processed) {
      processedCount++;
    } else if (result.error) {
      errorCount++;
    } else {
      skippedCount++;
    }
  }
  
  console.log('');
  console.log('Summary:');
  console.log(`  Processed: ${processedCount} files`);
  console.log(`  Skipped: ${skippedCount} files`);
  console.log(`  Errors: ${errorCount} files`);
  
  if (processedCount > 0) {
    console.log(`\n✓ Successfully ${enableGuards ? 'enabled' : 'disabled'} guards in ${processedCount} files`);
  }
}



if (require.main === module) {
  main();
}