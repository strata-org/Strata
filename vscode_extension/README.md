# Strata Analysis VSCode Extension

A VSCode extension for running Strata static analysis on TypeScript files.

## Features

- **Taint Analysis**: Detects data flow from external/untrusted sources through your TypeScript code
- **Real-time highlighting**: Highlights tainted variables and objects directly in the editor
- **Hover tooltips**: Shows detailed violation messages when hovering over highlighted code

## Usage

1. Open a TypeScript file in VSCode
2. Right-click in the editor and select "Strata: Run Taint Analysis"
3. Or use the keyboard shortcut: `Ctrl+Shift+S` (Windows/Linux) or `Cmd+Shift+S` (Mac)

## Requirements

- Strata framework must be installed and built at `/Users/mzwangg/Strata`
- TypeScript files only

## Demo

The extension will:
1. Run Strata's taint analysis on your TypeScript file
2. Highlight any variables or objects that contain tainted data
3. Show violation details when you hover over highlighted code
4. Display a summary of findings in the notification area

## Example

```typescript
// This will be highlighted as tainted
let userInput = getUserInput();

let profile = {
    1: userInput,  // This field will be highlighted
};

// This will also be highlighted as tainted
let taintedValue = profile[1];
```

## Installation

1. Copy this extension to your VSCode extensions directory
2. Run `npm install` in the extension directory
3. Run `npm run compile` to build the extension
4. Reload VSCode to activate the extension
