import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { exec } from 'child_process';

interface Violation {
    object: string;
    message: string;
}

interface AnalysisResult {
    violations: Violation[];
}

let decorationType: vscode.TextEditorDecorationType;

export function activate(context: vscode.ExtensionContext) {
    console.log('Strata Analysis extension is now active!');

    // Create decoration type for highlighting violations
    decorationType = vscode.window.createTextEditorDecorationType({
        backgroundColor: 'rgba(255, 0, 0, 0.2)',
        border: '1px solid red',
        borderRadius: '2px'
    });

    // Register taint analysis command
    let taintAnalysisDisposable = vscode.commands.registerCommand('strata.runTaintAnalysis', () => {
        runTaintAnalysis();
    });

    // Register heap higher order taint analysis command
    let heapHigherOrderTaintAnalysisDisposable = vscode.commands.registerCommand('strata.runHeapHigherOrderTaintAnalysis', () => {
        runHeapHigherOrderTaintAnalysis();
    });

    // Register uninitialized field access analysis command
    let uninitializedFieldAccessDisposable = vscode.commands.registerCommand('strata.runUninitializedFieldAccess', () => {
        runUninitializedFieldAccess();
    });

    // Register value validation analysis command
    let valueValidationDisposable = vscode.commands.registerCommand('strata.runValueValidation', () => {
        runValueValidation();
    });

    context.subscriptions.push(taintAnalysisDisposable);
    context.subscriptions.push(heapHigherOrderTaintAnalysisDisposable);
    context.subscriptions.push(uninitializedFieldAccessDisposable);
    context.subscriptions.push(valueValidationDisposable);
    context.subscriptions.push(decorationType);
}

function runHeapHigherOrderTaintAnalysis() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showErrorMessage('No active editor found');
        return;
    }

    const languageId = editor.document.languageId;
    const filename = editor.document.fileName;
    const fileExtension = path.extname(filename);
    
    if (languageId !== 'typescript' && languageId !== 'python') {
        vscode.window.showErrorMessage('Please open a TypeScript (.ts) or Python (.py) file');
        return;
    }

    // Determine which runner script to use based on file extension
    let command: string;
    if (fileExtension === '.py') {
        command = `./runners/check_python_heaphigherorder_taint.sh "${filename}"`;
    } else if (fileExtension === '.ts') {
        command = `./runners/check_typescript_heaphigherorder_taint.sh "${filename}"`;
    } else {
        vscode.window.showErrorMessage('Unsupported file extension. Please use .ts or .py files');
        return;
    }
    
    // Show progress indicator
    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: `Running Strata Heap Higher Order Taint Analysis (${fileExtension})...`,
        cancellable: false
    }, async (progress) => {
        return new Promise<void>((resolve, reject) => {
            // Get the workspace root to run the command from the right directory
            const workspaceRoot = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
            if (!workspaceRoot) {
                vscode.window.showErrorMessage('No workspace folder found');
                resolve();
                return;
            }

            exec(command, { cwd: '/Users/mzwangg/Strata' }, (error, stdout, stderr) => {
                if (error) {
                    vscode.window.showErrorMessage(`Analysis failed: ${error.message}`);
                    resolve();
                    return;
                }

                try {
                    // Parse the JSON output directly from stdout
                    const result: AnalysisResult = JSON.parse(stdout.trim());
                    
                    // Apply the analysis results to the editor
                    highlightViolations(editor, result.violations);
                    
                    // Show summary message
                    if (result.violations.length === 0) {
                        vscode.window.showInformationMessage('✅ No taint violations found!');
                    } else {
                        vscode.window.showWarningMessage(
                            `⚠️ Found ${result.violations.length} taint violation(s)`
                        );
                    }
                    
                } catch (parseError) {
                    vscode.window.showErrorMessage(`Failed to parse analysis results: ${parseError}`);
                }
                
                resolve();
            });
        });
    });
}

function runTaintAnalysis() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showErrorMessage('No active editor found');
        return;
    }

    const languageId = editor.document.languageId;
    const filename = editor.document.fileName;
    const fileExtension = path.extname(filename);
    
    if (languageId !== 'typescript' && languageId !== 'python') {
        vscode.window.showErrorMessage('Please open a TypeScript (.ts) or Python (.py) file');
        return;
    }

    // Determine which runner script to use based on file extension
    let command: string;
    if (fileExtension === '.py') {
        command = `./runners/check_python_taint.sh "${filename}"`;
    } else if (fileExtension === '.ts') {
        command = `./runners/check_typescript_taint.sh "${filename}"`;
    } else {
        vscode.window.showErrorMessage('Unsupported file extension. Please use .ts or .py files');
        return;
    }
    
    // Show progress indicator
    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: `Running Strata Taint Analysis (${fileExtension})...`,
        cancellable: false
    }, async (progress) => {
        return new Promise<void>((resolve, reject) => {
            // Get the workspace root to run the command from the right directory
            const workspaceRoot = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
            if (!workspaceRoot) {
                vscode.window.showErrorMessage('No workspace folder found');
                resolve();
                return;
            }

            exec(command, { cwd: '/Users/mzwangg/Strata' }, (error, stdout, stderr) => {
                if (error) {
                    vscode.window.showErrorMessage(`Analysis failed: ${error.message}`);
                    resolve();
                    return;
                }

                try {
                    // Parse the JSON output directly from stdout
                    const result: AnalysisResult = JSON.parse(stdout.trim());
                    
                    // Apply the analysis results to the editor
                    highlightViolations(editor, result.violations);
                    
                    // Show summary message
                    if (result.violations.length === 0) {
                        vscode.window.showInformationMessage('✅ No taint violations found!');
                    } else {
                        vscode.window.showWarningMessage(
                            `⚠️ Found ${result.violations.length} taint violation(s)`
                        );
                    }
                    
                } catch (parseError) {
                    vscode.window.showErrorMessage(`Failed to parse analysis results: ${parseError}`);
                }
                
                resolve();
            });
        });
    });
}

function highlightViolations(editor: vscode.TextEditor, violations: Violation[]) {
    // Clear previous decorations
    editor.setDecorations(decorationType, []);

    if (violations.length === 0) {
        return;
    }

    const decorations: vscode.DecorationOptions[] = [];
    const document = editor.document;
    const text = document.getText();

    // Group violations by object name to avoid duplicate highlights
    const violationsByObject = new Map<string, Violation[]>();
    violations.forEach(violation => {
        if (!violationsByObject.has(violation.object)) {
            violationsByObject.set(violation.object, []);
        }
        violationsByObject.get(violation.object)!.push(violation);
    });

    // Find and highlight each problematic object
    violationsByObject.forEach((objectViolations, objectName) => {
        // Create regex to find all occurrences of the object name
        // Use word boundaries to avoid partial matches
        const regex = new RegExp(`\\b${escapeRegExp(objectName)}\\b`, 'g');
        let match;
        
        while ((match = regex.exec(text)) !== null) {
            const startPos = document.positionAt(match.index);
            const endPos = document.positionAt(match.index + match[0].length);
            
            // Create hover message with all violations for this object
            const hoverMessages = objectViolations.map(v => v.message);
            const hoverText = hoverMessages.join('\\n\\n');
            
            decorations.push({
                range: new vscode.Range(startPos, endPos),
                hoverMessage: new vscode.MarkdownString(`**Strata Taint Analysis:**\\n\\n${hoverText}`)
            });
        }
    });

    // Apply all decorations
    editor.setDecorations(decorationType, decorations);
}

function escapeRegExp(string: string): string {
    return string.replace(/[.*+?^${}()|[\\]\\\\]/g, '\\\\$&');
}

function runUninitializedFieldAccess() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showErrorMessage('No active editor found');
        return;
    }

    const languageId = editor.document.languageId;
    const filename = editor.document.fileName;
    const fileExtension = path.extname(filename);
    
    if (languageId !== 'typescript' && languageId !== 'python') {
        vscode.window.showErrorMessage('Please open a TypeScript (.ts) or Python (.py) file');
        return;
    }

    // Determine which runner script to use based on file extension
    let command: string;
    if (fileExtension === '.py') {
        command = `./runners/check_python_uninit_field.sh "${filename}"`;
    } else if (fileExtension === '.ts') {
        command = `./runners/check_typescript_uninit_field.sh "${filename}"`;
    } else {
        vscode.window.showErrorMessage('Unsupported file extension. Please use .ts or .py files');
        return;
    }
    
    // Show progress indicator
    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: `Running Strata Uninitialized Field Access Analysis (${fileExtension})...`,
        cancellable: false
    }, async (progress) => {
        return new Promise<void>((resolve, reject) => {
            // Get the workspace root to run the command from the right directory
            const workspaceRoot = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
            if (!workspaceRoot) {
                vscode.window.showErrorMessage('No workspace folder found');
                resolve();
                return;
            }

            exec(command, { cwd: '/Users/mzwangg/Strata' }, (error, stdout, stderr) => {
                if (error) {
                    vscode.window.showErrorMessage(`Analysis failed: ${error.message}`);
                    resolve();
                    return;
                }

                try {
                    // Parse the JSON output directly from stdout
                    const result: AnalysisResult = JSON.parse(stdout.trim());
                    
                    // Apply the analysis results to the editor
                    highlightViolations(editor, result.violations);
                    
                    // Show summary message
                    if (result.violations.length === 0) {
                        vscode.window.showInformationMessage('✅ No uninitialized field access violations found!');
                    } else {
                        vscode.window.showWarningMessage(
                            `⚠️ Found ${result.violations.length} uninitialized field access violation(s)`
                        );
                    }
                    
                } catch (parseError) {
                    vscode.window.showErrorMessage(`Failed to parse analysis results: ${parseError}`);
                }
                
                resolve();
            });
        });
    });
}

function runValueValidation() {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showErrorMessage('No active editor found');
        return;
    }

    const languageId = editor.document.languageId;
    const filename = editor.document.fileName;
    const fileExtension = path.extname(filename);
    
    if (languageId !== 'typescript' && languageId !== 'python') {
        vscode.window.showErrorMessage('Please open a TypeScript (.ts) or Python (.py) file');
        return;
    }

    // Determine which runner script to use based on file extension
    let command: string;
    if (fileExtension === '.py') {
        command = `./runners/check_python_value_validation.sh "${filename}"`;
    } else if (fileExtension === '.ts') {
        command = `./runners/check_typescript_value_validation.sh "${filename}"`;
    } else {
        vscode.window.showErrorMessage('Unsupported file extension. Please use .ts or .py files');
        return;
    }
    
    // Show progress indicator
    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: `Running Strata Value Validation Analysis (${fileExtension})...`,
        cancellable: false
    }, async (progress) => {
        return new Promise<void>((resolve, reject) => {
            // Get the workspace root to run the command from the right directory
            const workspaceRoot = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
            if (!workspaceRoot) {
                vscode.window.showErrorMessage('No workspace folder found');
                resolve();
                return;
            }

            exec(command, { cwd: '/Users/mzwangg/Strata' }, (error, stdout, stderr) => {
                if (error) {
                    vscode.window.showErrorMessage(`Analysis failed: ${error.message}`);
                    resolve();
                    return;
                }

                try {
                    // Parse the JSON output directly from stdout
                    const result: AnalysisResult = JSON.parse(stdout.trim());
                    
                    // Apply the analysis results to the editor
                    highlightViolations(editor, result.violations);
                    
                    // Show summary message
                    if (result.violations.length === 0) {
                        vscode.window.showInformationMessage('✅ No value validation violations found!');
                    } else {
                        vscode.window.showWarningMessage(
                            `⚠️ Found ${result.violations.length} value validation violation(s)`
                        );
                    }
                    
                } catch (parseError) {
                    vscode.window.showErrorMessage(`Failed to parse analysis results: ${parseError}`);
                }
                
                resolve();
            });
        });
    });
}

export function deactivate() {
    if (decorationType) {
        decorationType.dispose();
    }
}
