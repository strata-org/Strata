"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.deactivate = exports.activate = void 0;
const vscode = require("vscode");
const path = require("path");
const child_process_1 = require("child_process");
let decorationType;
function activate(context) {
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
exports.activate = activate;
function runHeapHigherOrderTaintAnalysis() {
    const visibleEditors = vscode.window.visibleTextEditors;
    if (visibleEditors.length === 0) {
        vscode.window.showErrorMessage('No open editors found');
        return;
    }
    // Filter editors to only supported file types
    const supportedEditors = visibleEditors.filter(editor => {
        const fileExtension = path.extname(editor.document.fileName);
        return fileExtension === '.py' || fileExtension === '.ts';
    });
    if (supportedEditors.length === 0) {
        vscode.window.showErrorMessage('No TypeScript (.ts) or Python (.py) files are open');
        return;
    }
    // Show progress indicator
    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: `Running Heap Higher Order Taint Analysis on ${supportedEditors.length} file(s)...`,
        cancellable: false
    }, async (progress) => {
        const results = [];
        const promises = supportedEditors.map(editor => {
            return new Promise((resolve) => {
                const filename = editor.document.fileName;
                const fileExtension = path.extname(filename);
                let command;
                if (fileExtension === '.py') {
                    command = `./runners/check_python_heaphigherorder_taint.sh "${filename}"`;
                }
                else {
                    command = `./runners/check_typescript_heaphigherorder_taint.sh "${filename}"`;
                }
                (0, child_process_1.exec)(command, { cwd: '/Users/mzwangg/Strata' }, (error, stdout, stderr) => {
                    if (error) {
                        console.error(`Analysis failed for ${filename}: ${error.message}`);
                        resolve();
                        return;
                    }
                    try {
                        const result = JSON.parse(stdout.trim());
                        results.push({ editor, violations: result.violations });
                    }
                    catch (parseError) {
                        console.error(`Failed to parse results for ${filename}: ${parseError}`);
                    }
                    resolve();
                });
            });
        });
        await Promise.all(promises);
        // Apply highlighting to all editors after all analyses complete
        results.forEach(({ editor, violations }) => {
            highlightViolations(editor, violations);
        });
        vscode.window.showInformationMessage(`✅ Heap Higher Order Taint Analysis completed on ${supportedEditors.length} file(s)`);
    });
}
function runTaintAnalysis() {
    const visibleEditors = vscode.window.visibleTextEditors;
    if (visibleEditors.length === 0) {
        vscode.window.showErrorMessage('No open editors found');
        return;
    }
    // Filter editors to only supported file types
    const supportedEditors = visibleEditors.filter(editor => {
        const fileExtension = path.extname(editor.document.fileName);
        return fileExtension === '.py' || fileExtension === '.ts';
    });
    if (supportedEditors.length === 0) {
        vscode.window.showErrorMessage('No TypeScript (.ts) or Python (.py) files are open');
        return;
    }
    // Show progress indicator
    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: `Running Taint Analysis on ${supportedEditors.length} file(s)...`,
        cancellable: false
    }, async (progress) => {
        const results = [];
        const promises = supportedEditors.map(editor => {
            return new Promise((resolve) => {
                const filename = editor.document.fileName;
                const fileExtension = path.extname(filename);
                let command;
                if (fileExtension === '.py') {
                    command = `./runners/check_python_taint.sh "${filename}"`;
                }
                else {
                    command = `./runners/check_typescript_taint.sh "${filename}"`;
                }
                (0, child_process_1.exec)(command, { cwd: '/Users/mzwangg/Strata' }, (error, stdout, stderr) => {
                    if (error) {
                        console.error(`Analysis failed for ${filename}: ${error.message}`);
                        resolve();
                        return;
                    }
                    try {
                        const result = JSON.parse(stdout.trim());
                        results.push({ editor, violations: result.violations });
                    }
                    catch (parseError) {
                        console.error(`Failed to parse results for ${filename}: ${parseError}`);
                    }
                    resolve();
                });
            });
        });
        await Promise.all(promises);
        // Apply highlighting to all editors after all analyses complete
        results.forEach(({ editor, violations }) => {
            highlightViolations(editor, violations);
        });
        vscode.window.showInformationMessage(`✅ Taint Analysis completed on ${supportedEditors.length} file(s)`);
    });
}
function highlightViolations(editor, violations) {
    // Clear previous decorations
    editor.setDecorations(decorationType, []);
    if (violations.length === 0) {
        return;
    }
    const decorations = [];
    const document = editor.document;
    const text = document.getText();
    // Group violations by object name to avoid duplicate highlights
    const violationsByObject = new Map();
    violations.forEach(violation => {
        if (!violationsByObject.has(violation.object)) {
            violationsByObject.set(violation.object, []);
        }
        violationsByObject.get(violation.object).push(violation);
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
function escapeRegExp(string) {
    return string.replace(/[.*+?^${}()|[\\]\\\\]/g, '\\\\$&');
}
function runUninitializedFieldAccess() {
    const visibleEditors = vscode.window.visibleTextEditors;
    if (visibleEditors.length === 0) {
        vscode.window.showErrorMessage('No open editors found');
        return;
    }
    // Filter editors to only supported file types
    const supportedEditors = visibleEditors.filter(editor => {
        const fileExtension = path.extname(editor.document.fileName);
        return fileExtension === '.py' || fileExtension === '.ts';
    });
    if (supportedEditors.length === 0) {
        vscode.window.showErrorMessage('No TypeScript (.ts) or Python (.py) files are open');
        return;
    }
    // Show progress indicator
    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: `Running Uninitialized Field Access Analysis on ${supportedEditors.length} file(s)...`,
        cancellable: false
    }, async (progress) => {
        const results = [];
        const promises = supportedEditors.map(editor => {
            return new Promise((resolve) => {
                const filename = editor.document.fileName;
                const fileExtension = path.extname(filename);
                let command;
                if (fileExtension === '.py') {
                    command = `./runners/check_python_uninit_field.sh "${filename}"`;
                }
                else {
                    command = `./runners/check_typescript_uninit_field.sh "${filename}"`;
                }
                (0, child_process_1.exec)(command, { cwd: '/Users/mzwangg/Strata' }, (error, stdout, stderr) => {
                    if (error) {
                        console.error(`Analysis failed for ${filename}: ${error.message}`);
                        resolve();
                        return;
                    }
                    try {
                        const result = JSON.parse(stdout.trim());
                        results.push({ editor, violations: result.violations });
                    }
                    catch (parseError) {
                        console.error(`Failed to parse results for ${filename}: ${parseError}`);
                    }
                    resolve();
                });
            });
        });
        await Promise.all(promises);
        // Apply highlighting to all editors after all analyses complete
        results.forEach(({ editor, violations }) => {
            highlightViolations(editor, violations);
        });
        vscode.window.showInformationMessage(`✅ Uninitialized Field Access Analysis completed on ${supportedEditors.length} file(s)`);
    });
}
function runValueValidation() {
    const visibleEditors = vscode.window.visibleTextEditors;
    if (visibleEditors.length === 0) {
        vscode.window.showErrorMessage('No open editors found');
        return;
    }
    // Filter editors to only supported file types
    const supportedEditors = visibleEditors.filter(editor => {
        const fileExtension = path.extname(editor.document.fileName);
        return fileExtension === '.py' || fileExtension === '.ts';
    });
    if (supportedEditors.length === 0) {
        vscode.window.showErrorMessage('No TypeScript (.ts) or Python (.py) files are open');
        return;
    }
    // Show progress indicator
    vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: `Running Value Validation Analysis on ${supportedEditors.length} file(s)...`,
        cancellable: false
    }, async (progress) => {
        const results = [];
        const promises = supportedEditors.map(editor => {
            return new Promise((resolve) => {
                const filename = editor.document.fileName;
                const fileExtension = path.extname(filename);
                let command;
                if (fileExtension === '.py') {
                    command = `./runners/check_python_value_validation.sh "${filename}"`;
                }
                else {
                    command = `./runners/check_typescript_value_validation.sh "${filename}"`;
                }
                (0, child_process_1.exec)(command, { cwd: '/Users/mzwangg/Strata' }, (error, stdout, stderr) => {
                    if (error) {
                        console.error(`Analysis failed for ${filename}: ${error.message}`);
                        resolve();
                        return;
                    }
                    try {
                        const result = JSON.parse(stdout.trim());
                        results.push({ editor, violations: result.violations });
                    }
                    catch (parseError) {
                        console.error(`Failed to parse results for ${filename}: ${parseError}`);
                    }
                    resolve();
                });
            });
        });
        await Promise.all(promises);
        // Apply highlighting to all editors after all analyses complete
        // Use setTimeout to ensure UI has updated and force refresh decorations
        setTimeout(() => {
            results.forEach(({ editor, violations }) => {
                // Clear existing decorations first
                editor.setDecorations(decorationType, []);
                // Then apply new ones
                highlightViolations(editor, violations);
            });
        }, 100);
        vscode.window.showInformationMessage(`✅ Value Validation Analysis completed on ${supportedEditors.length} file(s)`);
    });
}
function deactivate() {
    if (decorationType) {
        decorationType.dispose();
    }
}
exports.deactivate = deactivate;
//# sourceMappingURL=extension_multi_window.js.map