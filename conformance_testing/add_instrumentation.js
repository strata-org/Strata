const fs = require("fs");
const path = require("path");
const parser = require("@babel/parser");
const traverse = require("@babel/traverse").default;
const generate = require("@babel/generator").default;
const t = require("@babel/types");

const inputPath = process.argv[2];

function instrumentFile(filePath) {
    const code = fs.readFileSync(filePath, "utf8");
    let ast;
    try {
        ast = parser.parse(code, {
        sourceType: "module",
        plugins: ["typescript"],
        strictMode: false
        });
    } catch (err) {
        console.log(`failed to parse ${filePath}`);
        return;
    }

    const topLevelVars = new Set();

    traverse(ast, {
    VariableDeclaration(path) {
        if (path.parent.type === "Program") {
        for (const decl of path.node.declarations) {
            if (t.isIdentifier(decl.id)) {
            topLevelVars.add(decl.id.name);
            }
        }
        }
    }
    });

    // Create JSON output: console.log(JSON.stringify({x: x, y: y}))
    if (topLevelVars.size > 0) {
        const objectProperties = Array.from(topLevelVars).map(name =>
            t.objectProperty(t.identifier(name), t.identifier(name))
        );
        
        const jsonStringifyCall = t.callExpression(
            t.memberExpression(t.identifier("JSON"), t.identifier("stringify")),
            [t.objectExpression(objectProperties)]
        );
        
        const consoleLogStatement = t.expressionStatement(
            t.callExpression(
                t.memberExpression(t.identifier("console"), t.identifier("log")),
                [jsonStringifyCall]
            )
        );

        ast.program.body.push(consoleLogStatement);
    }

    // Output result
    const output = generate(ast).code;
    fs.mkdirSync(path.dirname(filePath), { recursive: true });
    fs.writeFileSync(filePath, output, "utf8");
}

// Check if input is a file or directory
if (fs.statSync(inputPath).isDirectory()) {
    // Directory mode (for backward compatibility)
    function walkDir(inputBase) {
      fs.readdirSync(inputBase, { withFileTypes: true }).forEach(entry => {
        const inPath = path.join(inputBase, entry.name);

        if (entry.isDirectory()) {
          walkDir(inPath);
        } else if (entry.isFile() && (entry.name.endsWith(".ts") || entry.name.endsWith(".js"))) {
            instrumentFile(inPath);
        }
      });
    }
    walkDir(inputPath);
} else {
    // Single file mode
    instrumentFile(inputPath);
}
