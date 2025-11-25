// Test handling of var, const, and let in block scopes

let x = 0;
const y = 1;


function testLet(): number {
        return x; // Should be able to access outer scope variable x
    }

function testVar(): number {
        if (true) {
            var a = 10;
        }
        return a; // Should be able to access var a declared in block
    }

function testConst(): number {
    if (true) {
        const b = 20;
        return b; // const is block-scoped, accessible within this block
    }
    // return b; // Would cause error: b is not accessible here
}

// function errorLet(): number {
//     if (true) {
//         let c = 30;
//     }
//     return c; // Should cause error: c is not accessible here
// }

let letResult = testLet();
let varResult = testVar();
let constResult = testConst();
// let errorLetResult = errorLet(); // Uncommenting this line should cause an error