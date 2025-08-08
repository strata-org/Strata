// Test TypeScript file with function definitions and calls
// Similar to testFunction.py but in TypeScript syntax

function add_numbers(x: number, y: number): number {
    let result: number = x + y;
    return result;
}

// Main program
let a: number = 5;
let b: number = 3;
let c: number = add_numbers(a, b);
