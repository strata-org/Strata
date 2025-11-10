let a = 5;
let b = 10;
let c = 15;

function multiply(x: number, y: number): number {
    let c = 20; // Define local variable with same name as outer scope variable
    return x * y * c;
}

function sum(x: number, y: number): number {
    a = 10; // Modify outer scope variable
    return x + y + a;
}

let product = multiply(b, c); // Correct: product = 3000
let result = sum(a, b); // Correct: result = 25
// Value mismatch: a = 5 after sum function call, should be a = 10
