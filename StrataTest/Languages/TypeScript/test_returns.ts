// Test return statements
function getMax(a: number, b: number): number {
    if (a > b) {
        return a;
    }
    return b;
}

let x: number = 15;
let y: number = 23;
let maximum: number = getMax(x, y);
