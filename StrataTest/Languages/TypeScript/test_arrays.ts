// Basic array literal
// TODO: add assertion tests AST test + verification test (as a user) pre/post-condi
let numbers: number[] = [1, 2, 3, 4];

// Empty array initialization
let empty: number[] = [];

// Array element access
let first: number = numbers[0];
let last: number = numbers[4];

// Dynamic array indexing
let index: number = 2;
let element: number = numbers[index];

// Array element assignment
numbers[0] = 10;
numbers[index] = 30;

// Array in expressions
let sum: number = numbers[0] + numbers[1];
let isEqual: boolean = numbers[2] == 3

let strings: string[] = ["hello", "world"];

const numLen: number = numbers.length;
const strLen: number = strings.length;

// Mixed with objects
// let data: number[] = [100, 200, 300];
// let obj = {0: data[0], 1: data[1], 2: data[2]};

// Nested arrays
// let matrix: number[][] = [[1, 2], [3, 4]];

// Array Push and Pop
numbers.push(6);
let popped: number | undefined = numbers.pop();

// Pop empty array
empty.pop();
