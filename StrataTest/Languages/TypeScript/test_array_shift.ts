let numbers1: number[] = [1, 2, 3, 4];

// Shift removes the first element
let shifted: number | undefined = numbers1.shift();

// Array after shift
// nums = [2, 3, 4]

// Shift on empty array
let emptyArr: number[] = [];
let shiftedEmpty: number | undefined = emptyArr.shift();

// Unshift adds an element to the beginning
let newLen: number = numbers1.unshift(0);

// Array after unshift
// nums = [0, 2, 3, 4]

// Unshift multiple elements
let moreLen: number = numbers1.unshift(-2, 1)
