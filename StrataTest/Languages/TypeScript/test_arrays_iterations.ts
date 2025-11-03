// forEach
let arr = [1, 2, 3, 4, 5];

arr.forEach((value: number, index: number) => {
    arr[index] = value * 2;
});

// map
let mappedArr = arr.map((value: number) => {return value + 1});