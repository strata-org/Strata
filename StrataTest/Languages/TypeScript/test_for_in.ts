let obj = {0: 10, 1: 20, 2: 30};
let sum = 0;
for (let key in obj) {
    sum = sum + obj[key];
}