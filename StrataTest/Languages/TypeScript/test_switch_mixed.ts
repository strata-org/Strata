// Test switch with mixed break and fallthrough
let x: number = 2;
let result: number = 0;

switch (x) {
  case 1:
    result = 10;
    break;
  case 2:
    result = 20;
  case 3:
    result = 30;
    break;
  default:
    result = 40;
}

result;

