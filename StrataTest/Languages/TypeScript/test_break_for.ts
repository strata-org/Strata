// Test for loop with break statement
let sum: number = 0;

for (let i: number = 1; i <= 5; i = i + 1) {
  if (i === 3) {
    break;  // Should break when i equals 3
  }
  sum = sum + i;
}
// Expected: sum should be 3 (1 + 2), since loop breaks at i=3
