// Test handling of var, const, and let in block scopes

let x = 0;
const y = 1;
var z = 2;


// function testBlockScope() {
//     if (true) {
//         var x = 10;
//         let y = 20;
//         const z = 30;
//     } 
//     var x_out = x; // Should be accessible
//     let y = 0;
//     let z = 0;
//     return x_out;
// }

// let blockResult = testBlockScope();