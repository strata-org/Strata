function op1(x: number, y: number): number {
    function op2(a: number, b: number): number {
        return a + b;
    }
    let returnVal: number =  op2(x, y);
    return returnVal
}

let result: number = op1(4, 7);
