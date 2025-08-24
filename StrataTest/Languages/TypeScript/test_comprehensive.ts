// Comprehensive test combining multiple features
function calculate(base: number, multiplier: number): number {
    let temp: number = base * multiplier;
    if (temp > 100) {
        return temp - 10;
    } else {
        return temp + 5;
    }
}

let input: number = 15;
let factor: number = 3;
let result: number = calculate(input, factor);
let isLarge: boolean = result > 50;
let status: string = isLarge ? "big" : "small";
