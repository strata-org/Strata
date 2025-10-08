type A = { name: string };
type B = { age: number };

type Person = A & B;

const p: Person = {
    name: "Julia",
    age: 23,
};