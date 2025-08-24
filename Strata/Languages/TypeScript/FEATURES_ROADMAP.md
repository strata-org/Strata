# TypeScript Frontend - Feature Roadmap

This document outlines JavaScript/TypeScript features that need to be implemented in the Strata TypeScript frontend. Features are organized by complexity and importance for educational purposes.

## Currently Supported 

### Basic Data Types
- `number` literals and arithmetic operations
- `string` literals
- `boolean` literals and logical operations
- `null` values

### Basic Expressions
- Binary expressions: `+`, `-`, `*`, `/`, `%`, `==`, `!=`, `<`, `>`, `<=`, `>=`
- Logical expressions: `&&`, `||`
- Unary expressions: `-`, `!`
- Assignment expressions: `=`
- Conditional expressions: `condition ? true_val : false_val`
- Member expressions with numeric keys: `obj[0]`, `obj[1]`
- Function call expressions: `func(arg1, arg2)`

### Basic Statements
- Variable declarations: `let x: number = 5;`
- Function declarations: `function name(params): returnType { ... }`
- If statements: `if (condition) { ... } else { ... }`
- Return statements: `return value;`
- Expression statements: `x + 5;`
- Block statements: `{ ... }`

### Basic Objects
- Objects with numeric keys only: `{0: value1, 1: value2}`
- Numeric member access: `obj[0]`

---
# Features still needed

Here's a list of features that we don't support for TypeScript yet. I put these in a general order of "basic-ness" but they're open to interpretation. This isn't a comprehensive list, but just something to get the creative juices flowing.


## Basic (ish) Features 
These should *probably* be done first.
### Control Flow
- **While loops**: `while (condition) { ... }`
- **For loops**: `for (let i = 0; i < 10; i++) { ... }`
- **Break statements**: `break;`
- **Continue statements**: `continue;`
- **Switch statements**: `switch (value) { case 1: ... }`

### Data Structures
- **Arrays**: `[1, 2, 3]`, `let arr: number[] = [];`
- **Array indexing**: `arr[0]`, `arr[i]`
- **Array length**: `arr.length`
- **String properties**: `str.length`
- **Object string properties**: `{name: "value", age: 30}`
- **String member access**: `obj.name`, `obj["name"]`

### Enhanced Functions
- **Function expressions**: `let f = function() { ... }`
- **Arrow functions**: `(x) => x * 2`, `() => { ... }`
- **Nested functions**: Functions declared inside other functions

---

## Intermediate Features 

### Loops
- **For-in loops**: `for (let key in obj) { ... }`
- **For-of loops**: `for (let item of array) { ... }`

### Scope and Closures
- **Closures**: Functions capturing outer scope variables
- **Block scoping**: `let`/`const` vs `var` differences

### Array Operations
- **Array methods**: `.push()`, `.pop()`, `.shift()`, `.unshift()`
- **Array iteration**: `.forEach()`, `.map()`, `.filter()`
- **Array properties**: `.slice()`, `.concat()`, `.join()`

### Type System (TypeScript Specific)
- **Interfaces**: `interface Person { name: string; }`
- **Type aliases**: `type ID = string | number`
- **Union types**: `string | number`
- **Intersection types**: `A & B`
- **Generic functions**: `function id<T>(x: T): T`
- **Generic classes**: `class Container<T> { ... }`
- **Enums**: `enum Color { Red, Green, Blue }`
- **Type guards**: `typeof`, `instanceof`
---

## Advanced Features 

### Object-Oriented Programming
- **Classes**: `class Point { constructor(x, y) { ... } }`
- **Class methods**: Instance and static methods
- **Inheritance**: `class Child extends Parent { ... }`
- **Super calls**: `super()`, `super.method()`
- **Private fields**: `#privateField`

### Advanced Functions
- **Rest parameters**: `function f(...args) { ... }`
- **Default parameters**: `function f(x = 5) { ... }`
- **Destructuring parameters**: `function f({x, y}) { ... }`

### Modern JavaScript Features
- **Destructuring assignment**: `let {x, y} = point`, `let [a, b] = array`
- **Spread operator**: `...array`, `{...obj}`
- **Template literals**: `` `Hello ${name}` ``
- **Object shorthand**: `{x, y}` instead of `{x: x, y: y}`

### Error Handling
- **Try/catch/finally**: Exception handling
- **Throw statements**: `throw new Error("message")`
- **Error objects**: `new Error()`, custom error types

### Advanced Object Features
- **Prototype chain**: `obj.prototype`, `Object.create()`
- **Property descriptors**: `Object.defineProperty()`
- **Getters/setters**: `get prop() { ... }`, `set prop(value) { ... }`
- **Symbol properties**: `Symbol()`, `obj[Symbol.iterator]`

### Advanced Control Flow
- **Generators**: `function* gen() { yield 1; }`
- **Iterators**: `obj[Symbol.iterator]`
- **For-await-of**: `for await (let item of asyncIterable)`

### Advanced Language Features
- **Optional chaining**: `obj?.prop?.method?.()`
- **Nullish coalescing**: `value ?? default`
- **Logical assignment**: `||=`, `&&=`, `??=`
- **Private class methods**: `#method() { ... }`
- **Static class blocks**: `static { ... }`

### Concurrency
- **Promises**: `new Promise()`, `.then()`, `.catch()`, `.finally()`
- **Async functions**: `async function f() { ... }`
- **Await expressions**: `await promise`
- **Promise combinators**: `Promise.all()`, `Promise.race()`

### Advanced Function Features
- **Function.prototype methods**: `.call()`, `.apply()`, `.bind()`
- **Arguments object**: `arguments[0]`
- **Function properties**: `func.name`, `func.length`


### Module System
- **Import statements**: `import { x } from 'module'`
- **Export statements**: `export const x = 5`
- **Default exports**: `export default class`
- **Dynamic imports**: `import('module')`

---

## Notes for Students

- Each feature requires changes to both `js_ast.lean` and `TS_to_Strata.lean`
- Test incrementally - get simple cases working before complex ones
- Use conformance tests to validate correctness against native execution
- Some features will require extending Strata's dialects

