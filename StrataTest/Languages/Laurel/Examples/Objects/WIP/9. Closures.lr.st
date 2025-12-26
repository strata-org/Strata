/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/
// Work in progress

/*
Dafny example:

method hasClosure() returns (r: int) 
  ensures r == 13
{
  var x: int := 1;
  x := x + 2;
  var f: (int) -> int := (y: int) => assert x == 3; y + x + 4;
  x := x + 5; // update is lost.
  return f(6);
}

class Wrapper {
  var x: int
}

method hasClosureAndWrapper(wrapper: Wrapper) returns (r: int) 
  modifies wrapper
  ensures r == 15
{
  wrapper.x := 3;
  var f: (int) ~> int := (y: int) reads wrapper => y + wrapper.x + 4;
  wrapper.x := 5;
  r := f(6);
}
*/

/* 

Java example:

public void myMethod() {
    final String prefix = "Hello";
    int count = 0; // effectively final (not modified after initialization)
    
    class LocalGreeter {
        void greet(String name) {
            System.out.println(prefix + " " + name); // OK: accesses local variable
            // count++; // ERROR: would need to be effectively final
        }
    }
    
    LocalGreeter greeter = new LocalGreeter();
    greeter.greet("World");
}
*/

/*
C# example:

public Func<int> CreateCounter() {
    int count = 0;  // local variable
    return () => count++;  // lambda captures 'count'
}

// Usage:
var counter1 = CreateCounter();
Console.WriteLine(counter1());  // 0
Console.WriteLine(counter1());  // 1
Console.WriteLine(counter1());  // 2

var counter2 = CreateCounter();  // Independent copy
Console.WriteLine(counter2());  // 0
*/

/*
What Dafny does:
- The closure refers to variables with their values at the point where the closure is defined.
- The body is transparant.
- The heap is an implicit argument to the closure, so it can change.

I think all of the above is good, and we can use it for all three cases.
In the Java example, we can create a separate closure for each method of the type closure.

In the C# example, preprocessing should create a separate class that holds the on-heap variable,
so in affect there no longer are any variables captured by a closure.

*/

// Option A: first class procedures
procedure hasClosure() returns (r: int)
  ensures r == 7
{
  var x = 3;
  var aClosure: procedure() returns (r: int) := closure {
    r = x + 4;
  }
  x = 100;
  aClosure();
}


// Option B: type closures
composite ATrait {
  procedure foo() returns (r: int) ensures r > 0 {
    abstract
  }
}

procedure hasClosure() returns (r: int)
  ensures r == 7
{
  var x = 3;
  var aClosure := closure extends ATrait {
    procedure foo() returns (r: int) 
    {
      r = x + 4;
    }
  }
  x = 100;
  aClosure.foo();
}
