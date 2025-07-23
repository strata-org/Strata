// RUN: %parallel-boogie -noVerify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"



type a;
type b;
type C c d;
type C2 c d = C d c;

function g0([C2 a b]int) returns (int);
function g1([C2 b a]int) returns (int);
function g2([C a b]int) returns (int);
function g3([C b a]int) returns (int);

const c0 : [C2 a b]int;
const c1 : [C2 b a]int;
const c2 : [C a b]int;
const c3 : [C b a]int;

axiom g0(c0) == 0;
axiom g3(c0) == 0;
axiom g1(c1) == 0;
axiom g2(c1) == 0;
axiom g1(c2) == 0;
axiom g2(c2) == 0;
axiom g0(c3) == 0;
axiom g3(c3) == 0;
