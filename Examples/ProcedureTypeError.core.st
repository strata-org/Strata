program Core;
procedure SumPositive(a: int, b: int) returns (c: int)
spec {
    requires [precond1]: 0 <= a;
    requires [precond2]: c <= b;
}
{
    c := a + b;
};