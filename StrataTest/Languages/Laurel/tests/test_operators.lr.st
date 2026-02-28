procedure main() {
    var a: int := 10;
    var b: int := 3;
    var x: int := a - b;
    assert x == 7;
    var y: int := x * 2;
    assert y == 14;
    var z: int := y / 2;
    assert z == 7;
    var r: int := 17 % 5;
    assert r == 2;

    var t: bool := true;
    var f: bool := false;
    var c: bool := !f;
    assert c == true;
}
