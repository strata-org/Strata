procedure main() {
    var x: int := 5;
    var result: int := 0;

    if (x == 5) {
        result := 10;
    } else {
        result := 20;
    }
    assert result == 10;

    var y: int := 7;
    var status: int := 0;

    if (y == 7) {
        if (y == 7) {
            status := 1;
        } else {
            status := 2;
        }
    } else {
        status := 3;
    }
    assert status == 1;

    var a: int := 10;
    var b: int := 0;

    if (a > 3) {
        b := 1;
    } else {
        b := 2;
    }
    assert b == 1;
}
