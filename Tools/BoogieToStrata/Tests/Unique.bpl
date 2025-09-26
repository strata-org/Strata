type T0;
type T1;

const unique c0a : T0;
const unique c0b : T0;
const unique c0c : T0;

const unique c1a : T1;
const unique c1b : T1;
const unique c1c : T1;

procedure P0() {
    assert c0a == c0b;
    assert c0a != c0c;
}

procedure P1() {
    assert c1a == c1b;
    assert c1a != c1c;
}
