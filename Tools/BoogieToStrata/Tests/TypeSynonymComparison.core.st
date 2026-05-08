program Core;

type i64 := int;
type ref := i64;

function sle_ref_bool(p1 : ref, p2 : ref) : (bool) {
  (p1 <= p2)
}

function slt_ref_bool(p1 : ref, p2 : ref) : (bool) {
  (p1 < p2)
}

procedure main(out r : int)
spec {
  ensures (r == 0);
}
{
  entry: {
    assert sle_ref_bool(1, 2);
    r := 0;
  }
};
