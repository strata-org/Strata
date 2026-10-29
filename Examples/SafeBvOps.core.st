program Core;

procedure safe_bv_ops(x: bv W32, y: bv W32, out r: bv W32)
{
    var a: bv W32;
    var b: bv W32;
    var c: bv W32;
    var d: bv W32;
    var e: bv W32;
    var f: bv W32;
    a := bv32.safeAdd(x, y);
    b := bv32.safeSub(x, y);
    c := bv32.safeMul(x, y);
    d := bv32.safeNeg(x);
    e := bv32.safeSDiv(x, y);
    f := bv32.safeSMod(x, y);
    r := a;
};
