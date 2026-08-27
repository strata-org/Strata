program Core;

procedure Double (n : int, out result : int)
spec {
  ensures [double_correct]: result == int.mul(n, 2);
  } {
  result := int.add(n, n);
};
procedure TestProc (x : int, out output : int)
spec {
  ensures [testProc_result]: output == int.mul(x, 4);
  } {
  $__inline1_Double$inlined: {
    var $__inline1_n : int := x;
    var $__inline1_result : int;
    $__inline1_result := int.add($__inline1_n, $__inline1_n);
    output := $__inline1_result;
  }
  $__inline2_Double$inlined: {
    var $__inline2_n : int := output;
    var $__inline2_result : int;
    $__inline2_result := int.add($__inline2_n, $__inline2_n);
    output := $__inline2_result;
  }
};
