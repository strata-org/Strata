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
  var $__callElimTmp_arg_0 : int := x;
  var $__callElimTmp_output_1 : int := output;
  havoc output;
  assume [$__callElimAssume_double_correct_2]: output == int.mul($__callElimTmp_arg_0, 2);
  var $__callElimTmp_arg_3 : int := output;
  var $__callElimTmp_output_4 : int := output;
  havoc output;
  assume [$__callElimAssume_double_correct_5]: output == int.mul($__callElimTmp_arg_3, 2);
};
