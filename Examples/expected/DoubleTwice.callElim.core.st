program Core;

procedure Double (n : int, out result : int)
spec {
  ensures [double_correct]: result == n * 2;
  } {
  result := n + n;
};
procedure TestProc (x : int, out output : int)
spec {
  ensures [testProc_result]: output == x * 4;
  } {
  var tmp_arg_3 : int := x;
  var tmp_output_4 : int := output;
  havoc output;
  assume [callElimAssume_double_correct_5]: output == tmp_arg_3 * 2;
  var tmp_arg_0 : int := output;
  var tmp_output_1 : int := output;
  havoc output;
  assume [callElimAssume_double_correct_2]: output == tmp_arg_0 * 2;
};
