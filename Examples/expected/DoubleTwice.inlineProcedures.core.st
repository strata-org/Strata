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
  Double$inlined: {
    var Double_n_3 : int := x;
    var Double_result_4 : int;
    Double_result_4 := Double_n_3 + Double_n_3;
    output := Double_result_4;
  }
  Double$inlined: {
    var Double_n_0 : int := output;
    var Double_result_1 : int;
    Double_result_1 := Double_n_0 + Double_n_0;
    output := Double_result_1;
  }
};
