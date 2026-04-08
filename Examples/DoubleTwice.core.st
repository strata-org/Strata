program Core;

procedure Double(n : int) returns (result : int)
spec {
  ensures [double_correct]: (result == n * 2);
}
{
  result := n + n;
};

procedure TestProc(x : int) returns (output : int)
spec {
  ensures [testProc_result]: (output == x * 4);
}
{
  call output := Double(x);
  call output := Double(output);
};
