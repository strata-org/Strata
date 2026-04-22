program Core;

procedure Double(n : int, out result : int)
spec {
  ensures [double_correct]: (result == n * 2);
}
{
  result := n + n;
};

procedure TestProc(x : int, out output : int)
spec {
  ensures [testProc_result]: (output == x * 4);
}
{
  call Double(x, out output);
  call Double(output, out output);
};
