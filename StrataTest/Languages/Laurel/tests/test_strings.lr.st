procedure main() {
    var s1: string := "hello";
    var s2: string := " world";
    var result: string := s1 ++ s2;
    assert result == "hello world";

    var a: string := "abc";
    var b: string := "abc";
    assert a == b;
}
