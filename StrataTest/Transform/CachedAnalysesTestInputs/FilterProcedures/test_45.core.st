program Core;
procedure p0() returns () {
  call p1();
  call p2();
  call p3();
};
procedure p1() returns () {
  call p4();
};
procedure p2() returns () {
  call p4();
  call p5();
};
procedure p3() returns () {
  call p5();
};
procedure p4() returns () {
};
procedure p5() returns () {
};
