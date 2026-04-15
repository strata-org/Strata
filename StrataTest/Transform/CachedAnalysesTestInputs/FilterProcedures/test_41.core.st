program Core;
procedure p0() returns () {
  call p1();
};
procedure p1() returns () {
  call p2();
  call p3();
};
procedure p2() returns () {
  call p4();
};
procedure p3() returns () {
  call p5();
};
procedure p4() returns () {
  call p6();
};
procedure p5() returns () {
  call p6();
};
procedure p6() returns () {
};
