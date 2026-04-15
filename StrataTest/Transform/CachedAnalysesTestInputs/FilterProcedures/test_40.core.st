program Core;
procedure p0() returns () {
  call p1();
  call p2();
};
procedure p1() returns () {
  call p3();
  call p4();
};
procedure p2() returns () {
  call p4();
  call p5();
};
procedure p3() returns () {
  call p6();
};
procedure p4() returns () {
  call p6();
};
procedure p5() returns () {
};
procedure p6() returns () {
};
