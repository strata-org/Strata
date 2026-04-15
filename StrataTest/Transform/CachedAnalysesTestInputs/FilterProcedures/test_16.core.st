program Core;
procedure p0() returns () {
};
procedure p1() returns () {
  call p0();
};
procedure p2() returns () {
  call p1();
};
procedure p3() returns () {
  call p2();
};
