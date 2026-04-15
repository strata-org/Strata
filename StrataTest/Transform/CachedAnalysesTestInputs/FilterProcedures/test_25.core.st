program Core;
procedure p0() returns () {
  call p1();
};
procedure p1() returns () {
  call p2();
};
procedure p2() returns () {
  call p3();
  call p4();
};
procedure p3() returns () {
};
procedure p4() returns () {
};
