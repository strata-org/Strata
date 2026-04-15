program Core;
procedure p0() returns () {
  call p1();
};
procedure p1() returns () {
  call p2();
};
procedure p2() returns () {
};
procedure p3() returns () {
  call p1();
  call p4();
};
procedure p4() returns () {
};
