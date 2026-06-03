program CoreMatch;

// Nested non-recursive matches: outer on `m`, inner on `s`.

datatype Shape () { Circle(radius : int), Square(side : int), Triangle(base : int, height : int) };
datatype Mode  () { Area(), Perimeter() };

function compute(s : Shape, m : Mode) : int
{
  match m {
    arm Area() =>
      match s {
        arm Circle(radius : int)               => 3 * radius * radius;
        arm Square(side : int)                 => side * side;
        arm Triangle(base : int, height : int) => base * height;
      };
    arm Perimeter() =>
      match s {
        arm Circle(radius : int)               => 6 * radius;
        arm Square(side : int)                 => 4 * side;
        arm Triangle(base : int, height : int) => base + base + height;
      };
  }
};
