function select(map: int, key: int): intexternal;

function update(map: int, key: int, value: int): intexternal;

function const(value: int): intexternal;

procedure imperativeProc(x: int)
  returns (r: int)
  opaque
  ensures r == x + 1
{ r := x + 1; r };

procedure imperativeCallInExpressionPosition()
  opaque
{ var x: int := 0; var y: int := imperativeProc(x) + x; assert y == 1; assert x == 0 };
