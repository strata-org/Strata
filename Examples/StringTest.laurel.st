procedure testString()
returns (result: string)
requires true
{
  var message: string := "Hello, World!";
  return message;
}

procedure testStringConcat()
returns (result: string)
requires true
{
  var hello: string := "Hello";
  var world: string := "World";
  return hello;
}
