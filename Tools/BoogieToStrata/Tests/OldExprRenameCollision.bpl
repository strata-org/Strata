// Regression test: old() expression with a renamed (colliding) variable.
//
// The global variable `main` collides with procedure `main` after
// sanitization (cross-namespace collision). The variable must be
// renamed when emitted. An old() expression referencing that variable
// must use the *renamed* name, not the raw sanitized name.
// If the code silently falls back to Name() instead of NameOf(), the
// old() expression will reference the wrong (procedure) name.

var main: int;

procedure main()
  modifies main;
  ensures main == old(main) + 1;
{
  main := main + 1;
}
