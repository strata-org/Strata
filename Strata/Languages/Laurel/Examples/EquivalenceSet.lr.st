/-
A set with this behavior commonly occurs in languages like Java. 
It relies on an equivalence relation that is user defined,
so given two objects that are observationally different, but equivalent according to the relation,
adding one to the set means it will also contain the other.
-/
composite EquivalenceSet<T> {

  val areEquivalent = function(first: T, second: T): boolean
    reads abstract

  val contains = function(value: T): (r: boolean)
    reads abstract

/-
Dafny complains about the quantifier over T, because these objects are not known to be allocated in the current heap.
Dafny's solution is to mark the parameter 'value' of the contains function as 'older', 
documentation here: https://dafny.org/dafny/DafnyRef/DafnyRef#sec-older-parameters

However, older is a complicated concept, so it would be great if we could avoid needing it.
Here is a discussion about a proposal to do that: https://github.com/dafny-lang/dafny/issues/6235
-/
  val containsEquivalent = function(value: T): (r: boolean)
    reads abstract
    ensures r == forall((other: T) -> areEquivalent(other, value) && this.contains(other))
}

composite ImmutableEquivalenceSet<T> extends EquivalenceSet<T> {

  val areEquivalent = function(first: T, second: T): boolean
    reads abstract

  val contains = function(value: T): (r: boolean) -- no reads clause means its empty

  val containsEquivalent = function(value: T): (r: boolean)
    reads flatMap((contained: T) -> areEquivalent.reads(value, contained))
    ensures inherited
}

composite MutableEquivalenceSet<T> extends EquivalenceSet<T> {
  val add = function(value: T): (r: boolean)
    modifies abstract
    ensures containsEquivalent(value)
}

composite EquivalenceSetByDynamicList<T> extends MutableEquivalenceSet<T> {
  val data = new DynamicList<T>();

  val contains = function(value: T): (r: boolean)
    reads data {
    -- Note the for loop in a function
    for(var index = 0; index < data.size; index++) {
      if (data.get(index) == value) {
        return true;
      }
    }  
    return false;
  }

  val containsEquivalent = function(value: T): (r: boolean)
    reads data
    reads flatMap((contained: T) -> areEquivalent.reads(value, contained))
    ensures inherited 
  {
    for(var index = 0; index < data.size; index++) {
      if (areEquivalent(value, data.get(index))) {
        return true;
      }
    }  
    return false;
  }

  val add = function(value: T): (r: boolean)
    modifies data
    ensures inherited
  {
    var alreadyContained = containsEquivalent(value);
    if (!alreadyContained) {
      data.add(value);
    }
    return alreadyContained;
  }
}