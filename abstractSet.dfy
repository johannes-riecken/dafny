/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2017
   The University of Iowa
   
   Instructor: Cesare Tinelli
*/

class Set<T(==)> {
  // Abstract state, visible to clients
  ghost var Elems: set<T> ;

  // Concrete state, hidden from clients
  var s: seq<T> ;

  // Predicate defining the object invariant.
  predicate Valid()
    reads this;
  {
    && (forall x: T :: x in s <==> x in Elems)
    && (forall i:nat, j:nat :: i < j < |s| ==> s[i] != s[j])
  }

  // Constructor called when an instance of "IntegerElemset" is first
  // allocated. Note that this constructor is anonymous.
  constructor ()
	  modifies this;
    ensures Elems == {} ;
    ensures Valid() ;
  {
    s := [];

    Elems := {} ;
  }

  // Test if set contains the given element
  method contains(x: T) returns (b: bool)
    requires Valid() ;
    ensures Valid() ;
    ensures b <==> x in Elems ;
  {
    b := (x in s);
  }

  // Public method for adding an element to the set.
  // The underlying array is grown if necessary.
  method add(x: T)
    requires Valid() ;
    modifies this ;
    ensures Valid() ;
    ensures Elems == old(Elems) + { x } ;
  {
    if (x !in s)
    {
      s := [x] + s;
    }
    
    Elems := Elems + { x } ;
  }
}

method Main()
{
  var s1 := new Set() ;


  s1.add(3) ;

  var b := s1.contains(3) ;
  assert b == true ;

  s1.add(3) ;
  assert s1.Elems == {3};

}
