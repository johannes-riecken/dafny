/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2017
   The University of Iowa
   
   Instructor: Cesare Tinelli
*/

class IntSet {
  // Abstract state, visible to clients
  ghost var Elems: set<int>;

  // Concrete state, hidden from clients
  var s: seq<int>;

  predicate sorted(s: seq<int>)
  {
    forall i:nat, j:nat :: i < j < |s| ==> s[i] < s[j]
  }

  // Predicate defining the object invariant.
  predicate Valid()
    reads this;
  {
    && (forall x: int :: x in s <==> x in Elems)
    && sorted(s)
  }

  // Constructor called when an instance of "IntegerElemset" is first
  // allocated. Note that this constructor is anonymous.
  constructor ()
	  modifies this;
    ensures Elems == {};
    ensures Valid();
  {
    s := [];

    Elems := {};
  }

  // Test if set contains the given element
  // does binary search over s
  method contains(x: int) returns (b: bool)
    requires Valid();
    ensures Valid();
    ensures b <==> x in Elems;
  {
    var lo: nat := 0;
	  var hi: nat := |s|;
	  while (lo < hi)
      decreases hi - lo;
      invariant lo <= hi <= |s|;
		  invariant forall i:nat :: i < lo || hi <= i < |s|	==> s[i] != x;
	  {
	  	var mid: nat := (lo + hi) / 2;
	  	if (s[mid] < x) {
		  	lo := mid + 1;
		  } else if (s[mid] > x) {
		  	hi := mid;
		  } else {
			  return true;
		  }
  	}
	  return false;
  }   
  function method insert(x: int, a: seq<int>): seq<int>
    decreases a;
    requires sorted(a);
    ensures sorted(insert(x, a));
    ensures forall y :: y in a ==> y in insert(x, a);
    ensures forall y :: y in insert(x, a) ==> (y == x || y in a);
    ensures (set y | y in a) + {x} == (set y | y in insert(x,  a));
  {
    if a == [] then [x]
    else if x < a[0] then [x] + a
    else if x == a[0] then a
    else a[0..1] + insert(x, a[1..])
  }

  // Public method for adding an element x to the set.
  // x is inserted in s so as to maintain s sorted.
  method add(x: int)
    modifies this;
    requires Valid();
    ensures Valid();
    ensures Elems == old(Elems) + { x };
  {
    s := insert(x, s);
    
    Elems := Elems + { x };
  }
}


method Main()
{
  var s1 := new IntSet();
  s1.add(3);

  var b := s1.contains(3);
  assert b == true;

  s1.add(3);
  assert s1.Elems == {3};
}
