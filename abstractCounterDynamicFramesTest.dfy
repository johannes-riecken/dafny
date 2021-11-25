/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2017
   The University of Iowa
   
   Instructor: Cesare Tinelli

*/

class Cell {
  var data: int;

  constructor (n: int)
	  modifies this;
    ensures data == n;
  {
    data := n ;
  }
}

class Counter
{
  // public variable
  ghost var Val: int;

  // private variables
  var incs: Cell;
  var decs: Cell;

  function Valid(): bool
    reads this, incs, decs;
  {
    incs != decs &&
    incs != null &&
    decs != null &&
    Val == incs.data - decs.data
  }

  constructor ()
    ensures Valid();
    ensures Val == 0;
  {
    incs := new Cell(0);
    decs := new Cell(0);

    Val := 0;
  }

  method GetVal() returns (x: int)
    requires Valid();
    ensures x == Val;
  {
    x := incs.data - decs.data;
  }

  method Inc()
    requires Valid();
    ensures Valid();
    ensures Val == old(Val) + 1;
  {
    incs.data := incs.data + 1;

    Val := Val + 1;
  }

  method Dec()
    requires Valid();
    ensures Valid();
    ensures Val == old(Val) - 1;
  {
    decs.data := decs.data + 1;
    Val := Val - 1;
  }
}

method Main()
{
  var c := new Counter();  assert c.Val == 0;
  c.Inc();                 assert c.Val == 1;
  c.Inc();                 assert c.Val == 2;
  c.Dec();                 assert c.Val == 1;
  c.Inc();                 assert c.Val == 2;
}
