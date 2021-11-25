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
  ghost var R: set<object>;

  // private variables
  var incs: Cell;
  var decs: Cell;

  function Valid(): bool
    reads this, R;
  {
    R == {this, incs, decs}
    && null !in R
    && incs != decs
    && Val == incs.data - decs.data
  }

  constructor ()
    modifies this;
    ensures Valid();
    ensures fresh(R - {this});
    ensures Val == 0;
  {
    incs := new Cell(0);
    decs := new Cell(0);

    Val := 0;
    
    R := { this, incs, decs };
  }

  method GetVal() returns (x: int)
    requires Valid();
    ensures x == Val;
  {
    x := incs.data - decs.data;
  }

  method Inc()
    requires Valid();
    modifies R;
    ensures Valid();
    ensures R == old(R);
    ensures Val == old(Val) + 1;
  {
    incs.data := incs.data + 1;

    Val := Val + 1;
  }

  method Dec()
    requires Valid();
    modifies R;
    ensures Valid();
    ensures R == old(R);
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
