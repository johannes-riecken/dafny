/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2017
   The University of Iowa
   
   Instructor: Cesare Tinelli
*/

// Parametric FIFO queue

class Queue<T> {

  ghost var Contents: seq<T>;

  // container for the queue's elements
  var a: array<T>;
  // size of the queue
  var n: nat;

  predicate Valid()
  reads this, a;
  {
    // concrete state invariants
    a != null &&
    n <= a.Length && 
    0 < a.Length &&

    // connection between abstract and concrete state
    Contents == a[0..n]
  }

  constructor ()
    modifies this;
    ensures Valid();
    ensures fresh(a);
    ensures Contents == [];
  {
    a := new T[5];
    n := 0;

    Contents := [];
  }

  method front() returns (e: T)
    modifies this;
    requires Valid();
    requires Contents != [];
    ensures Valid();
    ensures a == old(a);
    ensures Contents == old(Contents);
    ensures e == Contents[0];
  {
    e := a[0]; 
  }
 
  method enqueue(e: T)
    modifies this, a;
    requires Valid();
    ensures Valid();
    ensures old(n) < old(a.Length) ==> a == old(a);
    ensures old(n) == old(a.Length) ==> fresh(a);
    ensures Contents == old(Contents) + [e];
  {
    if (n == a.Length) {
      var b := new T[2 * a.Length];
      // older versions of Dafny used the keyword "parallel" instead of "forall"
      forall i | 0 <= i < n {
        b[i] := a[i];
      }
      a := b;
    }
    a[n] := e;
    n := n + 1;

    Contents := a[0..n];
  }

  method dequeue() returns (e: T)
    modifies this, a;
    requires Contents != [];
    requires Valid();
    ensures Valid();
    ensures a == old(a);
    ensures [e] + Contents == old(Contents);
  {
    e := a[0];
    n := n - 1;
      // older versions of Dafny used the keyword "parallel" instead of "forall"
    forall i | 0 <= i < n {
      a[i] := a[i + 1];
    }

   Contents := a[0..n];
  }
}
method test ()
{
  var q := new Queue<int>();  assert q.Contents == [];
  
  q.enqueue(1); assert q.Contents == [1];
  
  q.enqueue(2);
  q.enqueue(3);
  q.enqueue(2);
  q.enqueue(4); assert q.Contents == [1,2,3,2,4];

  var f := q.front();
  assert f == 1 && q.Contents == [1,2,3,2,4];
 
  f := q.dequeue();
  assert f == 1 && q.Contents == [2,3,2,4];

  q.enqueue(5); assert q.Contents == [2,3,2,4,5];
}
