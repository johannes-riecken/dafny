/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2017
   The University of Iowa
   
   Instructor: Cesare Tinelli
*/

// Parametric linked lists

// Traditional (acyclic) linked list implementation with a node containing 
// the list element and a reference to the rest of the list.
// Empty lists are represented simply by null. 
// Hence non-null values of type Node<T> represent non-empty lists.

class Node<T> {
  // abstract variable storing (in the same order) the list of elements 
  // in the sequence headed by 'this'
  ghost var list: seq<T>;

  // Heap frame, 
  // Consists of the set of nodes in the list headed by 'this'
  ghost var nodes: set<Node<T>>;

  // element stored in the node
  var elem: T;
  // next node in the list, if any
  var next: Node<T>;

  // The invariant predicate provides a definition of 'list' and 'nodes'
  // by induction of the length of the list
  predicate Valid()
    decreases nodes;
    reads this, nodes;
  {
     // this in nodes &&      
     null !in nodes
     && (next == null ==> nodes == {this} 
                          && list == [elem]
        )
     && (next != null ==> next in nodes 
                          && nodes == {this} + next.nodes
                          && this !in next.nodes // acyclity condition
                          && list == [elem] + next.list
                          && next.Valid()
        )
  }
  
  // Makes 'this' the head of a sigleton list containg element 'e'
  constructor (e: T)
    modifies this;
    ensures Valid();
    ensures list == [e];
  {
    elem := e;
    next := null;

    list := [e];
    nodes := {this};
  }

  // Makes 'this' the head of a non-sigleton list containg element 'e' 
  // and continuing with the list headed by 'n'
  constructor insert(e: T, n: Node<T>)
    modifies this;
    requires n != null;
    requires n.Valid();
    requires this !in n.nodes; 
    ensures Valid();
    ensures list == [e] + n.list;
    ensures nodes == {this} + n.nodes;
  {
    elem := e;
    next := n;

    list := [e] + n.list;
    nodes := {this} + n.nodes;
  }

  // Returns the (possibly empty) tail of the list headed by 'this'
  method tail() returns (t: Node<T>)
    requires Valid();
    ensures Valid();
    ensures t != null ==> t.Valid()
                          && t.nodes == nodes - {this}
                          && t.list == list[1..];
  {
    t := next;
  }

  // Returns the element stored in the head of the list
  method head() returns (e: T)
    requires Valid();
    ensures Valid();
    ensures e == list[0];
  {
    e := elem;
  }
}

method main() 
{
  var l1 := new Node(3);
  var l2 := new Node.insert(4, l1);
  var l3 := new Node.insert(5, l2);
  assert l1.list == [3];
  assert l2.list == [4,3];
  assert l3.list == [5,4,3];
}
