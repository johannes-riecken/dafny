/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2017
   The University of Iowa
   
   Instructor: Cesare Tinelli
*/

// Bank account example
// showcasing the idea of (heap) frames

class Trans {
  var total: int;

  constructor ()
	  modifies this;
    ensures total == 0;
  {
    total := 0;
  }

  method add(n: nat)
    modifies this;
    ensures total == old(total) + n;
  {
    total := total + n;
  }
}


class Account
{
  // public variables
  ghost var Balance: int;           // the current balance of the account
  ghost var Frame: set<object>; // set of all objects (in the heap)
                                //   that methods can read or modify

  // private variables
  var deposits: Trans;   // stores the total amount of deposits
  var withdrawls: Trans; // stores the total amount of withdrawls

  function Valid(): bool
    reads this, Frame;
  {
    // concrete state invariants
    null !in {deposits, withdrawls} 
    && deposits != withdrawls 
    
    // Frame invariants
    && Frame == {this, deposits, withdrawls}  
	  
    // connection between abstract and concrete state
    && Balance == deposits.total - withdrawls.total
  }

  constructor ()
	  modifies this;
    ensures Valid();
    ensures Balance == 0;
  {
    deposits := new Trans();
    withdrawls := new Trans();
    
    Balance := 0;

    // establishes the initial frame
    Frame := {this, deposits, withdrawls};
  }

  method GetBalanceance() returns (b: int)
    requires Valid();
    ensures Valid();
    ensures b == Balance;
  {
    b := deposits.total - withdrawls.total;
  }

  method Deposit(a: nat)
    modifies Frame;
    requires Valid();
    ensures Valid();
    ensures Balance == old(Balance) + a;
  {
    deposits.add(a);
    
    Balance := Balance + a;
  }

  method Withdraw(a: nat)
    modifies Frame;
    requires Valid();
    ensures Valid();
    ensures Balance == old(Balance) - a;
  {
    withdrawls.add(a);
    
    Balance := Balance - a;
  }
}

