/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2017
   The University of Iowa
   
   Instructor: Cesare Tinelli

   Credits: Example adapted from Dafny tutorial
*/


method Abs(x: int) returns (y: int)
  ensures x < 0  ==> y == -x;
  ensures x >= 0 ==> y ==  x; 
{
  if (x < 0) 
    { y := -x; }
  else
    { y := x; }
}

method m(x:int) returns (abs:int)
  ensures abs >= x;
{
  abs := Abs(x);
}

method Test1(x: int)
{
  var v := Abs(x);
  assert 0 <= v;

  var v1 := Abs(3);
  assert v1 == 3;

  var v2 := Abs(3);
  assert v2 == 3;

}

function abs(x: int): int
{
  if x < 0 then -x else x
}

method Test2(x: int)
{
  var v := Abs(x);
  assert v == abs(x);
}
