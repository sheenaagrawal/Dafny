/*

   The method CalcTerm (m, n) computes 5*m-3*n using only arithmetic
   operations +5, -1, and -3.

   Fix the 'invariant' and 'decreases' annotations such that it verifies

*/
function method abs(m: int): nat
{ if m>0 then m else -m }

method CalcTerm(m: int, n: nat) returns (res: int)
  ensures res == 5*m-3*n;
{
  var m1: nat := abs(m);
  var n1: nat := n;
  res := 0;

  while (m1!=0)
    invariant 0 <= m1;
    invariant res == (abs(m)-m1)*5;
    decreases m1;
  {
    res := res+5;
    m1 := m1-1;
  }

  if (m<0) { res := -res; }
  var a := res;
  while (n1!=0)
    invariant 0 <= n1 <= n;
    invariant res == a - (n-n1)*3;
    decreases n1
  {
    res := res-3;
    n1 := n1-1;
  }
}
