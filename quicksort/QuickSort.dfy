include "part.dfy"


method qsort(a:array<int>, l:nat, u:nat)
  modifies a;
  
  requires a.Length > 0;
  requires 0 <= l <= u < a.Length;
  requires 0 <= l <= u < a.Length - 1 ==> partitioned(a, l, u, u+1, a.Length-1);
  requires 0 < l <= u <= a.Length - 1 ==> partitioned(a, 0, l-1, l, u);
  

  ensures sorted_between(a, l, u+1);
  ensures l > 0 ==> beq(old(a[..]), a[..], 0, l-1);
  ensures 0 < l <= u <= a.Length - 1 ==> partitioned(a, 0, l-1, l, u);
  ensures 0 <= l <= u < a.Length - 1 ==> beq(old(a[..]), a[..], u+1, a.Length - 1);
  ensures 0 <= l <= u < a.Length - 1 ==> partitioned(a, l, u, u+1, a.Length-1);
  
  
  decreases u - l;

{
  
  if u > l
  {
    var pv := partition(a,l,u);
    if pv == l 
    {
      qsort(a,pv+1,u);
    }
    else
    {
      qsort(a,l,pv-1);
      if pv != u
      {
        qsort(a,pv+1,u);
      }
    }
  }
}