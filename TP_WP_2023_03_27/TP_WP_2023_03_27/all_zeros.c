/*@ requires n > 0 ;
  @ requires \valid(t+(0..n-1));
  @ ensures \result <==> (\forall integer i; 0 <= i < n ==> t[i] == 0);
  @ assigns \nothing;
*/

int all_zeros(int t[], int n)
{
  int k;
  /*@ loop invariant  0 <= k < n &&
    @ (\forall integer j; 0 <= j < k ==> t[j] == 0);
    @ loop assigns k ;
    @ loop variant n - k ;
  */
  for (k = 0; k < n; k++)
    if (t[k] != 0)
      return 0;
  return 1;
}

// The following function allows to test the specification: correctness and
// completeness. (It cannot guarantee though that the specification is indeed
// correct and complete.)

void test1()
{
  int tab[3] = {0, 0, 0};
  int res = all_zeros(tab, 3);
  //@ assert res == 1;
}
void test2()
{
  int tab[3] = {0, 1, 0};
  int res = all_zeros(tab, 3);
  //@ assert res == 0;
}
void test3()
{
  int tab[3] = {0, 0, 0};
  int res =
      all_zeros(tab, 0); // should provoke a failure: not valid array of size 3
}
