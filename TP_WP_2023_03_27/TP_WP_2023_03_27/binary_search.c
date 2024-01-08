/*@ lemma div_by_2_def: \forall integer n; 0 <= n ==> 0 <= n - 2 * (n / 2) <= 1;
 */
// le lemme peut rester non prouve

// Predicat pour voir si query est entre 2 bornes
/*@
  predicate contains(int *arr, integer x, integer y, int query) =
    \exists integer i; x <= i <= y && arr[i] == query;
 */

#include <limits.h>

/*@ requires 0<=length<INT_MAX && \valid(arr+(0..length-1)) &&
   (\forall int i, j; 0 <= i < j <= length-1 ==> arr[i] <= arr[j]);
    assigns  \nothing;
    ensures -1 <= \result < length &&
      (\result >= 0 ==> arr[\result] == query) &&
      (\result == -1 ==>  !contains(arr, 0, length-1, query)) ;
*/
int binary_search(int *arr, int length, int query)
{
  int low = 0;
  int high = length - 1;
  /*@
    @ loop assigns low, high;
    @ loop invariant (low == high+1) ||
        (low <= high && 0 <= low <= length-1 && 0 <= high <= length-1);
    @ loop invariant !contains(arr, 0, low-1, query) &&
        !contains(arr, high+1, length-1, query);
    @ loop invariant
        contains(arr, 0, length-1, query) ==> contains(arr, low, high, query);
    @loop variant high-low+1;
  */
  while (low <= high)
  {
    // int mean = low + (high - low) / 2;
    int mean = (high + low) / 2; // Version avec erreur !!!
    //@ assert low <= mean <= high;
    if (arr[mean] == query)
      return mean;
    if (arr[mean] < query)
      //@assert !contains(arr, low, mean, query);
      low = mean + 1;
    else
      //@assert !contains(arr, mean, high, query);
      high = mean - 1;
  }
  return -1;
}

void test1()
{
  int tab[3] = {1, 0, 2};
  int res = binary_search(tab, 3, 1);
  //@ assert res == 0;
}
void test2()
{
  int tab[3] = {1, 0, 2};
  int res = binary_search(tab, 3, 4);
  //@ assert res == -1;
}
void test3()
{
  int tab[3] = {1, 0, 2};
  int res = binary_search(tab, 0, 1);
  // should provoke a failure: empty array not allowed
}

void test4()
{
  int tab[3] = {1, 0, 2};
  int res = binary_search(tab, 5, 1);
  // should provoke a failure: not valid array of size 5
}
