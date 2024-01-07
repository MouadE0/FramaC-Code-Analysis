/*@ requires n > 0 && k >= 0 && k < n ;
  @ requires \valid(t+(k..n-1));
  @ ensures  (\forall integer i; k <= i < n ==> \result <= t[i])  &&
  @          (\exists integer i; k <= i < n && \result == t[i]);
  @ assigns \nothing;
*/

int getMinSubarray(int t[], int n, int k) {
  int res = t[k];
  /*@ loop invariant k+1 <= i <= n &&
    @   (\forall integer j; k <= j < i ==> res <= t[j]) &&
    @   (\exists integer j; k <= j < i && res == t[j]);
    @ loop assigns i, res;
    @ loop variant n - i;
    @*/
  for (int i = k + 1; i < n; i++)
    if (t[i] < res) res = t[i];
  return res;
}

void test1() {
  int tab[3] = {1, 0, 2};
  int min = getMinSubarray(tab, 3, 1);
  //@ assert min == 0;
}
void test2() {
  int tab2[5] = {5, 100, 3, 10, 1};
  int min = getMinSubarray(tab2, 5, 3);
  //@ assert min == 5;
}
void test3() {
  int tab2[3] = {5, 100, 3};
  int min = getMinSubarray(
      tab2, 0, 1);  // should provoke a failure: empty array not allowed
}
void test4() {
  int tab2[3] = {5, 100, 3};
  int min = getMinSubarray(
      tab2, 5, 1);  // should provoke a failure: not valid array of size 5
}
