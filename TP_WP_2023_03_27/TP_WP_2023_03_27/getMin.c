/*@ requires n > 0;
  @ requires \valid(t+(0..n-1));
  @ ensures  (\forall integer i; 0 <= i < n ==> \result <= t[i]) &&
  @   (\exists integer i; 0 <= i < n && \result == t[i]); 
  @ assigns \nothing;
*/

int getMin(int t[], int n) { 
  int res = t[0]; 
  /*@ loop invariant 1 <= i <= n &&
    @   (\forall integer j; 0 <= j < i ==> res <= t[j]) &&
    @   (\exists integer j; 0 <= j < i && res == t[j]); 
    @ loop assigns i, res;
    @ loop variant n - i;
    @*/
  for (int i = 1; i < n; i++) 
  {
    if (t[i] < res) 
      res = t[i];
  }
  return res;
}

// The following function allows to test the specification: correctness and completeness.
// (It cannot guarantee though that the specification is indeed correct and complete.)

void test1(){
  int tab[3]={1,0,2};
  int min=getMin(tab,3);
  //@ assert min == 0; 
}
void test2(){
  int tab2[3]={5,100,3};
  int min=getMin(tab2,2);
  //@ assert min == 5; 
}
void test3(){
  int tab2[3]={5,100,3};
  int min=getMin(tab2,0); // should provoke a failure: empty array not allowed
}
void test4(){
  int tab2[3]={5,100,3};
  int min=getMin(tab2,5); // should provoke a failure: not valid array of size 5
}


