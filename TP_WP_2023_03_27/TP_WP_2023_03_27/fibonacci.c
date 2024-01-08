
/*@ logic integer fib(integer n) = (n <= 1) ? n : fib(n-1) + fib(n-2); */

/*@ requires 0 <= n <= 20;
  @ assigns \nothing;
  @ ensures \result = fib(n);
  @*/
int fibo(int n)
{
  if (n <= 1)
    return n;
  else
    return fibo(n - 1) + fibo(n - 2);
}

/*@ requires 0 <= n <= 20;
  @ assigns \nothing;
  @ ensures \result = fib(n);
  @*/
int fibo2(int n)
{
  int prev1 = 0, prev2 = 1, i;
  /*@
    loop assigns i, prev1, prev2;
    loop invariant 0 <= i <= n;
    loop invariant prev1 == fib(i) && prev2 == fib(i+1);
    loop variant n - i;
   */
  for (i = 0; i < n; i++)
  {
    int savePrev1 = prev1;
    prev1 = prev2;
    prev2 = savePrev1 + prev2;
  }
  return prev1;
}
