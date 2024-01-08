void loop1(int n)
{
  /*@ loop variant n; */
  while (n > 0)
    n--;
}

void loop2(int n)
{
  /*@ loop variant 100-n; */
  while (n < 100)
    n = n + 1;
}
