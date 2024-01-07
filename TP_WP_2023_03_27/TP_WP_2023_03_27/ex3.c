/*@ requires *p <= 100 && *p >= -100;
    ensures \result == \old(*p)+ 1 ;  */

int incr(int *p)
{
  *p = *p + 1;
  return *p;
};
