// In some versions of Frama-C, an additional option -pp-annot should be used to parse this example

#include <limits.h>

/*@
  requires INT_MIN <= *a + *b <= INT_MAX;
  requires \valid(a) && \valid(b);
  assigns  *a;
  ensures  *a == \old(*a)+ *b;
  ensures  *b == \old(*b);
*/
void incr_a_by_b(int* a, int const* b){
  *a += *b;
}
