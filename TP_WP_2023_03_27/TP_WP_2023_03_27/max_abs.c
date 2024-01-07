int abs ( int x );
int max ( int x, int y );

// returns maximum of absolute values of x and y
int max_abs( int x, int y ) {
  x=abs(x); 
  y=abs(y);
  return max(x,y);
}
