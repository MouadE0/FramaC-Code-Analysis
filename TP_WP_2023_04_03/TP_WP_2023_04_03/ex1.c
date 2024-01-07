int A, B, C; 

// Command: 
// frama-c-gui myfile.c -meta -meta-checks -meta-no-simpl -meta-number-assertions  -then-last -wp -wp-rte

// Exercice. Specification and proof of metaproperties (HILAREs).

// a) Specify a strong invariant stating that A==B is always true. Try to prove it. 
// b) Specify a weak invariant stating that A==B is always true. Try to prove it. 
// c) Specify that A is never read. Try to prove it. 
// d) Specify that A is never written unless C>=0 . Try to prove it. 

/*@ 
  requires A==B;
  assigns A,B; 
  ensures C>=0 && A==C && B==C ||
    C<0 && A==\old(A) && B==\old(B); */ 
void foo(){
  if ( C >= 0 ){
    A = C;
    B = C;
  }
} 

/*@ 
  requires A==B;
  assigns \nothing; 
  ensures \result == B; */  
int get_B(){
  return B;
}

/*@ 
  requires A==B;
  assigns \nothing; 
  ensures \result == C; */  
int get_C(){
  return C;
}

/*@ 
  requires A==B;
  assigns C; 
  ensures C == B; */  
void BtoC(){
  C=B;
}
