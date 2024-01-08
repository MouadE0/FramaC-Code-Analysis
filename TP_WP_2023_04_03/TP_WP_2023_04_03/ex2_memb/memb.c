/* Command to use for this file:


Without Coq and MetAcsl:
   frama-c-gui memb.c -wp -wp-rte -wp-prover=script,alt-ergo,cvc4

With MetAcsl:
   frama-c-gui memb.c -meta -meta-checks -meta-no-simpl -meta-number-assertions -then-last -wp -wp-rte  -wp-prover=script,alt-ergo,cvc4

With Coq (you may need to choose one of the provided versions of wp.script for your Coq version, to check it, type coqc -v):

   frama-c-gui memb.c -wp -wp-rte -wp-prover=script,alt-ergo,cvc4,native:coq -wp-coq-script wp.script

  -wp-prover   allows to select different (and multiple) provers
  -wp-timeout  sets the time allowed to the provers to finish the computation
  -wp-fct      selects the functions we want to prove with this run of WP

Note that if you do not have cvc4 (to check, type cvc4 --version), you may be unable 
to use cvc4 and script and keep only one prover: -wp-prover=alt-ergo 

You can also still try to use script with -wp-prover=script,alt-ergo
and choose one of the provided scripts in .frama-c/wp/script 
(after removing the suffix after .json)
*/

/*
 * Copyright (c) 2004, Swedish Institute of Computer Science.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the Institute nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file is part of the Contiki operating system.
 *
 * Author: Adam Dunkels <adam@sics.se>
 *
 */

/**
 * \addtogroup memb
 * @{
 */

 /**
 * \file
 * Memory block allocation routines.
 * \author Adam Dunkels <adam@sics.se>
 */
#include <string.h>

struct memb {
  unsigned short size;
  unsigned short num;
  char *count;
  void *mem;
};

#include "OccArray.acsl"

// TODO1: define a validity predicate for the memb datastructure
/*@
  predicate valid_memb(struct memb *m) =
    \true;
*/

/*@ // Converting from pointer to index and backwards.

  logic integer _memb_index(struct memb *m, void *ptr) =
    ((char*)ptr - (char*)m->mem) / m->size;

// TODO2: define a logic function that returns a pointer to the cell of a given index
  logic void *_memb_ptr(struct memb *m, integer index) = 
    NULL;

  lemma mult_simplification:
    \forall integer a, b;
    a >= 0 ==> b > 0 ==> (a * b) / b == a;

  lemma _memb_index_inverse:
    \forall struct memb *m, integer i;
    i >= 0 ==> m->size > 0 ==> _memb_index(m, _memb_ptr(m, i)) == i;
*/

/*@ // Helper predicates. For readability.

  predicate _memb_has(struct memb *m, void *ptr) =
    \exists integer i; 0 <= i < m->num && ptr == _memb_ptr(m, i);

  predicate _memb_allocated(struct memb *m, void *ptr) =
    _memb_has(m, ptr) && m->count[_memb_index(m, ptr)] != 0;
*/

/*@ // Counting free elements.

  logic integer _memb_numfree(struct memb *m) = occ_a(0, m->count, 0, m->num);

  predicate _memb_empty(struct memb *m) =
    \forall integer i; 0 <= i < m->num ==> m->count[i] == 0;

  predicate _memb_full(struct memb *m) =
    \forall integer i; 0 <= i < m->num ==> m->count[i] != 0;

  lemma _memb_empty_numfree:
    \forall struct memb *m; m->num >= 0 ==> _memb_empty(m) ==> _memb_numfree(m) == m->num;

  lemma _memb_empty_numfree_bis:
    \forall struct memb *m; _memb_numfree(m) == m->num ==> _memb_empty(m);

  lemma _memb_full_numfree:
    \forall struct memb *m; _memb_full(m) <==> _memb_numfree(m) == 0;
*/

/*@
  predicate lek(integer a, integer b, integer k) = a * k <= b * k;

  lemma le_lek:
    \forall integer a, b, k; (k > 0 && a <= b) ==> lek(a, b, k);
*/


/*@
  requires valid_memb(m);
  ensures valid_memb(m);
  ensures _memb_empty(m);
  assigns m->count[0 .. (m->num - 1)];
  assigns *((char*) m->mem + (0 .. (m->size * m->num - 1)));
*/
void
memb_init(struct memb *m)
{
  memset_char(m->count, 0, m->num);
  memset_char(m->mem, 0, m->size * m->num);
}
/*---------------------------------------------------------------------------*/
/*@
  requires valid_memb(m);
  ensures valid_memb(m);
  assigns m->count[0 .. (m->num - 1)];
  behavior free_found:
    assumes \exists integer i; 0 <= i < m->num && m->count[i] == 0;
    ensures \exists integer i;
      0 <= i < m->num &&
      \old(m->count[i]) == 0 &&
      m->count[i] == 1 &&
      \result == (char*) m->mem + (i * m->size) &&
      \forall integer j; (0 <= j < i || i < j < m->num) ==> m->count[j] == \old(m->count[j]);
    ensures \valid((char*) \result + (0 .. (m->size - 1)));
    ensures _memb_numfree(m) == \old(_memb_numfree(m)) - 1;
    ensures _memb_allocated(m, \result);
  behavior full:
    assumes _memb_full(m);
    ensures \forall integer i; 0 <= i < m->num ==> m->count[i] == \old(m->count[i]);
    ensures _memb_numfree(m) == \old(_memb_numfree(m));
    ensures \result == NULL;
  complete behaviors;
  disjoint behaviors;
*/
void *
memb_alloc(struct memb *m)
{
  int i;

  /*@
    loop invariant 0 <= i <= m->num;
    loop invariant \forall int j; 0 <= j < i ==> m->count[j] != 0;
    loop assigns i;
    loop variant m->num - i;
  */
  for(i = 0; i < m->num; ++i) {
    if(m->count[i] == 0) {
      /* If this block was unused, we increase the reference count to
	 indicate that it now is used and return a pointer to the
	 memory block. */
      ++(m->count[i]);

      /*@ assert lek(i, m->num - 1, m->size); */
      /*@ assert 0 <= i * m->size <= (m->num - 1) * m->size; */
      /*@ assert one_change{Pre, Here}(i, m->count, 0, m->num); */
      return (void *)((char *)m->mem + (i * m->size));
    }
  }

  /* No free block was found, so we return NULL to indicate failure to
     allocate block. */
  return NULL;
}
/*---------------------------------------------------------------------------*/
// TODO4: Specify the contract of the memb_free function
/*@
  requires valid_memb(m);
  ensures valid_memb(m);
  assigns m->count[_memb_index(m, ptr)];
  behavior alloc_found:
    assumes _memb_has(m, ptr) && _memb_allocated(m, ptr);
    ensures !_memb_allocated(m, ptr);
    ensures _memb_numfree(m) == \old(_memb_numfree(m)) + 1;
    ensures \result == 0;
//  behavior already_free:
// ...
//  behavior elem_notfound:
// ...
//  complete behaviors;
  disjoint behaviors;
*/
char
memb_free(struct memb *m, void *ptr)
{
  int i;
  char *ptr2;

  /* Walk through the list of blocks and try to find the block to
     which the pointer "ptr" points to. */
  ptr2 = (char *)m->mem;
  /*@
    loop invariant 0 <= i <= m->num;
    loop invariant valid_memb(m);
    loop invariant ptr2 == _memb_ptr(m, i);
    loop invariant i == _memb_index(m, _memb_ptr(m, i));
    loop invariant \forall int j; 0 <= j < i ==> (char*) ptr != (char*) m->mem + (j * m->size);
    loop assigns i, ptr2;
    loop variant m->num - i;
  */
  for(i = 0; i < m->num; ++i) {
    if(ptr2 == (char *)ptr) {
      /* We've found the block to which "ptr" points so we decrease the
	 reference count and return the new value of it. */
      m->count[i] = 0;
      /*@ assert _memb_allocated{Pre}(m, ptr) ==> one_change{Pre, Here}(i, m->count, 0, m->num); */
      return m->count[i];
    }
    ptr2 += m->size;
  }
  return -1;
}
/*---------------------------------------------------------------------------*/
/*@
  requires valid_memb(m);
  ensures \result <==> (m->mem <= ptr && (char*) ptr < (char*) m->mem + (m->num * m->size));
  assigns \nothing;
*/
int
memb_inmemb(struct memb *m, void *ptr)
{
  return (char *)ptr >= (char *)m->mem &&
    (char *)ptr < (char *)m->mem + (m->num * m->size);
}
/*---------------------------------------------------------------------------*/
// TODO5: Specify the contract of the memb_numfree function and prove it
/* @
  requires ...
  ensures ...
  assigns ...
*/
int
memb_numfree(struct memb *m)
{
  int i;
  int num_free = 0;

  /* @
    loop invariant ...
    loop assigns ...
    loop variant ...
  */
  for(i = 0; i < m->num; ++i) {
    if(m->count[i] == 0) {
      ++num_free;
    }
  }

  return num_free;
}
/** @} */
