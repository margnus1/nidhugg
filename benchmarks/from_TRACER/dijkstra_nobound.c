/* Copyright (C) 2018
 * This benchmark is part of SWSC
 */

/* Adapted from: 
 * Dijkstra's critical section algorithm, implemented with fences.
 *
 * URL:
 *   https://www.eecs.yorku.ca/course_archive/2007-08/W/6117/DijMutexNotes.pdf
 */

#include <assert.h>
#include <stdint.h>
#include <stdatomic.h>
#include <pthread.h>

#define N 2

// shared variables
atomic_int interested[N];
atomic_int passed[N];
atomic_int k;

atomic_int x;

void *t(void *arg)
{
  int done, _k;
  int tid = *((int *)arg);
  	
  atomic_store_explicit(&interested[tid], 1, memory_order_seq_cst);

  done = 0;
  for (;;) {
    for (;;) {
      _k = atomic_load_explicit(&k, memory_order_seq_cst); 
      if (_k==tid) {
	break;
      }
      if (atomic_load_explicit(&interested[_k], memory_order_seq_cst)==0)
	atomic_store_explicit(&k, tid, memory_order_seq_cst); 	  
    }
	  
    atomic_store_explicit(&passed[tid], 1, memory_order_seq_cst);

    done = 1;
    for (int j=0; j<N; j++) {
      if (j==tid) continue;
      if (atomic_load_explicit(&passed[j], memory_order_seq_cst)==1) {
	atomic_store_explicit(&passed[tid], 0, memory_order_seq_cst);
	done = 0;
      }
    }

    if (done==1) {
      break;
    }
  }

  // critical section
  atomic_store_explicit(&x, tid, memory_order_seq_cst);
  assert(atomic_load_explicit(&x, memory_order_seq_cst) == tid);
  
  atomic_store_explicit(&passed[tid], 0, memory_order_seq_cst);
  atomic_store_explicit(&interested[tid], 0, memory_order_seq_cst);
  return NULL;
}

int arg[N];

int main(int argc, char **argv)
{
  pthread_t ts[N];
  	
  for (int i=0; i<N; i++) {
    atomic_init(&interested[i], 0);
    atomic_init(&passed[i], 0);	
  }
  atomic_init(&k, 0);
  atomic_init(&x, 0);
	  
  for (int i=0; i<N; i++) {
    arg[i] = i;
    pthread_create(&ts[i], NULL, t, &arg[i]);
  }
  
  for (int i=0; i<N; i++) {
    pthread_join(ts[i], NULL);
  }
  
  return 0;
}
