#include <pthread.h>
#include <stdlib.h>
#include <assert.h>
#include <stdatomic.h>
#include <stdint.h>

#define N 8
#define T 4

atomic_int data[N];
atomic_uint_least8_t generation[N] = { 0 };

static void await(unsigned ix, uint_least8_t gen) {
  while (generation[ix] != gen);
}

static void sort_pair(unsigned a, unsigned b, uint8_t gena, uint8_t genb) {
  await(a, gena);
  await(b, genb);
  int da = data[a];
  int db = data[b];
  if (da > db) {
    data[a] = db;
    data[b] = da;
  }
  generation[a] = gena+1;
  generation[b] = genb+1;
}

static void *t1(void *arg) {
  sort_pair(0, 1, 0, 0);
  sort_pair(0, 2, 1, 1);
  /* *whistle* */
  sort_pair(0, 4, 2, 2);
  sort_pair(2, 4, 4, 3);
  sort_pair(1, 2, 4, 5);
  return NULL;
}

static void *t2(void *arg) {
  sort_pair(2, 3, 0, 0);
  sort_pair(1, 3, 1, 1);
  sort_pair(1, 2, 2, 2);
  sort_pair(1, 5, 3, 3);
  /* *whistle* */
  sort_pair(3, 4, 4, 4);
  return NULL;
}

static void *t3(void *arg) {
  sort_pair(4, 5, 0, 0);
  sort_pair(4, 6, 1, 1);
  sort_pair(5, 6, 2, 2);
  sort_pair(2, 6, 3, 3);
  /* *whistle* */
  sort_pair(5, 6, 5, 4);
  return NULL;
}

static void *t4(void *arg) {
  sort_pair(6, 7, 0, 0);
  sort_pair(5, 7, 1, 1);
  /* *whistle* */
  sort_pair(3, 7, 2, 2);
  sort_pair(3, 5, 3, 4);
  /* *whistle* */
  return NULL;
}

int main() {
  /* Chosen by fair dice roll, guaranteed to be random. */
  srand(2314626165);
  for (int i = 0; i < N; ++i) data[i] = rand();

  pthread_t tids[T];
  static void *(* const f[T])(void*) = {t1, t2, t3, t4};
  for (int i = 0; i < T; ++i) pthread_create(tids+i,NULL,f[i],NULL);
  for (int i = 0; i < T; ++i) pthread_join(tids[i],NULL);

  for (int i = 0; i < N-1; ++i)
    assert(data[i] <= data[i+1]);
  return 0;
}
