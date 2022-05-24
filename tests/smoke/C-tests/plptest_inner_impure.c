// nidhuggc: -unroll=2 -sc -optimal
#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <assert.h>

atomic_int x;
atomic_int y;

static void *test(void *arg) {
  while(true) {
    bool did_y = false;
    int a;
    while(true) {
      a = x;
      if (a) break;
      if (!did_y) { y++; did_y = true; }
      if (did_y) break;
    }
    if (a) break;
  }

  return arg;
}

int main() {
  pthread_t t;
  pthread_create(&t, NULL, test, NULL);
  x = 1;
  assert(y < 2);
}
