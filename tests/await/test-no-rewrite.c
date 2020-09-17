#include <stdio.h>
#include <pthread.h>
#include <stdatomic.h>

atomic_uint x, y;
extern void __VERIFIER_assume(int cond);

static void *thread(void *arg) {
    x = 1;
    y = 2;
    return NULL;
}

int main() {
    pthread_t t;
    pthread_create(&t, NULL, thread, NULL);

    /* Could the rewrite hoist the store above the load?*/
    int ret = x;
    y = 2;
    __VERIFIER_assume(ret == 1);
    printf("main: load_await(x, = 1) = %d\n", ret);

    pthread_join(t, NULL);
}
