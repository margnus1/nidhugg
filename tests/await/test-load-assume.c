#include <stdio.h>
#include <pthread.h>
#include <stdatomic.h>

atomic_uint x;
extern void __VERIFIER_assume(int cond);

static void *thread(void *arg) {
    x = 1;
    return NULL;
}

int main() {
    pthread_t t;
    pthread_create(&t, NULL, thread, NULL);

    int ret;
    __VERIFIER_assume((ret = x) == 1);;
    printf("main: load_await(x, = 1) = %d\n", ret);

    pthread_join(t, NULL);
}
