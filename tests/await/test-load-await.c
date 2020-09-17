#include <stdio.h>
#include <pthread.h>
#include <stdatomic.h>

atomic_int x;
extern int __VERIFIER_xchg_await_aint(atomic_int *var, int new_value,
				      int condition, int cond_arg);
extern int __VERIFIER_load_await_aint(atomic_int *var, int condition,
				      int cond_arg);
#define AWAIT_COND_LE 6
#define AWAIT_COND_EQ 2

static void *thread(void *arg) {
    x = 1;
    return NULL;
}

int main() {
    pthread_t t;
    pthread_create(&t, NULL, thread, NULL);

    int ret = __VERIFIER_load_await_aint(&x, AWAIT_COND_EQ, 1);
    printf("main: load_await(x, = 1) = %d\n", ret);

    pthread_join(t, NULL);
}
