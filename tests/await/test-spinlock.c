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
    while (x == 0);
    pthread_join(t, NULL);
}
