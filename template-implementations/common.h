#ifndef COMMON_H
#define COMMON_H
#define TABLE_SIZE 16384

typedef enum {
    FOUND,
    NOTFOUND,
    CONTINUE
} Status;

static void *surely_malloc (size_t n) {
    void *p = malloc(n);
    if (!p) exit(1);
    return p;
}

static int hash(void* p) {
    // Ensure the pointer is cast to a proper unsigned type before multiplication
    if (p == NULL) {
        return 0; // Reserved index for NULL
    }
    uintptr_t ptr_value = (uintptr_t)p;
    return (int)(ptr_value * 654435761ULL % TABLE_SIZE);
}

#endif