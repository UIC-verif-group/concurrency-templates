#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include "threads.h"
#include "template.h"

void insert (css *t, int x, void *value) {
    struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
    pn->p = NULL;
    pn->n = get_root(t);
    
    Status status = traverse(t, pn, x);
    insertOp_helper(t, pn->p, x, value);
    free(pn);
}

void *lookup (css *t, int x) {
    struct pn *pn = (struct pn *) surely_malloc (sizeof *pn);
    void *v;
    pn->p = NULL;
    pn->n = get_root(t);

    Status status = traverse(t, pn, x);
    v = lookupOp_helper(t, pn->p, x, status);
    free(pn);
    return v;
}