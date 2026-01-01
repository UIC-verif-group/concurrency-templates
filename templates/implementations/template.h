#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include <stdint.h>
#include "threads.h"
#include "common.h"
#include "data_structure.h"

typedef struct css css;

//Template style
typedef struct pn {
    struct node *p;
    struct node *n;
} pn;

css *make_css();
node *get_root(css *t);

Status traverse(css *t, pn *pn, int x);

void insertOp_helper(css *c, node *p, int x, void *value);
void insert (css *t, int x, void *value);

void *lookupOp_helper(css *c, node *p, int x, Status status);
void *lookup (css *t, int x);

//support print
void printDS_helper (css *t);