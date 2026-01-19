#include "data_structure.h"
#include "template.h"

typedef struct css { node *root; lock_t lock; } css;

Status traverse(css *c, pn *pn, int x);

//void insertOp_lock(css* c, node *p, int x, void* value, Status status);
void insertOp_helper(css *c, node *p, int x, void *value);
void *lookupOp_helper(css *c, node *p, int x, Status status);

//support print ds
void printDS_helper (css *t);