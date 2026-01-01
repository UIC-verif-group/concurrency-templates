#include "data_structure.h"
#include "template.h"

typedef struct md_entry { lock_t lock; int min; int max; } md_entry;
typedef struct css { node *root; md_entry *metadata[16384]; } css;

int inRange(md_entry *m, int x);
md_entry *lookup_md(css *c, node *p);
Status traverse(css *c, pn *pn, int x);

//void insertOp_giveup(css* c, node *p, int x, void* value, Status status);
void insertOp_helper(css *c, node *p, int x, void *value);
void *lookupOp_helper(css *c, node *p, int x, Status status);

//support print ds
void printDS_helper (css *t);
