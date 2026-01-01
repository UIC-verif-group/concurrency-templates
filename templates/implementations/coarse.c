#include "coarse.h"

//FOUND = 0, NOTFOUND = 1, CONTINUE = 2
Status traverse(css *c, pn *pn, int x) {
    Status status = CONTINUE;
    acquire(c->lock);  // acquire coarse-grained lock    
    if(!pn->n){
        node *r = c->root;
        if (hash(r) == hash(pn->n)){
            return CONTINUE;
        }
        else{
            pn->n = r;
        } 
    }

    for( ; ; ){
        pn->p = pn->n;
        status = findNext(pn->p, (node**)&pn->n, x);
        if (status == FOUND){
            break;
        }
        else if (status == NOTFOUND){
            break;
        }
        else{}
    }
    return status;
}

void insertOp_helper(css *c, node *p, int x, void *value){
    node *new_node = insertOp(p, x, value);
    if (!new_node){
        release(c->lock);  
        return;
    }
    
    // Handle case where status is CONTINUE (p == NULL)
    if (p == NULL) {
        c->root = new_node;
        release(c->lock);
        return;
    }
    release(c->lock);
}

void *lookupOp_helper(css *c, node *p, int x, Status status){
    void *v;
    if (status == FOUND){
        v = get_value(p);
    }
    else{
        v = NULL;
    }
    release(c->lock);
    return v;
}

css *make_css(){
    css *new_css = (css*) surely_malloc(sizeof(css));

    lock_t lock = makelock();
    new_css->root = NULL;
    new_css->lock = lock;
    release(lock);

    return new_css;
}

node *get_root(css* t){
    acquire(t->lock);
    node *r = t->root;
    release(t->lock);
    return r;
}

//Print
void printDS_helper (css *t){
    printf ("COARSE-GRAINED LOCKING Template - ");
    struct node* tgt;
    tgt = get_root(t);
    printDS(tgt);
}