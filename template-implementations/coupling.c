#include "coupling.h"

md_entry* lookup_md(css* c, node* p){
    return c->metadata[hash(p)];
}

//FOUND = 0, NOTFOUND = 1, CONTINUE = 2
Status traverse(css *c, pn *pn, int x) {
    Status status = CONTINUE;
    md_entry *md = lookup_md(c, pn->n);
    acquire(md->lock);    
    if(!pn->n){
        node *r = c->root;
        if (hash(r) == hash(pn->n)){
            return CONTINUE;
        }
        else{
            pn->n = r;
            release(md->lock);
        } 
    }
    else{
        release(md->lock); 
    } //special case for empty data structure

    md_entry *md_n = lookup_md(c, pn->n);
    md_entry *md_p;
    acquire(md_n->lock); 
    for( ; ; ){
        pn->p = pn->n;
        status = findNext(pn->p, (node**)&pn->n, x);
        if (status == FOUND){
            break;
        }
        else if (status == NOTFOUND){
            break;
        }
        else{
            md_n = lookup_md(c, pn->n);
            acquire(md_n->lock); // acquire pn->n
            md_p = lookup_md(c, pn->p);
            release(md_p->lock); // release pn->p
        }
    }
    return status;
}

void insertOp_helper(css *c, node *p, int x, void *value){
    node *new_node = insertOp(p, x, value);
    if (!new_node){
        md_entry *md = lookup_md(c, p);
        lock_t lockp = md->lock;
        release(lockp);
        return;
    }
    
    // Allocate metadata for the new node
    int idx = hash(new_node);
    c->metadata[idx] = surely_malloc(sizeof(md_entry));

    // Initialize and set lock for the new node
    lock_t lock = makelock();
    c->metadata[idx]->lock = lock;
    
    // Handle case where status is CONTINUE (p == NULL)
    if (p == NULL) {
        c->root = new_node;
        md_entry* md = lookup_md(c, NULL);
        lock_t lockp = md->lock;
        release(lock);
        release(lockp);
        return;
    }
    md_entry *md = lookup_md(c, p);
    lock_t lockp = md->lock;
    release(lock);
    release(lockp);
}

void *lookupOp_helper(css *c, node *p, int x, Status status){
    void *v = NULL;
    if (status == FOUND){
        v = get_value(p);
    }
    else{
        v = NULL;
    }
    md_entry *md = lookup_md(c, p);
    lock_t lockp = md->lock;
    release(lockp);
    return v;
}

css *make_css(){
    css *new_css = (css*) surely_malloc(sizeof(css));
    int idx = hash(NULL);
    new_css->metadata[idx] = surely_malloc(sizeof(md_entry));

    lock_t lock = makelock();
    new_css->root = NULL;
    new_css->metadata[idx]->lock = lock;
    release(lock);

    return new_css;
}

node *get_root(css* t){
    md_entry* md = lookup_md(t, NULL);
    acquire(md->lock);
    node *r = t->root;
    release(md->lock);
    return r;
}

//Print
void printDS_helper (css *t){
    printf ("LOCK-COUPLING Template - ");
    struct node* tgt;
    tgt = get_root(t);
    printDS(tgt);
}