#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <stdint.h>
#include "threads.h"
#include "common.h"

typedef struct node node;
Status findNext(node *p_ds, node **n_ds, int x);
node *insertOp(node *p_ds, int x, void *value);
void *get_value(node* p_ds);
int get_key(node* p_list);

//support print function 

void *get_left(node *node); //for BST
void *get_right(node *node); //for BST
void *get_next(node *node); //for list

void print_key_value(node *node);

#pragma once
typedef struct stack {
    struct node * items[100]; // Assuming a maximum of 100 nodes
    int top;
} stack;

#ifndef INLINE_STACK
#define INLINE_STACK

static void initStack(stack* s) {
    s->top = -1;
}

// Function to push a node onto the stack
static void push(stack* s, node * item) {
    s->items[++s->top] = item;
}

// Function to check if the stack is empty
static int isEmpty(stack* s) {
    return s->top == -1;
}

// Function to pop a node from the stack
static node* pop(stack* s) {
    if (!isEmpty(s)) {
        return s->items[s->top--];
    }
    return NULL;
}

#endif // INLINE_STACK

void printDS (node *p);
