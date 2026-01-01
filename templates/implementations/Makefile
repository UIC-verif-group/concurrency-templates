CC = gcc
CFLAGS = -pthread

TARGETS = bst list

ifeq ($(filter list, $(MAKECMDGOALS)),list)
    CASE = 2
    TARGET = list
else ifeq ($(filter bst, $(MAKECMDGOALS)),bst)
    CASE = 1
    TARGET = bst
else
    CASE = 0
    TARGET = bst
endif

ifeq ($(filter lock, $(MAKECMDGOALS)),coupling)
    LOCK_TYPE = coupling
else ifeq ($(filter giveup, $(MAKECMDGOALS)),giveup)
    LOCK_TYPE = giveup
else ifeq ($(filter coarse, $(MAKECMDGOALS)),coarse)
    LOCK_TYPE = coarse
else
    LOCK_TYPE = coupling
endif

ifeq ($(CASE), 1)
    OBJS = threads.o SC_atomics.o bst.o $(LOCK_TYPE).o template.o main.o
else ifeq ($(CASE), 2)
    OBJS = threads.o SC_atomics.o list.o $(LOCK_TYPE).o template.o main.o
endif

.SECONDARY:

.DEFAULT_GOAL := all

all: $(TARGETS)

$(TARGETS): $(OBJS)
	$(CC) $(CFLAGS) -o $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(TARGETS) $(OBJS) *.gch *.o bst list *.out

.PHONY: coupling giveup coarse clean

coupling: clean
coupling: CFLAGS += -DLOCK_TYPE=\"coupling\"
coupling: all

giveup: clean
giveup: CFLAGS += -DLOCK_TYPE=\"giveup\"
giveup: all

coarse: clean
coarse: CFLAGS += -DLOCK_TYPE=\"coarse\"
coarse: all