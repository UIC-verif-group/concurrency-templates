# Run program 

To run the program for each data structure (linked list or BST) with each template (coarse-grained locking, lock-coupling, or give-up), do the following:

```sh
make clean 
make coupling list 
./list
```

In `make coupling list`, `coupling` selects the lock-coupling template and `list` selects the linked list.
Repeat the same steps with `bst` instead of `list` (i.e. `make coupling bst && ./bst`), and then repeat both cases for the give-up template (e.g. `make giveup list && ./list` and `make giveup bst && ./bst`).

# Detailed Program

- `common.h` contains utility functions used by the templates.
- `data_structure.h` declares the interface functions.
- `bst.c` and `list.c` implement the BST and list interfaces defined in `data_structure.h`.
- `template.h` and `template.c` provide the top-level templates, defining the `insert` and `lookup` functions.
- `coarse.h` and `coarse.c` implement the coarse-grained locking template, based on `template.h` and `data_structure.h`.
- `giveup.h` and `giveup.c` implement the give-up template, based on `template.h` and `data_structure.h`.
- `coupling.h` and `coupling.c` implement the lock-coupling template, based on `template.h` and `data_structure.h`.

