# A Formal Interface for Concurrent Search Structure Templates (Artifact)
This repository contains the formalization accompanying the paper **A Formal Interface for Concurrent Search Structure Templates.**

- Our proofs are developed using the VST framework, originally developed by Mansky et al.<sup>(1)</sup>, whose development can be found on GitHub ([VST on Iris](https://github.com/PrincetonUniversity/VST/tree/vst_on_iris)).
- Our development builds on the flow framework by Krishna et al.<sup>(2, 3)</sup>, as integrated into Iris 4.3.0 by Patel et al.<sup>(4)</sup>, with minor modifications to adapt it to our setting. The standalone development of flow interfaces is available on GitHub ([Flow Interfaces Repository](https://github.com/nyu-acsys/template-proofs/tree/lockfree/templates/flows)).

# Getting Started Guide
To evaluate the artifact, we provide two options: 

(1) using a container that has the implementation installed already ([Option 1: Docker Container (Recommended)](#installation-option-1-docker-container-recommended)), or 

(2) installing the artifact locally on your machine ([Option 2: Local Installation](#installation-option-2-local-installation-alternative)). 

**(3) For both options, the artifact can be downloaded from ([Zenodo](https://doi.org/10.5281/zenodo.18319035)). For Option 2, the repository can also be cloned.**

## Installation Option 1: Docker container (Recommended)

To use the precompiled Docker image, first install the [Docker engine](https://docs.docker.com/engine/install/).
We provide two precompiled Docker images, depending on your machine architecture:

### Option A: AMD64 (Intel / x86_64 Linux/Windows)

Use this image if you are on an Intel/AMD x86_64 machine (linux/amd64):
```
docker load -i templates-artifact-amd64-built.tar.gz
docker run --rm -it templates-artifact:amd64-built /bin/bash
```

### Option B: ARM64 (Apple Silicon / ARM Linux)

Use this image if you are on Apple Silicon (M1/M2/M3/M4) or a linux/arm64 machine:
```
docker load -i templates-artifact-arm64-built.tar.gz
docker run --rm -it templates-artifact:arm64-built /bin/bash
```

**Note:** Using the wrong architecture may require emulation and can be significantly slower.

### Directory layout inside the container
-------------------------------------
```
/root
├── template-implementations/     # Runnable C implementations (executables)
│   ├── Makefile
│   ├── list.c
│   ├── bst.c
│   └── ...
├── template-proofs/              # Rocq development (proof scripts)
│   ├── Makefile
│   ├── verif_template.v
│   ├── verif_coarse.v
│   ├── verif_coupling.v
│   └── ...
├── flows/                        # Flow framework used by proofs
├── VST/                          # Verified Software Toolchain
└── ...                           # Other dependencies
```

### How to evaluate the artifact (C programs + Rocq/VST proofs)

This artifact can be evaluated in two complementary ways:

#### 1) Run the C implementations (executable sanity check)
Inside the Docker container, run:

```
cd root/template-implementations
make clean && make coupling list && ./list
```

Here, `coupling` selects the **lock-coupling template**, and `list` selects the **linked-list** data structure.

To run the **BST** version, replace `list` with `bst` (i.e., `make coupling bst && ./bst`). Repeat the above steps for the **give-up** template (e.g., `make giveup list && ./list` and `make giveup bst && ./bst`), and for the **coarse-grained locking** template (e.g., `make coarse list && ./list` and `make coarse bst && ./bst`).

**Expected output (C demos):**

Each executable (`./list` or `./bst`) runs a deterministic demo workload (a fixed sequence of inserts/lookups). The output is intended as a sanity check that:

- The program terminates normally (exit code 0).
- The printed output corresponds to a deterministic demo run (a fixed sequence of inserts/lookups), serving as a sanity check that the executable builds and runs correctly. The executable prints a *Traverse* section showing the final structure (either a Linked-List or a BST), followed by `lookup` results such as Lookup `key = 4: ten`.

#### 2) Evaluate the Rocq development (run the proofs)

The main way to evaluate the Rocq part is to compile the development, which checks all mechanized proofs.

Inside the Docker container (or after local installation), run:
```
cd root/template-proofs
eval $(opam env)
make clean
make -jN
```

Here, `N` sets the parallelism (e.g., `-j3`).

**Expected outcome:**

- A successful build (no errors) means all Rocq proof files were typechecked and the proofs were accepted.

- For the Rocq development, a successful build will show continuous compilation progress like the following:
```
make[1]: Entering directory '/root/template-proofs'
COQDEP VFILES
COQC flows_ora.v
...
COQC verif_template.v
COQC verif_coarse.v
COQC verif_giveup.v
COQC verif_coupling.v
make[1]: Leaving directory '/root/template-proofs'
```

If you see `COQC ...` lines continuing to appear, it indicates the proofs are still compiling normally, and the build may simply take some time depending on the machine resources.

## Installation Option 2: Local Installation (Alternative)

This option builds the Rocq development locally using **`opam`**. It creates a **fresh opam switch inside the artifact directory**, ensuring that none of your existing Rocq/Coq developments are affected.

### Prerequisite

This installation requires a working installation of **`opam`**. The provided script does **not** install `opam`; it only creates and uses a local switch. See [opam installation instructions](https://opam.ocaml.org/doc/Install.html).

### Building the Artifact

To build the artifact in a new opam switch, we provide an installation script, `build_artifact.sh`. Please run the following at the root of the artifact folder `./build_artifact.sh`

The `./build_artifact.sh` script
1. creates a fresh `opam` switch in the artifact directory,
2. installs all required dependencies in that switch, and
3. builds the Rocq implementation.

# Step-by-Step Instructions

This section describes (1) how to run the C implementation and (2) how the Rocq project corresponds to the paper.

## 1. Implementation in C

Our implementation is written in C and located in `template-implementations` directory. To run the program for each data structure (linked list or BST) with each template (coarse-grained locking, lock coupling, or give-up), use the following command:

```
cd root/template-implementations
make clean && make coupling list && ./list
```
Here, `coupling` selects the **lock-coupling template**, and `list` selects the **linked-list** data structure.

To run the **BST** version, replace `list` with `bst` (i.e., `make coupling bst && ./bst`). Repeat the above steps for the **give-up** template (e.g., `make giveup list && ./list` and `make giveup bst && ./bst`), and for the **coarse-grained locking** template (e.g., `make coarse list && ./list` and `make coarse bst && ./bst`).

### Expected output (C demos).
Each executable (`./list` or `./bst`) runs a deterministic demo workload (a fixed sequence of inserts/lookups). The output is intended as a sanity check that:

- the program terminates normally (exit code 0), and

- the printed results reflect successful operations under the chosen template.

### C source layout (high level)
- `common.h` contains utility functions used by the templates.
- `data_structure.h` declares the interface functions.
- `bst.c` and `list.c` implement BST and list interfaces defined in `data_structure.h`.
- `template.h` and `template.c` provide the top-level templates (defining `insert` and `lookup`).
- `coarse.h` and `coarse.c` implement coarse-grained locking template.
- `giveup.h` and `giveup.c` implement the give-up template.
- `coupling.h` and `coupling.c` implement the lock-coupling template.

## 2. Rocq development
We describe the Rocq development corresponding to each figure in the paper, proceeding from the data structure interface (Fig. 6) to the concurrency template interface (Fig. 7), then the definitions of selected predicates (Figs. 16 and 19), followed by the node definitions for BSTs and linked lists (Figs. 10 and 13), and finally the proof outlines (Figs. 9, 12, 17, and 18).

Our paper presents specifications using **Hoare triples** and **logically atomic triples**. In contrast, the mechanized proofs are carried out in VST (a Rocq-based separation logic framework). Below we illustrate, by example, how the paper notation corresponds to VST's function specifications.

### 2.1. Specifications in VST (by example)

**Example: Hoare triple (paper) vs VST spec (Rocq)**

Paper notation:

`∀n. { Int.min_signed ≤ n + n ≤ Int.max_signed } twice(n) { r. r = n + n }`

VST function specification:

```
DECLARE _twice
WITH n: Z
PRE  [tint] PROP(Int.min_signed <= n + n <= Int.max_signed) PARAMS(Vint (Int.repr n)) GLOBALS() SEP ()
POST [tint] PROP () LOCAL (temp ret_temp (Vint (Int.repr (n +. n)))) SEP ()
```

**Example: logically atomic triple (paper) vs atomic spec (VST)**

Paper notation:

`∀C. ⟨ Ref(css) | CSS(css, C) ⟩ insert(css, k, v) ⟨ Ref(css) | CSS(css, C [k← v]) ⟩`

In VST, logically atomic triples are expressed using **atomic function specifications**:

```
DECLARE _insert ... ATOMIC ...
OBJ C ...
WITH css, k, v
PRE  [...] PROP() PARAMS() GLOBALS() SEP (Ref css | CSS ... C css)
POST [...] PROP () LOCAL ()SEP (Ref css | CSS ... (<[k := v]> C) css)
```

*Takeaway.* The paper uses concise logical notation for clarity, whereas VST makes parameters, memory resources, and abstract state transitions explicit. Logically atomic triples correspond to atomic function specifications where abstract state changes are represented via `OBJ` parameters and separation-logic assertions.

### 2.2. Data structure interface (Fig. 6)

The data structure interface in Fig. 6 is formalized as `Class NodeRep` in `template-proofs/data_struct.v`; the **Hoare-triple specifications** of `findNext`, `insertOp`, and `lookupOp` correspond to `findnext_spec`, `insertOp_spec`, and `get_value_spec`, respectively.

The table below compares the paper predicates with their Rocq counterparts.

| Paper (Fig. 6)                       | Rocq                                                                                                     |
| ------------------------------------ | -------------------------------------------------------------------------------------------------------- |
| `node (n, In, Cn)`                   | `node p Ip Cp` in `template-proofs/data_struct.v`                                                        |
| `x ∈ ins(In, n)`                     | `in_inset _ _ _ x Ip p` in `template-proofs/data_struct.v`                                               |
| `x ∈ outs(In, next)`                 | `in_outset _ _ _ x Ip next` in `template-proofs/data_struct.v`                                           |
| `x ∉ outs(In)`                       | `¬ in_outsets _ _ Key x Ip` in `template-proofs/data_struct.v`                                           |
| `m ↦ next`                           | `data_at sh (tptr t_struct_node) n_pt n` in `template-proofs/data_struct.v`                              |
| `ks(In, n) = ks(I0, n) ⊎ ks(I1, n1)` | `keyset _ _ _ I0 p ∪ keyset _ _ _ I_new new_node = keyset _ _ _ Ip p` in `template-proofs/data_struct.v` |
| `In ≾ (I0 ⊕ I1)`                     | `contextualLeq _ Ip (I0 ⋅ I_new)` in `template-proofs/data_struct.v`                                     |

Differences between the paper and the Rocq development
- Argument naming
    + Paper: uses `n`, `In`, and `Cn` for node pointers, interfaces, and contents
    + Rocq: uses the names `p`, `Ip`, and `Cp` instead, chosen for convenience in the Rocq development.
- Heap edges: 
    + Paper: heap maps-to is written abstractly as `m ↦ next`.
    + Rocq: heap maps-to relations in the paper correspond to VST predicates such as `data_at`, which make memory layout and permissions explicit.
- Set membership
    + Paper: membership is written using set notation (e.g., `x ∈ ins(In, n)` and `x ∈ outs(In, next)`).
    + Rocq: membership is expressed by predicates such as `in_inset` and `in_outset`, which additionally take invariant arguments.
- Keysets: 
    + Paper: keysets are written using ks and combined with disjoint union `⊎`.
    + Rocq: keysets are written using keyset and combined using explicit set union `∪`.
- Composition of flows and contextual extension
    + Paper: written using symbolic operators (`⊕`, `≾`).
    + Rocq: written using named operations and relations (`⋅`, `contextualLeq`).
- Additional predicates
    + Rocq: includes several auxiliary predicates that do not appear in the paper. These predicates are introduced for mechanization purposes and are omitted from the paper for brevity, as they do not add conceptual insight.

### 2.3. Concurrency template interface (Fig. 7)

The concurrency template interface in Fig. 7 is formalized as `Class Template` in `template-proofs/template_class.v`; the **logically atomic specifications** of `traverse`, `insertHelper`, and `lookupHelper` correspond to `traverse_spec`, `insertOp_helper_spec`, and `lookupOp_helper_spec`, respectively.

The table below compares the paper predicates with their Rocq counterparts.

| Paper (Fig. 7)               | Rocq                                                                                                       |
| ---------------------------- | ---------------------------------------------------------------------------------------------------------- |
| `InFP(n, p, lk)`             | `inFP γ_f pnN p1 l` in `template-proofs/template_class.v`                                                  |
| `is_root(n)`                 | `is_root_t γ_n pnN` in `template-proofs/template_class.v`                                                  |
| `md_node (n, p, Rn, css, r)` | `md_entry_rep_t γ_I γ_k γ_m γ_n p1 p nr css r` in `template-proofs/template_class.v`                       |
| `CSS(css, C)`                | `CSSt γ_I γ_f γ_k γ_g γ_m γ_n C css` in `template-proofs/template_class.v`                                 |
| `x ∈ ks(Rn.I, n)`            | `in_inset _ _ _ x (Ip_of nrt) pt ∧ ¬ in_outsets _ _ _ x (Ip_of nrt)` in `template-proofs/template_class.v` |

Differences between the paper and the Rocq development
- Naming and parameters
    + Paper: uses compact predicates with implicit parameters (e.g., `n`, `p`, `Rn`). 
    + Rocq: predicates carry additional ghost names and explicit parameters (e.g., `γ_I`, `γ_k`, `γ_m`, `γ_n`) required by the mechanized development. The metadata record `Rn` (with flow interface `Rn.I` and contents map `Rn.C`) corresponds to `nr`; the paper's pointer `p` corresponds to `p1`, and the paperss node `n` corresponds to `p`.
- Compound predicates
    + Paper: expresses keyset membership using a single predicate (`x ∈ ks(Rn.I, n)`).
    + Rocq: keyset membership is expanded into inset/outset predicates, reflecting the definition `ks(Rn.In, n) := ins(Rn.In, n) \ outs(Rn.In)`.
- Postcondition of the `traverse` and `lookupHelper` specifications
    + Paper: only two cases are considered, `F` and `NF`.
    + Rocq: distinguishes an additional `CNT` case; `NF` and `CNT` differ only by whether `pt = nullval` and are merged in the paper for brevity. 
- Additional predicates
    + Rocq: includes additional auxiliary predicates introduced for mechanization and omitted from the paper for brevity, as they add no conceptual insight.

### 2.4. Definition of CSS (Fig. 16)

The definitions of `CSS` and related predicates used in the lock-coupling proof in Fig. 16 are formalized in `template-proofs/coupling_lib.v`.

The table below compares the paper predicates with their Rocq counterparts.

| Paper (Fig. 16)                                 | Rocq                                                                                                            |
| ----------------------------------------------- | --------------------------------------------------------------------------------------------------------------- |
| `Rn := (In, Cn)`                                | `NodeR := { Cp : gmap Key KValue; Ip : flowint_T; }` in `template-proofs/coupling_lib.v`                        |
| `φ(r, I)`                                       | `globalinv _ _ _ r I` in `template-proofs/coupling_lib.v`                                                       |
| `InFP(n, p, lk)`                                | `inFP (γ_f : gname) (n : Node) (m : val) (lock : val)` in `template-proofs/data_struct.v`                       |
| `◯ N`<sup>`γf`</sup>                            | `own (inG0 := nodemap_inG) γ_f (◯ (to_agree <$> N) : gmap_authR Node _)` in `template-proofs/data_struct.v`     |
| `own_nodes(γf, I, h)`                           | `own_nodes γ_f (I : @multiset_flowint_ur Key _ _ ) md` in `template-proofs/data_struct.v`                       |
| `● N`<sup>`γf`</sup>                            | `own (inG0 := nodemap_inG) γ_f (● (to_agree <$> N))` in `template-proofs/data_struct.v`                         |
| `md_node (n, p, Rn, css, r)`                    | `md_entry_rep γ_I γ_k γ_m γ_n p1 (p : Node) (nr : NodeR) css r` in `template-proofs/coupling_lib.v`             |
| `◯ In`<sup>`γI`</sup>                           | `own γ_I (◯ (Ip nr))` in `template-proofs/coupling_lib.v`                                                       |
| `◯ (ks(In, n), dom(Cn))`<sup>`γk`</sup>         | `own γ_k (◯ prod (keyset _ _ _ nr.(Ip) p, dom (Cp nr)) : keyset_authR Key)` in `template-proofs/coupling_lib.v` |
| `◯ (Ex Cn)`<sup>`γm`</sup>                      | `own γ_m (◯ (Excl <$> (Cp nr)) : keymap_authR _ _)` in `template-proofs/coupling_lib.v`                         |
| `CSS(css, C)`                                   | `CSS γ_I γ_f γ_k γ_g γ_m γ_n C css` in `template-proofs/coupling_lib.v`                                         |
| `● I`<sup>`γI`</sup>                            | `own γ_I (● I)` in `template-proofs/coupling_lib.v`                                                             |
| `● (KS, dom(C))`<sup>`γk`</sup>                 | `own γ_k (● prod (KS, dom C) : keyset_authR Key)` in `template-proofs/coupling_lib.v`                           |
| `● (Ex C)`<sup>`γm`</sup>                       | `own γ_m (● (Excl <$> C) : keymap_authR _ _)` in `template-proofs/coupling_lib.v`                               |
| `p.lock ↦□ lk`                                  | `field_at lsh t_md_entry [StructField _lock] lock p1` in `template-proofs/coupling_lib.v`                       |
| `hashtable(h)`                                  | `([∗ set] i ∈ upto_gset size ∖ {[0%Z]}, md_slot i css)` in `template-proofs/coupling_lib.v`                     |
| `inv_for_lock (lk, md_node (n, p, Rn, css, r))` | `inv_for_lock lock (md_entry_rep γ_I γ_k γ_m γ_n p1 p nr css r)` in `template-proofs/coupling_lib.v`            |

Differences between the paper and the Rocq development
- Naming and parameters
    + Paper: uses compact predicates with implicit parameters (e.g., `n`, `p`, `Rn`).
    + Rocq: uses explicit parameters and ghost names (e.g., `γ_I`, `γ_k`, `γ_m`, `γ_n`). The metadata record `Rn` (with flow interface `Rn.I` and contents map `Rn.C`) corresponds to `nr`. The paper's pointer `p` corresponds to `p1`, and the paper's node `n` corresponds to `p`.
- Global invariants
    + Paper: writes the global invariant abstractly as `φ(r, I)`.
    + Rocq: represents it explicitly as `globalinv` (can be found in `flows/theories/inset_flows.v`).
- Representation of `own_nodes`
    + Paper: `own_nodes(γ_f, I, h)` is defined using an abstract total function `h : val → val`, which maps a node address `n` directly to its associated
    pointer value `h(n)`. Node metadata is thus treated as a simple functional mapping, abstracting away from any concrete memory representation.
    + Rocq: the abstract function `h` is implemented by a concrete metadata array `md`, represented as a list. A hash function `f : val → Z` maps each node
    address to an index in the array. Accordingly, the paper's condition `h(n) = p` is expressed as `Znth (f n) md = p`, together with the explicit
    bounds condition `0 ≤ f n < Zlength md`. These bounds are required in Rocq to ensure totality and safe array access.
- Ghost ownership (`◯` / `●`)
    + Paper: uses abstract ghost assertions such as `◯ N`<sup>`γf`</sup> and `● N`<sup>`γf`</sup> (and similarly for `γI`, `γk`, `γm`) to describe shared vs. authoritative knowledge.
    + Rocq: realizes these assertions using Iris's own predicate over concrete authoritative resource algebras (e.g., `gmap_authR`, `keyset_authR`, `keymap_authR`), making the underlying ghost state and validity conditions explicit.
- C-level memory layout and field access
    + Paper: uses abstract heap assertions such as `p.lock ↦□ lk`.
    + Rocq: replaces these with VST separation-logic predicates that expose the concrete C struct layout, e.g., `field_at lsh t_md_entry [StructField _lock] lock p1`, including permissions and field projections.
- Hashtable/metadata slots are made explicit
    + Paper: treats the hashtable abstraction (`hashtable(h)`) at a high level.
    + Rocq: expands it into a big separation over all slots, e.g., `([∗ set] i ∈ upto_gset size ∖ {[0%Z]}, md_slot i css)`, which is needed to reason about disjointness and updates at individual indices.
- More auxiliary predicates (mechanization artifacts)
    + Paper: omits routine bookkeeping predicates to keep the presentation focused.
    + Rocq: introduces auxiliary predicates (e.g., for slot invariants, agreement maps, and well-formedness side conditions) to support proof automation and ensure totality/safety; these are omitted from the paper for brevity, as they add little conceptual insight.

### 2.5. Definition of `md_node` for the give-up template (Fig. 19)

The definitions of `md_node` and related predicates used in the give-up proof in Fig. 19 are formalized in `template-proofs/giveup_lib.v`.

The table below compares the paper predicates with their Rocq counterparts.

| Paper (Fig. 19)                                     | Rocq                                                                                                     |
| --------------------------------------------------- | -------------------------------------------------------------------------------------------------------- |
| `Rn := (In, Cn, minₙ, maxₙ)`                        | `NodeR := { min : Z; max : Z; Cp : gmap Key KValue; Ip : flowint_T; }` in `template-proofs/giveup_lib.v`  |
| `md_node (n, p, Rn, css, r)`                        | `md_entry_rep γ_I γ_k γ_m γ_n p1 (p : Node) (nr : NodeR) (css r : val)` in `template-proofs/giveup_lib.v` |
| `p.min ↦ minₙ`                                      | `field_at Ews t_md_entry [StructField _min] (vint (min nr)) p1` in `template-proofs/giveup_lib.v`         |
| `p.max ↦ maxₙ`                                      | `field_at Ews t_md_entry [StructField _max] (vint (max nr)) p1` in `template-proofs/giveup_lib.v`         |
| `p ≠ NULL ⇒ (∀k. minₙ < k < maxₙ ⇒ k ∈ ins(Iₙ, n))` | `(p <> nullval → ∀ k, (min nr < k < max nr)%Z → in_inset _ _ _ k (Ip nr) p)`                               |

Differences between the paper and the Rocq development
- Extended metadata record
    + Paper: the metadata record is written abstractly as `Rn := (In, Cn, minₙ, maxₙ)`.
    + Rocq: this record is realized concretely as NodeR, with explicit fields `min` and `max` in addition to the flow interface `Ip` and contents map `Cp`.
- Concrete memory layout
    + Paper: field access is written abstractly (e.g., `p.min ↦ minₙ`).
    + Rocq: field access is expressed using VST separation-logic predicates such as `field_at Ews t_md_entry [StructField _min] (vint (min nr)) p1`, exposing the C struct layout and permissions.
- Explicit parameters and ghost state
    + Paper: suppresses ghost parameters and proof artifacts.
    + Rocq: the predicate md_node is expanded into md_entry_rep with explicit ghost names (`γ_I`, `γ_k`, `γ_m`, `γ_n`), pointers, and metadata, which are required for mechanized verification.
- Auxiliary structure
    + Rocq: introduces additional auxiliary predicates and parameters to support proof automation and safety guarantees; these are omitted from the paper for brevity, as they do not add conceptual insight.

### 2.6. The `node` definition of BST (Fig. 10)
- **Fig. 10 (BST `node`)** is formalized as `Program Instance specific_node_rep : NodeRep` in `template-proofs/verif_bst.v`.

### 2.7. The `node` definition of linked list (Fig. 13)
- **Fig. 13 (linked list `node`)** is formalized as `Program Instance specific_node_rep : NodeRep` in `template-proofs/verif_list.v`.

### 2.8. Proof outlines (Figs. 9, 12, 17, and 18)
- **Fig. 9 (top-level `insert`)** is formalized in `template-proofs/verif_template.v`: its logically atomic specification is `insert_spec`, and its proof is `Lemma insert`.
- **Fig. 12 (BST `insertOp`)** is formalized as follows: its Hoare-triple specification is `insertOp_spec` in `template-proofs/data_struct.v`, and its proof is `Lemma insertOp` in `template-proofs/verif_bst.v`.
- **Fig. 17 (lock-coupling `traverse`)** is formalized in `template-proofs/template_class.v`: its logically atomic specification is `traverse_spec`, and its proof is `Lemma traverse_lock` in `template-proofs/verif_coupling.v`.
- **Fig. 18 (lock-coupling `insertHelper`)** is formalized in `template-proofs/template_class.v`: its logically atomic specification is `insertOp_helper_spec`, and its proof is `Lemma insertOp_helper` in `template-proofs/verif_coupling.v`.

## 3. What claims from the paper are supported by this artifact?

This artifact supports the paper's claims by providing:

1. A mechanized formalization of the interfaces:
   - Data structure interface (Fig. 6): `template-proofs/data_struct.v`
   - Template interface (Fig. 7): `template-proofs/template_class.v`

2. Mechanized proofs (checked by Rocq/VST compilation) for:
   - Top-level insert (Fig. 9): `template-proofs/verif_template.v`
   - BST insertOp (Fig. 12): `template-proofs/verif_bst.v`
   - Lock-coupling traverse + insertHelper (Figs. 17–18): `template-proofs/verif_coupling.v`
   - Coarse-grained template: `template-proofs/verif_coarse.v`
   - Give-up template: `template-proofs/verif_giveup.v`

How to verify:
- Run `make -jN` in the Rocq development. Successful compilation means the proofs are checked.
- Run the C implementations (Section 1) to confirm the executable builds and runs.

#### Key proof files (entry points)
- `template-proofs/verif_template.v`   (top-level insert)
- `template-proofs/verif_bst.v`        (BST insertOp)
- `template-proofs/verif_list.v`       (List node + insertOp)
- `template-proofs/verif_coupling.v`   (lock-coupling template proofs)
- `template-proofs/verif_coarse.v`     (coarse-grained template proofs)
- `template-proofs/verif_giveup.v`     (give-up template proofs)

## 4. Proof Modules Summary

Outside of what is explicitly discussed in the paper, we summarize the specification and verification modules included in the `template-proofs` directory below:

- Specifications of BST and Linked List (`template-proofs/data_struct.v`)
- Verification of BST (`template-proofs/verif_bst.v`)
- Verification of Linked List (`template-proofs/verif_list.v`)
- Specifications of Templates (`template-proofs/template_class.v`)
- Verification of Coarse-Grained Template (`template-proofs/verif_coarse.v`)
- Verification of Lock-Coupling Template (`template-proofs/verif_coupling.v`)
- Verification of Give-Up Template (`template-proofs/verif_giveup.v`)
- Specifications and Verification of Top-Level Code (`template-proofs/verif_template.v`)

## 5. Hash Function Assumptions and Specification

We model the hash function abstractly as a pure Coq function: `Parameter f : val -> Z.` together with the following axioms:
- Injectivity: `f new = f p → new = p`. This assumption ensures that distinct pointers map to distinct hash values, simplifying reasoning about key uniqueness in the verified data structure.
- Null Hashing: `f nullval = 0`. The null pointer is mapped to hash value `0`.

The C function `hash` is specified in VST as:

```
DECLARE _hash
    WITH p : val
    PRE [ tptr tvoid ] 
    PROP (is_pointer_or_null p) PARAMS (p) GLOBALS () SEP ()
    POST [ tint ]
    PROP ((0 ≤ f p < size)%Z /\ repable_signed (f p)) RETURN (vint (f p)) SEP ().
```
That is, given a pointer (or null), `hash(p)` returns the integer value `f(p)`, which lies within the hash table bounds and is representable as a signed machine integer. The specification is purely functional and does not manipulate memory.

All axioms and the corresponding VST specification can be found in `template-proofs/common.v`.

# References

1. Mansky, William, and Ke Du. "An Iris instance for verifying CompCert C programs." Proceedings of the ACM on Programming Languages 8, no. POPL (2024): 148-174. 

2. Krishna, Siddharth, Dennis Shasha, and Thomas Wies. "Go with the flow: Compositional Abstractions for Concurrent Data Structures." Proceedings of the ACM on Programming Languages 2, no. POPL (2017): 1-31.

3. Krishna, Siddharth, Alexander J. Summers, and Thomas Wies. "Local Reasoning for Global Graph Properties." In ESOP 2020, pp. 308–335.

4. Patel, Nisarg, Dennis Shasha, and Thomas Wies. "Verifying Lock-Free Search Structure Templates." In ECOOP 2024. LIPIcs 313, pp. 30:1–30:28.