# README


This goal of this repository is to certify results of the type `Lower_bound m t g` (defined in `Coq/coqbinstretching.v` and explained in the companion research paper).

## Package dependencies (on a Linux distribution)

- coq
- xz-utils
- g++


## Content

- `README`: this file
- `Coq/binstretching.v`: the coq script containing theorems, proofs and functions in order to certify `Lower_bound` results
- `Coq/testnewtree.sh`: a bash script that
  1. creates a file coq_gen_script.v which proves the requested `Lower_bound` property by reading the input tree in `witnesses/`
  2. runs this file
- `Coq/witnesses/*.v`: files defining in Coq a witness tree for the corresponding `Lower_bound` property
- `converter/*`: contains the converter from a DOT format to the Coq format
- `lowerbounds/*.gen`: files defining a witness tree in a DOT format




## Usage (to certify provided results)

In the repository `Coq/witnesses/` are present files allowing to certify the property `Lower_bound` for the following values:
```
m t g = 4 19 14
        5 19 14
        6 19 14
        7 19 14
        8 19 14
        3 112 82
```
     
Each property can be certified by running the command: `cd Coq && ./testnewtree.sh m t g`.

Note that this command takes a few minutes to certify `Lower_bound 7 19 14` and more than one hour to certify `Lower_bound 8 19 14`, as well as several GB of memory. If the property is certified, then it is printed on the standard output.

## Usage (to certify new results)

The folder `converter/` contains a converter from an easy-to-generate DOT format to the Coq format described below.
For instance, executing the command `./compile.sh 19 14 6` creates the binary file `build/rooster-6-19-14` which is able to translate a DOT file witnessing the property `Lower_bound 6 19 14`.
Examples of entry files are present in the folder `lowerbounds/`. The files of `Coq/witnesses/` have been generated using for instance the command:
```
./converter/build/rooster-6-19-14 lowerbounds/lb-6-19-14.gen Coq/witnesses/lb_6_19_14.v
```

The labels of these graphs are explained below, with arbitrary values.
- On the vertices
  - `player = alg | adv`: determines which player will play next, the adversary or the algorithm.
  - `loads = "11 10 3 0"`: describes the current height of each bin, in non-increasing order.
  - `next_item = 9`: on an algorithm node, describe the value of the next item chosen by the adversary.
  - `optimal = "({9,5}, {10,3}, {10,3}, {10})"`: on each algorithm node with no successor, describes an optimal packing of the elements chosen by the adversary on this path.
- On the edges
  - `bin = 2`: connects an `alg` node to an `adv` node where the height of the corresponding bin is increased by the item previously chosen by the adversary. There must be such an edge for every bin index except if the height of the bin exceeds the target `t` or in case of duplicates.
  - `next_item = 9`: connects an `alg` node to an `adv` node, where the value of `next_item` in the `adv` node is equal to this one.



## Format (Coq)


#### Types defined in `binstretching.v`

A tree is defined in Coq in the following format:

```
Inductive treeN  :=
  | nd : BinLoadsN -> N  -> forestN -> treeN
  | lf : BinLoadsN -> list N -> BinsExtendedN -> treeN
with forestN :=
  | leafN :  forestN
  | consN : treeN -> forestN -> forestN
.
Notation "[[ ]]" := leafN (format "[[ ]]") .
Notation "[[ x ]]" := (consN x leafN) .
Notation "[[ x ; y ; .. ; z ]]" :=  (consN x (consN y .. (consN z leafN) ..)).
```

where `BinLoadsN` is a list of binary integers (type `N`) representing the heights of the bins associated to this node, and `BinsExtendedN` is a list of list of binary integers, representing a packing of the relevant elements in bins.

- The first parameter of a tree node is the current state of the bins reached by an online algorithm.
- The second parameter of a tree node is the next element(s) sent by the adversary. On an internal node, there is only one element. On a leaf node, there can be multiple ones.
- The third parameter of an internal node (type `forestN`) represents the children of that node, i.e., the nodes that can be reached from this node while maintaining all bins small enough.
- The third parameter of a leaf node represents an offline packing of all the elements.
- An element of type `forestN` can be represented as a list, replacing the brackets by double-brackets: `Definition f := [[ t1 ; t2 ; t3 ]].`

In order to avoid duplicated subtrees, we define a new type `RecordN`, which can be seen as a list of trees:

```
Inductive recordN := recN: list elt ->  treeN -> recordN.
Definition RecordN := list recordN.
```

- An element `recN l t` of type `recordN` represents a tree `t` whose root node corresponds to a state after the elements of `l` have been packed by an online algorithm.
Any internal node `nd St e F` of `t` can omit some children nodes in `F` if such a node is a root of a tree present in the following part of the record. This way, several nodes can declare the same tree as a child node, which allows the checker to verify such a tree only once.


#### Format of a tree file `witnesses/lb_$m_$t_$g.v`

We require to define two variables. `lb_T` represents the top part of the tree, so the state of its root node must not contain non-zeros. `lb_R` contains the list of records.

One of the simplest lower bound, `Lower_bound 2 4 3`, can then be proved if the file `witnesses/lb_2_4_3.v` defines the following variables (note that the record node is used only once, so is not useful in this example; this node could simply be added to `lb_T` as in the second example below).

```
Require import binstretching.

Definition lb_T :=(
  (nd [] 1 
  [[ nd [1] 1 
    ([[lf [2] [2;2] [ [1;2] ; [1;2] ] ]]) 
  ]])
  )%N.
  
Definition lb_R : RecordN :=
([ recN [1;1]   (lf [1;1] [3] [ [1;1] ; [3] ] ) ])%N.
```


```
Require import binstretching.

Definition lb_T :=(
  (nd [] 1 
  [[ nd [1] 1 
    ([[lf [2] [2;2] [ [1;2] ; [1;2] ];
       lf [1;1] [3] [ [1;1] ; [3] ]  ]]) 
  ]])
  )%N.
  
Definition lb_R : RecordN := ([])%N.
```


## Authors

Martin Böhm and Bertrand Simon


