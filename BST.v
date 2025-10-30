Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.


(* Tree type - Exercise 3.1 *)
Inductive tree :=
| leaf : tree
| node : tree -> nat -> tree -> tree.

(* Examples from from PDF *)
Definition tree1 :=
  node (node (node leaf 2 leaf) 5 (node leaf 7 leaf))
       10
       (node (node leaf 12 leaf) 16 (node leaf 17 leaf)).

Definition tree2 :=
  node (node (node leaf 1 leaf) 2 (node leaf 3 leaf))
       4
       (node leaf 5 leaf).

Inductive sorted : tree -> Prop  :=
| leaf_sorted : sorted leaf
(* TODO: add node constructor cases *)
.

Fixpoint elem_of (x:nat) (t:tree) : bool 
(* TODO: implement elem_of *)
. Admitted.

Fixpoint insert (x:nat) (t:tree) : tree 
(* TODO: implement insert *)
. Admitted.