Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.



Inductive tree :=
| leaf : tree
| node : tree -> nat -> tree -> tree.

(* Tree type examples from PDF  - Exercise 3.1 *)
Definition tree1 :=
  node (node (node leaf 2 leaf) 5 (node leaf 7 leaf))
       10 (* root *)
       (node (node leaf 12 leaf) 16 (node leaf 17 leaf)).

Definition tree2 :=
  node (node (node leaf 3 leaf) 2 (node leaf 4 leaf))
       1 (* root *)
       (node leaf 5 leaf).

(* Exercise 3.2 - Helper functions *)
Inductive greater :  nat -> tree -> Prop :=
|leaf_greater : forall n, greater n leaf
|node_greater : forall n l v r, 
    n > v ->
    greater n l ->
    greater n r ->
    greater n (node l v r)
.
Inductive smaller  : nat -> tree -> Prop :=
|leaf_smaller : forall n, smaller n leaf
|node_smaller : forall n l v r, 
    n < v ->
    smaller n l ->
    smaller n r ->
    smaller n (node l v r)
.

(* Exercise 3.2 - sorted *)
Inductive sorted : tree -> Prop  :=
| leaf_sorted : sorted leaf
| node_sorted : forall l v r,
    greater v l ->
    smaller v r ->
    sorted l ->
    sorted r ->
    sorted (node l v r)
.
Hint Constructors sorted : core.
Hint Constructors smaller : core. 
Hint Constructors greater : core. 

(* Exercise 3.3 *)
Example tree_is_sorted1 : sorted tree1.
Proof. unfold tree1. repeat constructor. Qed.

Example tree_is_sorted2 : not (sorted tree2).
Proof. 
  unfold not. unfold tree2. intros. inversion H; subst. clear H. 
  inversion H3. subst. inversion H7; subst. inversion H0.
Qed.


Fixpoint elem_of (x:nat) (t:tree) : bool 
(* TODO: implement elem_of *)
. Admitted.

Fixpoint insert (x:nat) (t:tree) : tree 
(* TODO: implement insert *)
. Admitted.