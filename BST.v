Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Lia.


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

(* Exercise 3.4 *)
Fixpoint elem_of (x:nat) (t:tree) : bool :=
match t with
| leaf => false
| node l v r => 
  if v =? x
  then true 
  else
    if x <? v
    then 
      elem_of x l 
    else
      elem_of x r
  (* More concise:
    (v =? x) || 
    (if x <? v then elem_of x l else elem_of x r)
  *)
end.

(* Positive tests *)
Example tree_elem_of_16 : elem_of 16 tree1 = true.
Proof. unfold tree1. reflexivity. Qed.

Example tree_elem_of_2 : elem_of 2 tree1 = true.
Proof. unfold tree1. reflexivity. Qed.

(* Negative tests *)
Example tree_elem_of_88 : elem_of 88 tree1 = false.
Proof. unfold tree1. reflexivity. Qed.

Example tree_elem_of_42 : elem_of 42 tree1 = false.
Proof. unfold tree1. reflexivity. Qed.

Fixpoint insert (x:nat) (t:tree) : tree :=
match t with
| leaf => node leaf x leaf 
| node l v r => 
  if v =? x then
  t
  else if v <? x then
  node l v (insert x r)
  else
  node (insert x l) v r
end.
Transparent insert.

Example insert_empty : insert 42 leaf = (node leaf 42 leaf).
Proof.
  reflexivity.
Qed.

Example insert_copy : insert 2 tree1 = 
        node (node (node leaf 2 leaf) 5 (node leaf 7 leaf))
       10 (* root *)
       (node (node leaf 12 leaf) 16 (node leaf 17 leaf)).
Proof.
  unfold tree1. reflexivity.
Qed.


Example insert_42 : insert 42 tree1 = 
        node (node (node leaf 2 leaf) 5 (node leaf 7 leaf))
       10 (* root *)
       (node (node leaf 12 leaf) 16 (node leaf 17 (node leaf 42 leaf))).
Proof.
  unfold tree1. reflexivity.
Qed.

Example insert_1 : insert 1 tree1 = 
        node (node (node (node leaf 1 leaf) 2 leaf) 5 (node leaf 7 leaf))
       10 (* root *)
       (node (node leaf 12 leaf) 16 (node leaf 17 leaf)).
Proof.
  unfold tree1. reflexivity.
Qed.

Example insert_nested : insert 2 (insert 5 (insert 10 leaf)) = node (node (node leaf 2 leaf ) 5 leaf) 10 leaf.
Proof. reflexivity. Qed.
(* Built tree up from skratch using insert *)



Lemma smaller_insert : forall n x t,
  smaller n t -> n < x -> smaller n (insert x t).
Proof.
  induction t as [| l IHl v r IHr]; simpl; intros Hsm Hlt.
  - constructor; easy.
  - inversion Hsm; subst; clear Hsm.
    destruct (v=?x) eqn:Heq.
    + constructor; easy.
    + destruct (v<?x) eqn:Hgt; constructor; try easy.
      * apply IHr; easy.
      * apply IHl; easy.
Qed.

Lemma greater_insert : forall n x t,
  greater n t -> n > x -> greater n (insert x t).
Proof.
  induction t as [| l IHl v r IHr]; simpl; intros Hg Hgt.
  - constructor; easy.
  - inversion Hg; subst; clear Hg.
    destruct (v=?x) eqn:Heq.
    + constructor; easy.
    + destruct (v<?x); constructor; try easy.
      * apply IHr; easy.
      * apply IHl; easy.
Qed.

Hint Resolve smaller_insert : core.
Hint Resolve greater_insert : core.

(* Exercise 3.8  *)
Lemma insert_sorted :
  forall t x, sorted t -> sorted (insert x t).
Proof.
  induction t; simpl; intros.
  - constructor; easy.
  - inversion H; subst. destruct (n=?x) eqn:Heq.
    (* Value exists *)
    + assumption.
    (* Value does not exist *)
    + destruct (n<?x) eqn:Hneq.
      (* Insert left *)
      * constructor; try easy.
        -- rewrite Nat.ltb_lt in Hneq. eapply smaller_insert; try easy.
        -- apply IHt2; assumption.
      (* Insert right *)
      * constructor; try easy.
        -- rewrite Nat.ltb_nlt in Hneq. assert (x < n) by (apply Nat.eqb_neq in Heq; lia). eapply greater_insert; try easy.
        -- apply IHt1; assumption.
Qed.

(* Exercise 3.9 *)
Lemma insert_correct :
  forall t x y,
    sorted t ->
    elem_of y (insert x t)
    = orb (elem_of y t) (Nat.eqb x y).
Proof.
  induction t; simpl; intros.
  - destruct (x=?y) eqn:Heq.
    + reflexivity.
    + destruct (y<?x); reflexivity.
  - inversion H; subst. 
    destruct (n=?x) eqn:Heq.
    + rewrite Nat.eqb_eq in Heq. subst. simpl.
      destruct (x=?y).
      * reflexivity.
      * rewrite orb_false_r. reflexivity.
    + destruct (n<?x) eqn:Hneq.
      * simpl. destruct (n=?y) eqn:Heqny.
        -- reflexivity.
        -- destruct (y<?n) eqn:Hyn.
            (* Skal bruge Hyn for at finde at y < n < x -> y < x*)
          --- rewrite Nat.ltb_lt in Hyn. rewrite Nat.ltb_lt in Hneq. assert (x <> y) by lia. Search (_<>_). apply Nat.eqb_neq in H0. rewrite H0. Search (_||_). rewrite Bool.orb_false_r. reflexivity.
          --- apply IHt2. assumption.
      * simpl. destruct (n=?y).
        -- reflexivity.
        -- destruct (y<?n) eqn:Hyn.
          --- apply IHt1. assumption.
          --- rewrite Nat.ltb_nlt in Hyn, Hneq. assert (x <> y) by (apply Nat.eqb_neq in Heq; lia). apply Nat.eqb_neq in H0. rewrite H0. rewrite Bool.orb_false_r. reflexivity.
Qed.
  

