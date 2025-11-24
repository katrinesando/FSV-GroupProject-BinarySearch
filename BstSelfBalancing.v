Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Lia.


Inductive color : Type :=
| Black | Red.

Inductive rb_tree :=
| leaf : rb_tree
| node : color -> rb_tree -> nat -> rb_tree -> rb_tree.

(* 
(* Root is always black - all leafs are black *)
Definition rb_tree1 := correct rb tree
Definition rb_tree2 := not correct tree 
*)
(* Helper functions *)
Inductive greater :  nat -> rb_tree -> Prop :=
|leaf_greater : forall n, greater n leaf
|node_greater : forall n c l v r, 
    n > v ->
    greater n l ->
    greater n r ->
    greater n (node c l v r)
.
Inductive smaller  : nat -> rb_tree -> Prop :=
|leaf_smaller : forall n, smaller n leaf
|node_smaller : forall n c l v r, 
    n < v ->
    smaller n l ->
    smaller n r ->
    smaller n (node c l v r)
.

Inductive rb_sorted : rb_tree -> Prop :=
| leaf_sorted : rb_sorted leaf
| node_sorted : forall c l v r,
    greater v l ->
    smaller v r ->
    rb_sorted l ->
    rb_sorted r ->
    rb_sorted (node c l v r)
.
Hint Constructors rb_sorted : core.
Hint Constructors smaller : core. 
Hint Constructors greater : core. 

Fixpoint rb_elem_of (x: nat) (t:rb_tree) : bool :=
  match t with
  | leaf => false
  | node c l v r => 
    (v =? x) || 
    (if x <? v then rb_elem_of x l else rb_elem_of x r)
  end.


Definition balance (t: rb_tree) : rb_tree :=
match t with
| node c l v r =>
  match c, v, l, r with
  | Black, v, (node Red (node Red a x b) y c), r =>
      node Red (node Black a x b) y (node Black c v r)
  | Black, v, (node Red a x (node Red b y c)), r =>
      node Red (node Black a x b) y (node Black c v r)
  | Black, x, a, (node Red (node Red b y c) v r) =>
      node Red (node Black a x b) y (node Black c v r)
  | Black, x, a, (node Red b y (node Red c v r)) =>
    node Red (node Black a x b) y (node Black c v r)
  | _, _, _, _ => t
  end
| _ => t
end.

Fixpoint rb_insert_aux (x : nat) (t : rb_tree) : rb_tree :=
match t with
| leaf  => node Red leaf x leaf
| node c l v r => 
  if v =? x then
  t
  else if v <? x then
  balance (node c l v (rb_insert_aux x r))
  else
  balance (node c (rb_insert_aux x l) v r)
end.

Definition rb_insert (x:nat) (t:rb_tree) : rb_tree :=
match rb_insert_aux x t with
| node _ l v r => node Black l v r
| leaf => (*Guaranteed to not be the case*) leaf
end.

Definition tree1 :=
  node Black 
  (node Red leaf 5 leaf) 
  10 
  (node Red leaf 15 leaf).
Definition tree_complex :=
  node Black (node Red (node Black leaf 1 leaf) 2 (node Black leaf 3 leaf))
  4
  (node Red (node Black leaf 5 leaf) 
    6 
    (node Black leaf 8 (node Red leaf 9 leaf))).

Example simple_insert : rb_insert 2 tree1 =
  node Black (node Black leaf 2 leaf) 
  5
  (node Black leaf 10 (node Red leaf 15 leaf)).
Proof. unfold tree1. unfold rb_insert. simpl. reflexivity. Qed.

Example complex_insert : rb_insert 7 tree_complex =
  node Black (node Red (node Black leaf 1 leaf) 2 (node Black leaf 3 leaf))
  4
  (node Red (node Black leaf 5 leaf) 
    6 
    (node Black (node Red leaf 7 leaf) 8 (node Red leaf 9 leaf))).
Proof. unfold tree1. unfold rb_insert. simpl. reflexivity. Qed.

(* Prove rb insert is correct *)
Inductive no_red_red : rb_tree -> Prop :=
| nr_leaf : no_red_red leaf
| nr_node_black : 
    forall v l r,
    no_red_red l -> no_red_red r -> no_red_red (node Black l v r)
| nr_node_red : forall l v r,
    (* children must be black nodes or leaf *)
    (match l with node Red _ _ _ => False | _ => True end) ->
    (match r with node Red _ _ _ => False | _ => True end) ->
    no_red_red l -> no_red_red r -> no_red_red (node Red l v r).

  (* black-height: compute black-height and require uniformity *)
Search(eqb).
Definition color_eqb (c: color) : nat :=
  match c with
  | Black => 1
  | Red => 0
  end.

Fixpoint black_height (t: rb_tree) : option nat :=
  match t with
  | leaf => Some 0
  | node c l v r =>
     match black_height l, black_height r with
     | Some hl, Some hr =>
         if Nat.eqb hl hr then
           Some (hl + color_eqb c)(* compare colors via eqb on constructors using a helper if needed *)
         else None
     | _, _ => None
     end
  end.

Definition rb_invariant (t: rb_tree) : Prop :=
  rb_sorted t /\ no_red_red t /\ exists k, black_height t = Some k.

(* Lemma skeletons to prove *)
Lemma balance_preserves_sorted :
  forall t, rb_sorted t -> rb_sorted (balance t).
Admitted.

Lemma balance_preserves_no_red_red :
  forall t, no_red_red t -> no_red_red (balance t).
Admitted.

Lemma balance_preserves_bh :
  forall t k, black_height t = Some k -> black_height (balance t) = Some k.
Admitted.

Lemma rb_insert_aux_preserves_invariant :
  forall x t,
    rb_invariant t ->
    (* rb_insert_aux may produce red root; we show invariants hold except possibly root color *)
    rb_sorted (rb_insert_aux x t) /\ no_red_red (rb_insert_aux x t) /\
    exists k, black_height (rb_insert_aux x t) = Some k.
Admitted.

(* recolor helper lemmas *)
Lemma recolor_preserves_rb_sorted :
  forall c l v r,
    rb_sorted (node c l v r) ->
    rb_sorted (node Black l v r).
Proof.
  intros * H. inversion H; subst. constructor; assumption.
Qed.

Lemma recolor_preserves_no_red_red :
  forall c l v r,
    no_red_red (node c l v r) ->
    no_red_red (node Black l v r).
Proof.
  intros c l v r H.
  inversion H; subst; clear H.
  - (* originally leaf impossible for node *)
    eauto. admit.
  - (* originally black *)
    constructor; assumption.
Admitted.

Lemma black_height_recolor_root :
  forall c l v r k,
    black_height (node c l v r) = Some k ->
    match c with
    | Black => black_height (node Black l v r) = Some k
    | Red => black_height (node Black l v r) = Some (k + 1)
    end.
Proof.
  intros c l v r k H.
  simpl in H.
  destruct (black_height l) eqn:Hl; destruct (black_height r) eqn:Hr; try discriminate.
  destruct (Nat.eqb n n0) eqn:Heq; try discriminate.
  apply Nat.eqb_eq in Heq. subst. admit.
Admitted.
  (* destruct c; simpl in *; now rewrite Hl, Hr. *)

Lemma rb_insert_aux_never_leaf : forall x t, rb_insert_aux x t <> leaf.
Proof.
  intros x t. destruct t.
  - simpl. discriminate.
  - simpl. destruct (n =? x); [discriminate|].
    destruct (n <? x); simpl; admit.
    (* + unfold balance; destruct c; destruct l; destruct r; simpl; discriminate.
    + unfold balance; destruct c; destruct l; destruct r; simpl; discriminate. *)
Admitted.
(* Final theorem: recoloring root to Black preserves invariants and gives rb_invariant *)
Theorem rb_insert_correct : forall x t,
  rb_invariant t ->
  rb_invariant (rb_insert x t).
Proof.
  intros x t [Hsorted [Hnored [k Hbh]]].
  unfold rb_insert.
  pose proof (rb_insert_aux_preserves_invariant x t) as Haux.
  remember (rb_insert_aux x t) as t'.
  destruct t' as [ | c l v r ] eqn:E.
  - (* impossible by lemma *)
    exfalso. apply (rb_insert_aux_never_leaf x t). symmetry. assumption.
  -  
    destruct Haux as [Hsorted' [Hnored' Hbh']].
    constructor.
    +  (* sortedness preserved *)
      eauto.
    + split.
      *  (* no-red-red preserved *)
        eauto.
      *  (* black-height preserved *)
        exists k. assumption.
    + (* recolor to Black preserves invariants *)
      pose proof (recolor_preserves_rb_sorted c l v r Hsorted') as Hsorted_black.
      pose proof (recolor_preserves_no_red_red c l v r Hnored') as Hnored_black.
      destruct Hbh' as [k' Hbh'].
      destruct c.
    * specialize (black_height_recolor_root Black l v r k' Hbh') as Hbh_recolored.
      simpl in Hbh_recolored.
      split; [ exact Hsorted_black | ].
      split; [ exact Hnored_black | ].
      exists k'. exact Hbh_recolored.
    * specialize (black_height_recolor_root Red l v r k' Hbh') as Hbh_recolored.
      simpl in Hbh_recolored.
      split; [ exact Hsorted_black | ].
      split; [ exact Hnored_black | ].
      exists (k' + 1). exact Hbh_recolored.
Qed.