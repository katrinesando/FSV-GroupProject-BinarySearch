Require Import BstProject.BST.
Require Import BstProject.project_lib.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Lia.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Transparent BST.insert.

(* bst to list *)
Fixpoint bst_to_list (bst: tree) : list nat :=
  match bst with
  | leaf => []
  | node l v r => [v] ++ bst_to_list l ++ bst_to_list r
end.

(* Definition list_to_bst (lst: list nat) : tree :=
  fold_left(fun acc elem => insert elem acc) lst leaf. *)

Fixpoint list_to_bst (l : list nat) : tree :=
  match l with
  | [] => leaf
  | x :: xs => insert x (list_to_bst xs)
  end.

Example bst_lst : bst_to_list tree1 = [10;5;2;7;16;12;17]. (*[2;5;7;10;12;16;17].*)
Proof. unfold bst_to_list. simpl. reflexivity. Qed.

Example lst_bst : list_to_bst [12;17;16;2;7;5;10] =  tree1. (* [10;5;7;2;16;17;12] *)
Proof. unfold list_to_bst. unfold tree1. simpl. reflexivity. Qed.


Ltac solve_by_IH :=
  match goal with
  | [ H : _ |- _ ] => solve [ apply H; assumption ]
  end.


Lemma smaller_list : forall n t x, 
  smaller n t -> In x (bst_to_list t) -> n < x.
Proof.
  induction t; simpl; intros.
  - inversion H0.
  - inversion H; subst.
    destruct H0.
    + subst. assumption.
    + apply in_app_or in H0. destruct H0 as [H_left | H_right]; solve_by_IH.
Qed.

Lemma greater_list : forall n t x, 
  greater n t -> In x (bst_to_list t) -> x < n.
Proof.
  induction t; simpl; intros.
  - inversion H0.
  - inversion H; subst.
    destruct H0.
    + subst. assumption.
    + apply in_app_or in H0. destruct H0 as [H_left | H_right]; solve_by_IH.
Qed.

Lemma bst_to_list_correct : forall t n,
  sorted t ->
  elem_of n t = true <-> In n (bst_to_list t).
Proof.
  induction t; simpl. intros n H_sort.
  - (* Leaf *) intuition. 
  - (* Node *) intros n0 H_sort. inversion H_sort; subst.
    destruct (n=?n0) eqn:Heq.
    + (* Equal *) rewrite Nat.eqb_eq in Heq; intuition. 
    + (*Inequality*) destruct (n0 <? n) eqn:Hlt.
      * (* Right subtree *) rewrite IHt1; try assumption.
        split; intros H.
        -- right. apply in_or_app. left. assumption.
        -- destruct H as [Heq' | H].
          --- subst. rewrite Nat.eqb_refl in Heq. inversion Heq.
          --- apply in_app_or in H. destruct H as [H_left | H_right].
            ---- assumption.
            ---- eapply smaller_list in H_right; [| exact H3]. rewrite Nat.ltb_lt in Hlt. lia.          
            
      * (* Left subtree *) rewrite IHt2; try assumption.
        split; intros H.
        -- right. apply in_or_app. right. assumption.
        -- destruct H as [Heq' | H].
          --- subst. rewrite Nat.eqb_refl in Heq. inversion Heq.
          --- apply in_app_or in H. destruct H as [H_left | H_right].
            ---- eapply greater_list in H_left; [| exact H2]. rewrite Nat.ltb_ge in Hlt. lia.
            ---- assumption.
Qed.

Lemma list_to_bst_sorted : forall l, sorted (list_to_bst l).
Proof.
  induction l; simpl.
  - constructor. (* leaf is sorted *)
  - apply insert_sorted. assumption.
Qed.

Lemma list_to_bst_correct : forall l x,
  elem_of x (list_to_bst l) = true <-> In x l.
Proof.
  induction l; intros.
  - simpl. split; intros; inversion H.
  - simpl. rewrite insert_correct; try apply list_to_bst_sorted.
    rewrite orb_true_iff. rewrite IHl.
    rewrite Nat.eqb_eq. 
    split; intros; rewrite or_comm; assumption.
Qed.


Definition same_elements (t1 t2 : tree) : Prop :=
  forall x, elem_of x t1 = elem_of x t2.

Theorem bst_list_bst_same :
  forall t t' l n,
  sorted t ->
  bst_to_list t = l ->
  list_to_bst l = t' ->
  elem_of n t = elem_of n t'.
Proof.
  intros.
  subst.
  destruct (elem_of n t) eqn:H_n_in_t;
  destruct (elem_of n (list_to_bst (bst_to_list t))) eqn:H_n_in_new; try reflexivity.
  - apply bst_to_list_correct in H_n_in_t; try assumption.
    rewrite <- list_to_bst_correct in H_n_in_t.
    rewrite <- H_n_in_t; rewrite <- H_n_in_new. reflexivity.
  - apply list_to_bst_correct in H_n_in_new.
    rewrite <- bst_to_list_correct in H_n_in_new; try assumption.
    rewrite <- H_n_in_t; rewrite <- H_n_in_new. reflexivity.
Qed. 
  
(* Exercise 3.10*)
(* Find smallest value in right subtree -> expects to get right subtree *)
Fixpoint successor (t:tree) : option nat :=
  match t with 
  | leaf => None
  | node leaf v _ => Some v 
  | node l _ _  => successor l
end.

Fixpoint delete (x : nat) (t : tree) : tree :=
  match t with
  | leaf => leaf
  | node l v r =>
    if v =? x then
      match l,r with
      | leaf, _ => r
      | _, leaf => l
      | _,_ => 
        match successor r with
        | Some v' => node l v' (delete v' r)
        | None => leaf (* Impossible *)
        end
      end
    else if x <? v then
      node (delete x l) v r
    else
      node l v (delete x r)
end.

Example delete_one_child : delete 5 (node (node (node leaf 2 leaf ) 5 leaf) 10 leaf) = node (node leaf 2 leaf ) 10 leaf.
Proof. unfold delete. reflexivity. Qed.

Example delete_no_children : delete 2 (node (node (node leaf 2 leaf ) 5 leaf) 10 leaf) = node (node leaf 5 leaf ) 10 leaf.
Proof. unfold delete. reflexivity. Qed.

Example delete_two_children : delete 5 tree1 =   
      node (node (node leaf 2 leaf) 7 leaf)
       10 (* root *)
      (node (node leaf 12 leaf) 16 (node leaf 17 leaf)).
Proof. unfold delete. simpl. reflexivity. Qed.

Example delete_root : delete 10 tree1 =
  node (node (node leaf 2 leaf) 5 (node leaf 7 leaf))
  12 (* new root *)
  (node leaf 16 (node leaf 17 leaf)).
Proof. unfold delete. reflexivity. Qed.


Ltac solve_lift :=
  simpl; intros;
  try constructor;
  match goal with
  | [ H : greater _ (node _ _ _) |- _ ] => inversion H; subst
  | [ H : smaller _ (node _ _ _) |- _ ] => inversion H; subst
  end;
  try constructor; 
  try lia; 
  match goal with
  | [ IH : forall _, _ -> _ |- _ ] => apply IH; assumption
  end.

(* Lemmas to help prove sorted*)
(* If a value is greater than all elements of a tree, and we increase the
   value, it stays greater than all elements. *)
Lemma greater_lift :
  forall v m t,
    greater v t ->
    v < m ->
    greater m t.
Proof.
  induction t;
  solve_lift.
Qed.

Lemma smaller_lift_right :
  forall m v t,
    m < v ->
    smaller v t ->
    smaller m t.
Proof.
  induction t; 
  solve_lift.
Qed.

(* If the parent ensures all elements of r are > v (smaller v r), then the
   leftmost/successor element of r is strictly greater than v. *)
Lemma successor_min_greater_than_parent :
  forall v r m,
    smaller v r ->
    successor r = Some m ->
    v < m.
Proof.
  induction r; intros m Hsm Hsucc; simpl in *; try discriminate.
  inversion Hsm; subst.
  destruct r1.
  - (* left = leaf: successor is the root of this node *)
    injection Hsucc as <-. assumption.
  - (* successor is in the left subtree *)
    simpl in Hsucc. eapply IHr1; eauto.
Qed.

(* If the successor comes from a left subtree, it is strictly less than the
   parent value (all elements of the left subtree are < parent). *)
Lemma successor_from_left_lt_parent :
  forall l v m,
    greater v l ->
    successor l = Some m ->
    m < v.
Proof.
  induction l; intros v m Hgt Hsucc; simpl in *; try discriminate.
  inversion Hgt; subst.
  destruct l1.
  - injection Hsucc as <-. assumption.
  - eapply IHl1; eauto.
Qed.

Hint Resolve successor_min_greater_than_parent : core.
Hint Resolve greater_lift : core.
Hint Resolve smaller_lift_right : core.
Hint Resolve successor_from_left_lt_parent : core.

(* Minimum value property in right subtree *)
(* The successor is a minimal element of the tree: every element of the tree
   is >= the successor. We state this using [elem_of] for membership. This is
   the correct non-strict property (the strict version `smaller m r` is false
   when the successor equals the root value). *)
 
Lemma delete_unfold_node (x v : nat) (l r : tree) :
  delete x (node l v r) =
    if v =? x then
      match l, r with
      | leaf, _ => r
      | _, leaf => l
      | _, _ =>
          match successor r with
          | Some v' => node l v' (delete v' r)
          | None => leaf
          end
      end
    else if x <? v then node (delete x l) v r
    else node l v (delete x r).
Proof. reflexivity. Qed.

(* Successor greater than all left subtree of original node *)
Lemma successor_greater_than_left :
  forall l v r m,
    sorted (node l v r) ->
    successor r = Some m ->
    greater m l.
Proof.
  intros l v r m Hsrt Hsucc.
  inversion Hsrt; subst.
  (* lift greater v l to greater m l using v < m from the successor of r *)
  eauto.
Qed.

(* Helper: if n > all elements of t, then n > successor of t *)
Lemma greater_than_successor :
  forall n t m,
    greater n t ->
    successor t = Some m ->
    n > m.
Proof.
  induction t; intros m Hgt Hsucc; simpl in *; try discriminate.
  inversion Hgt; subst.
  eauto.
Qed.

Lemma smaller_than_successor :
  forall n t m,
    smaller n t ->
    successor t = Some m ->
    n < m.
Proof.
  induction t; intros m Hgt Hsucc; simpl in *; try discriminate.
  inversion Hgt; subst.
  eauto.
Qed.

Hint Resolve successor_greater_than_left : core.
Hint Resolve greater_than_successor : core.
Hint Resolve smaller_than_successor : core.

(* Delete preserves 'smaller' when we delete ANY x (except root collapse case is handled by pattern) *)
Lemma smaller_delete :
  forall n x t,
    smaller n t ->
    smaller n (delete x t).
Proof.
  intros n x t.
  generalize dependent x.
  induction t; intros; simpl.
  - assumption.
  - inversion H; subst.
    destruct (n0 =? x) eqn:Heq.
    + (* deleting root *)
      destruct t1, t2; simpl; try assumption. 
      destruct (successor (node t2_1 n2 t2_2)) eqn:Hsucc.
      * (* successor found: n3 *)
        destruct t2_1; simpl in *.
        -- eauto. (* t2_1 = leaf, so successor is n2 *)
        -- (* t2_1 = node, successor from left subtree *)
            simpl in Hsucc. rewrite Hsucc. eauto.
      *  (* no successor: impossible *)
        destruct t2_1; simpl; simpl in *. 
        ++ discriminate Hsucc.
        ++ destruct t2_1_1.
          --- inversion Hsucc; subst.
          --- simpl in *. rewrite Hsucc. eauto.
    + (* not deleting root *)
      destruct (x <? n0) eqn:Hlt; eauto.
      
Qed.

Lemma greater_delete :
  forall n x t,
    greater n t ->
    greater n (delete x t).
Proof.
  (* Generalize [n] and [x] so the IHs can be instantiated with the
     successor value when the recursive delete removes a different key. *)
  intros n x t.
  generalize dependent x.
  induction t; intros x H; simpl.
  - assumption.
  - inversion H; subst.
    destruct (n0 =? x) eqn:Heq.
    + (* deleting root *)
      destruct t1, t2; simpl; try assumption. 
      destruct (successor (node t2_1 n2 t2_2)) eqn:Hsucc.
      * (* successor found: n3 *)
        destruct t2_1; simpl in *.
        -- eauto.
        --(* t2_1 = node, successor from left subtree *)
            simpl in Hsucc; rewrite Hsucc; eauto.
      * (* no successor: impossible *)
        destruct t2_1; simpl; simpl in *. 
        ++ discriminate Hsucc.
        ++ destruct t2_1_1.
          --- inversion Hsucc; subst.
          --- simpl in *. rewrite Hsucc. eauto.
    + (* not deleting root *)
      destruct (x <? n0) eqn:Hlt; eauto.
Qed.

Lemma successor_smaller_right_after_delete :
  forall r m,
    sorted r ->
    successor r = Some m ->
    smaller m (delete m r).
Proof.
  intros r m Hsort Hsucc.
  (* First: smaller m r from successor_all_right *)
  revert m Hsucc Hsort.
  induction r; intros; simpl in *; try discriminate.
  inversion Hsort; subst.
  destruct r1.
  - (* right subtree root is the successor, delete removes it and returns r2 *)
     simpl. inversion Hsucc; subst. simpl. rewrite Nat.eqb_refl. assumption.
  - (* successor comes from the left subtree *)
    simpl in Hsucc. 
    assert (n > m) by (eapply greater_than_successor; eauto).
    assert (m < n) by lia.
    destruct (n =? m) eqn:Heq.
    +  apply Nat.eqb_eq in Heq; subst. lia.
    +  assert (m <? n = true) as Hlt by (apply Nat.ltb_lt; lia).
      rewrite Hlt; eauto.
Qed.

Hint Resolve smaller_delete : core.
Hint Resolve greater_delete : core.
Hint Resolve successor_smaller_right_after_delete : core.

Lemma delete_sorted :
  forall t x, sorted t -> sorted (delete x t).
Proof.
  induction t; intros x Hs; simpl.
  - assumption.
  - inversion Hs; subst.
    destruct (n =? x) eqn:Heq.
    + (* deleting root *)
      destruct t1.
      * assumption. (* no left subtree *)
      * destruct t2.
        -- (* one-child left *) assumption.
        -- (* two children *)
           destruct (successor (node t2_1 n1 t2_2)) eqn:Hsucc; eauto.
    + (* not deleting root *)
      destruct (x <? n) eqn:Hlt; eauto.
Qed.



Lemma smaller_elem_false :
  forall n t, smaller n t -> elem_of n t = false.
Proof.
  induction t; simpl; intros Hsm.
  - reflexivity.
  - inversion Hsm; subst; clear Hsm.
    destruct (n0 =? n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + destruct (n <? n0) eqn:Hlt.
      * apply IHt1. assumption.
      * rewrite Nat.ltb_nlt in Hlt. lia.
Qed.

Lemma greater_elem_false :
  forall n t, greater n t -> elem_of n t = false.
Proof.
  induction t; simpl; intros Hgt.
  - reflexivity.
  - inversion Hgt; subst; clear Hgt.
    destruct (n0 =? n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + destruct (n <? n0) eqn:Hlt.
      * rewrite Nat.ltb_lt in Hlt; lia.
      * apply IHt2. assumption.
Qed.

Hint Resolve smaller_elem_false : core.
Hint Resolve greater_elem_false : core.


Lemma delete_correct :
forall t x,
    sorted t ->
    elem_of x t = true -> 
    (elem_of x (delete x t)) = false.
Proof.
  induction t; simpl; intros x Hs He.
  - lia.
  - inversion Hs; subst. 
    destruct (n =? x) eqn:Hnx.
    + rewrite Nat.eqb_eq in Hnx; subst.
      destruct t1.
      * apply smaller_elem_false. assumption.
      * destruct t2.
        -- eauto. (*  apply greater_elem_false. assumption. *)
        -- destruct (successor (node t2_1 n0 t2_2)) eqn:Hsucc.
          ++ simpl. 
              assert (x < n1).
              { eapply successor_min_greater_than_parent; eauto. }
              assert ((n1 =? x = false)).
              { apply Nat.eqb_neq. intros E. lia. }
              rewrite H0. rewrite <- Nat.ltb_lt in H. rewrite H.
              inversion H2; subst.
              assert ((x =? n) = false).
              { apply Nat.eqb_neq. intro E. lia. }
              rewrite Nat.eqb_sym.
              rewrite H1.
              assert ((x <? n) = false).
              { apply Nat.ltb_ge. lia. }
              rewrite H6.
              apply greater_elem_false. assumption.
          ++ auto.
    + destruct (x <? n) eqn:Hnx0; simpl; rewrite Hnx; rewrite Hnx0; try apply IHt1; try apply IHt2; assumption.
Qed.

(* 580 -> 500*)