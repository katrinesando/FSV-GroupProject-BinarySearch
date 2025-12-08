Require Import BstProject.BST.
Require Import BstProject.project_lib.
Require Import Lia.

Fixpoint bst_to_list (bst: tree) : list nat :=
  match bst with
  | leaf => []
  | node l v r => [v] ++ bst_to_list l ++ bst_to_list r
end.

(* 
  VV Tail recursive definition which made proving hard VV

  Definition list_to_bst (lst: list nat) : tree :=
  fold_right(fun elem acc => insert elem acc) leaf lst.
 *)
 
Fixpoint list_to_bst (l : list nat) : tree :=
  match l with
  | [] => leaf
  | x :: xs => insert x (list_to_bst xs)
  end.

Example bst_lst : bst_to_list tree1 = [10;5;2;7;16;12;17].
Proof. unfold bst_to_list. simpl. reflexivity. Qed.

Example lst_bst : list_to_bst [12;17;16;2;7;5;10] =  tree1.
Proof. unfold list_to_bst. unfold tree1. simpl. reflexivity. Qed.

Lemma smaller_list : forall n t x, 
  smaller n t -> In x (bst_to_list t) -> n < x.
Proof.
  induction t; simpl; intros.
  - inversion H0.
  - inversion H; subst.
    destruct H0.
    + subst. assumption.
    + apply in_app_or in H0. destruct H0 as [H_left | H_right].
      * apply IHt1; assumption.
      * apply IHt2; assumption.
Qed.


Lemma greater_list : forall n t x, 
  greater n t -> In x (bst_to_list t) -> x < n.
Proof.
  induction t; simpl; intros.
  - inversion H0.
  - inversion H; subst.
    destruct H0.
    + subst. assumption.
    + apply in_app_or in H0. destruct H0 as [H_left | H_right].
      * apply IHt1; assumption.
      * apply IHt2; assumption.
Qed.

Lemma bst_to_list_correct : forall t n,
  sorted t ->
  elem_of n t = true <-> In n (bst_to_list t).
Proof.
  induction t; simpl. intros n H_sort.
  - (* Leaf *) auto with *. 
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
  destruct (elem_of n (list_to_bst (bst_to_list t))) eqn:H_n_in_new.
  - reflexivity.
  - apply bst_to_list_correct in H_n_in_t; try assumption.
    rewrite <- list_to_bst_correct in H_n_in_t.
    rewrite <- H_n_in_t; rewrite <- H_n_in_new. reflexivity.
  - apply list_to_bst_correct in H_n_in_new.
    rewrite <- bst_to_list_correct in H_n_in_new; try assumption.
    rewrite <- H_n_in_t; rewrite <- H_n_in_new. reflexivity.
  - reflexivity.
Qed. 