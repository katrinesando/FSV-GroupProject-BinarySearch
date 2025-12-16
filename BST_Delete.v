Require Import BstProject.BST.
Require Import BstProject.project_lib.
Require Import Lia.

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
      (*delete happens here*)
      match l,r with
      | leaf, _ => r
      | _, leaf => l
      | _,_ => 
        match successor r with
        | Some v' => node l v' (delete v' r)
        | None => leaf (*Impossible*)
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

(* Lemmas to help prove sorted*)
Lemma greater_lift :
  forall v m t,
    greater v t ->
    v < m ->
    greater m t.
Proof.
  induction t; simpl; intros Hg Hlt.
  - constructor.
  - inversion Hg; subst.
    constructor; eauto. lia.
Qed.

Lemma smaller_lift_right :
  forall m v t,
    m < v ->
    smaller v t ->
    smaller m t.
Proof.
  induction t; intros Hlt Hsm; simpl.
  - constructor.
  - inversion Hsm; subst.
    constructor; eauto. lia.
Qed.

Lemma successor_min_greater_than_parent :
  forall v r m,
    smaller v r ->
    successor r = Some m ->
    v < m.
Proof.
  induction r; intros m Hsm Hsucc; simpl in *; try discriminate.
  inversion Hsm; subst.
  destruct r1; eauto.
  injection Hsucc as <-. assumption.
Qed.

Lemma successor_from_left_lt_parent :
  forall l v m,
    greater v l ->
    successor l = Some m ->
    m < v.
Proof.
  induction l; intros v m Hgt Hsucc; simpl in *; try discriminate.
  inversion Hgt; subst.
  destruct l1; eauto.
  injection Hsucc as <-. assumption.
Qed.

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
  eapply greater_lift; eauto.
  eapply successor_min_greater_than_parent; eauto.
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
  destruct t1; eauto.
  injection Hsucc as <-. assumption.
Qed.

Lemma smaller_than_successor :
  forall n t m,
    smaller n t ->
    successor t = Some m ->
    n < m.
Proof.
  induction t; intros m Hgt Hsucc; simpl in *; try discriminate.
  inversion Hgt; subst.
  destruct t1; eauto.
  injection Hsucc as <-. assumption.
Qed.

(* Create hint databases for BST properties *)
Hint Resolve greater_lift smaller_lift_right : core.
Hint Resolve successor_min_greater_than_parent successor_from_left_lt_parent : core.
Hint Resolve greater_than_successor smaller_than_successor : core.
Hint Resolve successor_greater_than_left : core.

(* Delete preserves 'smaller' when we delete ANY x (except root collapse case is handled by pattern) *)
Lemma smaller_delete :
  forall n x t,
    smaller n t ->
    smaller n (delete x t).
Proof.
  intros n x t.
  generalize dependent x.
  induction t; intros; simpl; try assumption.
  - inversion H; subst.
    destruct (n0 =? x) eqn:Heq.
    + (* deleting root *)
      destruct t1, t2; simpl; try assumption. 
      destruct (successor (node t2_1 n2 t2_2)) eqn:Hsucc.
      * destruct t2_1; simpl in *; eauto.
        simpl in Hsucc. rewrite Hsucc. constructor; eauto.
      * (* no successor: impossible *)
        destruct t2_1; simpl; simpl in *; eauto.
        ++ destruct t2_1_1; eauto.
           simpl in *. rewrite Hsucc. eauto.
    + destruct (x <? n0) eqn:Hlt; eauto.
Qed.

Lemma greater_delete :
  forall n x t,
    greater n t ->
    greater n (delete x t).
Proof.
  intros n x t.
  generalize dependent x.
  induction t; intros x H; simpl; try assumption.
  inversion H; subst.
  destruct (n0 =? x) eqn:Heq.
  - (* deleting root *)
     destruct t1, t2; simpl; try assumption. 
     destruct (successor (node t2_1 n2 t2_2)) eqn:Hsucc.
     + (* successor found *)
        destruct t2_1; simpl in *; eauto.
        simpl in Hsucc. rewrite Hsucc. constructor; eauto. 
     + (* no successor: impossible *)
        destruct t2_1; simpl; simpl in *; eauto. 
        destruct t2_1_1; eauto.
        simpl in *. rewrite Hsucc. eauto.
  - (* not deleting root *)
      destruct (x <? n0) eqn:Hlt; eauto.
Qed.

Lemma successor_smaller_right_after_delete :
  forall r m,
    sorted r ->
    successor r = Some m ->
    smaller m (delete m r).
Proof.
  intros r m Hsort Hsucc.
  revert m Hsucc Hsort.
  induction r; intros; simpl in *; try discriminate.
  inversion Hsort; subst.
  destruct r1.
  - (* right subtree root is the successor, delete removes it and returns r2 *)
     simpl. inversion Hsucc; subst. simpl. rewrite Nat.eqb_refl. assumption.
  - (* successor comes from the left subtree *)
    simpl in Hsucc; eauto.
    assert (n > m) by (eapply greater_than_successor; eauto).
    assert (m < n) by lia.
    destruct (n =? m) eqn:Heq.
    +  apply Nat.eqb_eq in Heq; subst. lia.
    +  assert (m <? n = true) as Hlt by (apply Nat.ltb_lt; lia).
      rewrite Hlt; simpl.
      constructor; try eauto.
Qed.

Hint Resolve smaller_delete greater_delete : core.
Hint Resolve successor_smaller_right_after_delete : core.

Lemma delete_sorted :
  forall t x, sorted t -> sorted (delete x t).
Proof.
  induction t; intros x Hs; simpl.
  - assumption.
  - inversion Hs; subst.
    destruct (n =? x) eqn:Heq.
    + (* deleting root *)
      destruct t1; try assumption.
      * destruct t2; try assumption.
        -- (* two children *)
           destruct (successor (node t2_1 n1 t2_2)) eqn:Hsucc; eauto.
    + (* not deleting root *)
      destruct (x <? n) eqn:Hlt; constructor; eauto.
Qed.

Lemma smaller_elem_false :
  forall n t, smaller n t -> elem_of n t = false.
Proof.
  induction t; simpl; intros Hsm.
  - reflexivity.
  - inversion Hsm; subst; clear Hsm.
    destruct (n0 =? n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + destruct (n <? n0) eqn:Hlt; eauto.
Qed.

Lemma greater_elem_false :
  forall n t, greater n t -> elem_of n t = false.
Proof.
  induction t; simpl; intros Hgt.
  - reflexivity.
  - inversion Hgt; subst; clear Hgt.
    destruct (n0 =? n) eqn:Heq. 
    + apply Nat.eqb_eq in Heq. lia.
    + destruct (n <? n0) eqn:Hlt; eauto.
Qed.

Hint Resolve smaller_elem_false greater_elem_false : core.

Theorem delete_correct :
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
      destruct t1; eauto.
      destruct t2; eauto.
      * destruct (successor (node t2_1 n0 t2_2)) eqn:Hsucc; eauto.
        simpl. 
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
        rewrite H6. eauto.
    + destruct (x <? n) eqn:Hnx0; simpl; rewrite Hnx; rewrite Hnx0; try apply IHt1; try apply IHt2; assumption.
Qed.
  

