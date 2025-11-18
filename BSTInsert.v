Require Import BstProject.BST.
Require Import BstProject.project_lib.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Lia.
Transparent BST.insert.

(* bst to list *)
Fixpoint bst_to_list (bst: tree) : list nat :=
  match bst with
  | leaf => []
  | node l v r => bst_to_list l ++ [v] ++ bst_to_list r
end.

Definition list_to_bst (lst: list nat) : tree :=
  fold_left(fun acc elem => insert elem acc) lst leaf.

Example bst_lst : bst_to_list tree1 = [2;5;7;10;12;16;17].
Proof. unfold bst_to_list. reflexivity. Qed.

Example lst_bst : list_to_bst [10;5;7;2;16;17;12] =  tree1.
Proof. unfold list_to_bst. reflexivity. Qed.

(*Useful Theorems *)
(* Theorem bst_list_sorted : list -> bst -> list - skulle give sorted list ud
forall t1 t2, 
bst_to_list t1 = bst_to_list t2
*)

(* Size of list equals size of tree *)

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
        | None => leaf (*Impossible -> TODO: make option (None)*)
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
(* If a value is greater than all elements of a tree, and we increase the
   value, it stays greater than all elements. *)
Lemma greater_lift :
  forall v m t,
    greater v t ->
    v < m ->
    greater m t.
Proof.
  induction t; simpl; intros Hg Hlt.
  - constructor.
  - inversion Hg; subst.
    constructor.
    + lia.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
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
    constructor.
    + lia.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
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
  eapply greater_lift.
  - eauto.
  - eapply successor_min_greater_than_parent; eauto.
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
  destruct t1.
  - (* successor is the root *)
    injection Hsucc as <-. assumption.
  - (* successor in left subtree *)
    eapply IHt1; eauto.
Qed.

Lemma smaller_than_successor :
  forall n t m,
    smaller n t ->
    successor t = Some m ->
    n < m.
Proof.
  induction t; intros m Hgt Hsucc; simpl in *; try discriminate.
  inversion Hgt; subst.
  destruct t1.
  - (* successor is the root *)
    injection Hsucc as <-. assumption.
  - (* successor in left subtree *)
    eapply IHt1; eauto.
Qed.

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
        -- (* t2_1 = leaf, so successor is n2 *)
           injection Hsucc as <-. simpl.
           constructor.
           ++ (* n > n2 *)
              eapply smaller_than_successor; eauto.
           ++ (* greater n left *)
              assumption.
           ++ (* greater n t2_2 *)
              inversion H6; subst. 
              rewrite (Nat.eqb_refl n2). eauto.
        -- (* t2_1 = node, successor from left subtree *)
            simpl in Hsucc. rewrite Hsucc. constructor. 
           ++ (* n > n3 *)
              eapply smaller_than_successor; eauto.
           ++ (* greater n left *)
              assumption.
           ++ (* greater n (delete n3 right) *)
           eapply IHt2. eauto.
      * (* no successor: impossible *)
        destruct t2_1; simpl; simpl in *. 
        ++ discriminate Hsucc.
        ++ destruct t2_1_1.
          --- inversion Hsucc; subst.
          --- simpl in *. rewrite Hsucc. eauto.
    + (* not deleting root *)
      destruct (x <? n0) eqn:Hlt.
      * constructor; try assumption; apply IHt1; assumption.
      * constructor; try assumption; apply IHt2; assumption.
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
        -- (* t2_1 = leaf, so successor is n2 *)
           injection Hsucc as <-. simpl.
           constructor.
           ++ (* n > n2 *)
              eapply greater_than_successor; eauto.
           ++ (* greater n left *)
              assumption.
           ++ (* greater n t2_2 *)
              inversion H6; subst. 
              rewrite (Nat.eqb_refl n2). eauto.
        -- (* t2_1 = node, successor from left subtree *)
            simpl in Hsucc. rewrite Hsucc. constructor. 
           ++ (* n > n3 *)
              eapply greater_than_successor; eauto.
           ++ (* greater n left *)
              assumption.
           ++ (* greater n (delete n3 right) *)
           eapply IHt2. eauto.
      * (* no successor: impossible *)
        destruct t2_1; simpl; simpl in *. 
        ++ discriminate Hsucc.
        ++ destruct t2_1_1.
          --- inversion Hsucc; subst.
          --- simpl in *. rewrite Hsucc. eauto.
    + (* not deleting root *)
      destruct (x <? n0) eqn:Hlt.
      * constructor; try assumption; apply IHt1; assumption.
      * constructor; try assumption; apply IHt2; assumption.
Qed.

Lemma successor_smaller_right_after_delete :
  forall r m,
    sorted r ->
    successor r = Some m ->
    smaller m (delete m r).
Proof.
  intros r m Hsort Hsucc.
  (*
  (* First: smaller m r from successor_all_right *)
  apply smaller_delete.
  eapply successor_all_right; eauto. *)
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
      rewrite Hlt; simpl.
      constructor; try eauto.
      * eapply smaller_lift_right; try eauto.
Qed.

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
           destruct (successor (node t2_1 n1 t2_2)) eqn:Hsucc.
           ++ (* successor found *)
              simpl.
              constructor.
              ** (* greater n0 t1 *)
                 eapply successor_greater_than_left; eauto.
              ** (* smaller n0 (delete n0 right) *) 
              rewrite Nat.eqb_eq in Heq; subst. 
              rewrite <- (delete_unfold_node n2 n1 t2_1 t2_2).
              eapply successor_smaller_right_after_delete; eauto.
              ** (* sorted left *) assumption.
              ** (* sorted right after delete *) eapply IHt2; assumption.
           ++ (* No successor: impossible since right has at least root *)
              simpl in Hsucc; eauto.
    + (* not deleting root *)
      destruct (x <? n) eqn:Hlt.
      * (* delete in left *)
        constructor; try assumption.
        -- eapply greater_delete; eauto.
        -- eapply IHt1; assumption.
      * (* delete in right *)
        constructor; try assumption.
        -- eapply smaller_delete; eauto.
        -- eapply IHt2; assumption.
Qed.



Lemma smaller_elem_false :
  forall n t, smaller n t -> elem_of n t = false.
Proof.
  induction t as [| l v r IHl IHr]; simpl; intros Hsm.
  - reflexivity.
  - inversion Hsm; subst; clear Hsm.
    destruct (r =? n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + destruct (n <? r) eqn:Hlt.
      * apply v. assumption.
      * rewrite Nat.ltb_nlt in Hlt. lia.
Qed.

Lemma greater_elem_false :
  forall n t, greater n t -> elem_of n t = false.
Proof.
  induction t as [| l v r IHl IHr]; simpl; intros Hgt.
  - reflexivity.
  - inversion Hgt; subst; clear Hgt.
    destruct (r =? n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. lia.
    + destruct (n <? r) eqn:Hlt.
      * rewrite Nat.ltb_lt in Hlt; lia.
      * apply IHr. assumption.
Qed.

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
        -- apply greater_elem_false. assumption.
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
              rewrite H1. Search (_>_).
              assert ((x <? n) = false).
              { apply Nat.ltb_ge. lia. }
              rewrite H6.
               apply greater_elem_false. assumption.
          ++ auto.
    + destruct (x <? n) eqn:Hnx0.
      * simpl. rewrite Hnx. rewrite Hnx0. apply IHt1; assumption.
      * simpl. rewrite Hnx. rewrite Hnx0. apply IHt2; assumption.
Qed.
  

