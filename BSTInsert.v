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

(* Minimum value property in right subtree *)
Lemma successor_all_right :
  forall r m,
    sorted r ->
    successor r = Some m ->
    smaller m r.
Proof.
  induction r; intros m Hsrt Hsucc; simpl in *; try discriminate.
  destruct r1; inversion Hsrt; subst.
  - (* left = leaf, root is successor *)
    (* inversion Hsucc; subst m. constructor. 
    try eauto. try lia. admit. *)
     (* successor in left subtree *)
    injection Hsucc as <-. constructor; try eauto.
    + contradiction. exfalso. admit.
    (* + assumption. *)
  - (* successor in left subtree *)
    admit. 
Admitted.

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
  (* Get smaller m r from successor_all_right *)
  assert (Hsm_m_r : smaller m r) by (eapply successor_all_right; eauto).
  (* smaller v r gives v < all elems of r, successor_smaller gives v < m *)
  assert (v < m) by (admit).
  (* Use greater v l and transitivity: for any x in l, x < v < m *)
  revert H3. (* H3 is greater v l *)
  induction l; intros Hgl; constructor.
  - inversion Hgl; subst; admit.
  - inversion Hgl; subst.
    + admit.
    + apply IHl1; admit.
  Admitted.


(* Delete preserves 'smaller' when we delete ANY x (except root collapse case is handled by pattern) *)
Lemma smaller_delete_any :
  forall n x t,
    smaller n t ->
    smaller n (delete x t).
Proof.
  induction t; intros; simpl.
  - assumption.
  - inversion H; subst.
    destruct (n0 =? x) eqn:Heq.
    + (* deleting root *)
      destruct t1, t2; simpl; try assumption.
      (* two-child case: rebuilding root with successor; need smaller n new_tree *)
      all: destruct (successor (node t2_1 n0 t2_2)) eqn:Hsucc; try assumption.
      * (* Successor found *)
        admit.
      * (* No successor: impossible since right has at least root *)
        simpl in Hsucc. admit.
    + destruct (x <? n0) eqn:Hlt.
      * constructor; try assumption; apply IHt1; assumption.
      * constructor; try assumption; apply IHt2; assumption.
Admitted.

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

Lemma greater_delete :
  forall n x t,
    greater n t ->
    greater n (delete x t).
Proof.
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
              eapply greater_than_successor; eauto.
           ++ (* greater n left *)
              assumption.
           ++ (* greater n t2_2 *)
              inversion H6; subst. 
              rewrite (Nat.eqb_refl n2). eauto.
        -- (* t2_1 = node, successor from left subtree *)
            admit.   
        (* constructor.
           ++ (* n > n3 *)
              eapply greater_than_successor; eauto.
           ++ (* greater n left *)
              assumption.
           ++ (* greater n (delete n3 right) *)
              apply IHt2. assumption. *)
      * (* no successor: impossible *)
        eauto. admit.
    + (* not deleting root *)
      destruct (x <? n0) eqn:Hlt.
      * constructor; try assumption; apply IHt1; assumption.
      * constructor; try assumption; apply IHt2; assumption.
Admitted.

(* After deleting the successor from r, remaining elements are > successor *)
Lemma successor_smaller_right_after_delete :
  forall r m,
    sorted r ->
    successor r = Some m ->
    smaller m (delete m r).
Proof.
  intros r m Hsort Hsucc.
  (*
  (* First: smaller m r from successor_all_right *)
  apply smaller_delete_any.
  eapply successor_all_right; eauto. *)
  revert m Hsucc.
  induction r; intros m Hsucc; simpl in *; try discriminate.
  inversion Hsort; subst.
  destruct r1.
  - (* right subtree root is the successor, delete removes it and returns r2 *)
    inversion Hsucc; subst. simpl. eauto. admit.
  - (* successor comes from the left subtree *)
    simpl in Hsucc. admit.
Admitted.    
    (* assert (m < v) as Hmv.
    { (* successor from left is < v because all elements of left are < v *)
      eapply successor_lt_root_left with (l:=r1) (r:=r2); eauto.
    }
    assert (v =? m = false) by (apply Nat.eqb_neq; lia).
    assert (m <? v = true) by (apply Nat.ltb_lt; auto).
    rewrite H0, H1. clear H0 H1.
    constructor; try assumption.
    + (* m < v *) exact Hmv.
    + (* smaller m r2 via transitivity m < v and smaller v r2 *)
      eapply smaller_lift_right; eauto. *)


Lemma delete_sorted :
  forall t x, sorted t -> sorted (delete x t).
Proof.
  induction t; intros x Hs; simpl.
  - assumption.
  - inversion Hs; subst.
    destruct (n =? x) eqn:Heq.
    + (* deleting root *)
      destruct t1.
      * (* no left subtree *)
        destruct t2.
        -- (* no right subtree: tree becomes leaf *) constructor.
        -- (* one-child right: node leaf n0 t2_2 becomes t2 *) assumption.
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
        -- eapply smaller_delete_any; eauto.
        -- eapply IHt2; assumption.
Qed.

Lemma delete_correct :
forall t x,
    sorted t ->
    elem_of x t = true -> 
    (elem_of x (delete x t)) = false.
Proof.
  intros. 
  induction t. simpl; intros.
  - admit.
  - inversion H. 
Admitted.
  

