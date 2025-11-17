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


(* If successor exists, it satisfies smaller property *)
Lemma successor_smaller : forall n t v,
  smaller n t -> successor t = Some v -> n < v.
Proof.
  induction t; intros. simpl in H0.
  - discriminate.
  - inversion H; subst. destruct t1; simpl in *.
    + injection H0 as H0; subst. assumption.
    + eapply IHt1; eauto.
Qed.

Lemma successor_unfold :
  forall r1 n1 r2 v,
    successor (node r1 n1 r2) = Some v ->
    match r1 with
    | leaf => Some n1
    | node _ _ _ => successor r1
    end = Some v.
Proof.
  intros r1 n1 r2 v H.
  simpl in H.
  destruct r1; simpl in *; auto.
Qed.


(* Successor is the minimum in the right subtree, so it's >= root in BST *)
Lemma successor_greater : forall n t v,
  greater n t -> successor t = Some v -> n > v.
Proof.
  induction t; intros; simpl in *.
  - discriminate.
  - inversion H; subst. destruct t1; simpl in *.
    + injection H0 as H0; subst. assumption.
    + eapply IHt1; eauto.
Qed.

(* In a sorted BST, the successor from right subtree is greater than all left *)
Lemma successor_greater_than_left : forall l v r succ_v,
  sorted (node l v r) ->
  successor r = Some succ_v ->
  greater succ_v l.
Proof.
  intros. inversion H; subst.
  assert (v < succ_v).
  { eapply successor_smaller; eauto. }
  induction l.
  - constructor.
  - inversion H4; subst. constructor.
    +  lia.
    + apply IHl1; eauto.
      * constructor; try assumption.
       -- inversion H5; inversion H6; subst; assumption.
      * inversion H5; inversion H6; subst; assumption.
    + apply IHl2; eauto.
      * constructor; try assumption.
       -- inversion H5; inversion H6; subst; assumption.
      * inversion H5; inversion H6; subst; assumption.
Qed.


Lemma smaller_delete_any : forall n x t,
  smaller n t -> smaller n (delete x t).
Proof.
  induction t as [| l IHl v r IHr]; intros; simpl.
  - exact H.
  - inversion H; subst; clear H.
    destruct (v =? x) eqn:Heq.
    + destruct l.
      * exact H6.
      * destruct r.
        -- exact H5.
        -- simpl. destruct (successor (node r1 n1 r2)) eqn:Hsucc.
           ++ pose proof (successor_unfold r1 n1 r2 n2 Hsucc) as Hunf.
              rewrite Hunf. constructor.
              ** eapply successor_smaller; eauto.
              ** exact H5.
              ** admit. 
              (* apply IHr. exact H6. *)
           ++ simpl in Hsucc. admit. 
           (* destruct r1; discriminate. *)
    + destruct (x <? v) eqn:Hlt.
      * constructor; try assumption. apply IHl; assumption.
      * constructor; try assumption. apply IHr; assumption.
Admitted.

(* In a sorted BST, successor from right is smaller than all right after deletion *)
Lemma successor_smaller_than_right : 
  forall r succ_v,
    sorted r ->
    successor r = Some succ_v ->
    smaller succ_v (delete succ_v r).
Proof.
  induction r; intros; simpl in *.
  - discriminate.
  - destruct r1; simpl in *.
    + (* Base case: successor is the root *)
      injection H0 as H0; subst.
      simpl. rewrite Nat.eqb_refl. 
      inversion H; subst. eauto.
    + (* Recursive case *)
      inversion H; subst.
      destruct (n =? succ_v) eqn:Heq.
      * (* n = succ_v, impossible since successor is in left *)
        simpl in H0. destruct r1_1.
        -- (* Left subtree is leaf, so successor is n *)
           injection H0 as H0; subst.
           simpl. 
           inversion H; subst. destruct r2.
           ++ constructor.
              ** exfalso. inversion H; subst. rewrite Nat.eqb_eq in Heq. subst. inversion H4; subst. lia.
              ** eauto.
              ** inversion H6. subst. eauto.
          ++ destruct (successor (node r2_1 n0 r2_2)) eqn:Hsucc2; try eauto.
              ** constructor.
                --- (* Left subtree has successor *)
                rewrite Nat.eqb_eq in Heq. subst. eapply successor_smaller; try eauto.
                --- constructor; try (inversion H6; subst; eauto).
                  *** exfalso. inversion H; subst. rewrite Nat.eqb_eq in Heq. subst. inversion H4; subst. lia.
                --- rewrite Nat.eqb_eq in Heq. subst. apply smaller_delete_any. eauto.
          -- (* Left subtree is not leaf, contradicts n = succ_v *)
           simpl in H0. 
           admit.
      * destruct (succ_v <? n) eqn:Hlt.
        -- (* Delete from left *)
           simpl. constructor.
           ++ eapply successor_smaller; eauto. admit.
           ++ apply IHr1; assumption.
           ++ eauto. admit.
        -- (* succ_v >= n, but we know succ_v < n from BST property *)   
        (* assert (succ_v < n) by 
           (eapply successor_smaller; eauto).
           rewrite Nat.ltb_lt in Hlt. lia. *)
Admitted.

Lemma successor_greater_root :
  forall r1 n1 r2 v,
    successor (node r1 n1 r2) = Some v ->
    n1 >= v.
Proof.
  intros r1 n1 r2 v H.
  simpl in H. 
  destruct r1; simpl in *.
  - inversion H. subst. lia.
  - admit.
Admitted.

Lemma greater_delete : forall n x t,
  greater n t -> greater n (delete x t).
Proof.
  induction t as [| l IHl v r IHr]; intros; simpl.
  - exact H.
  - inversion H; subst; clear H.
    destruct (v =? x) eqn:Heq.
    + destruct l.
      * exact H6.
      * destruct r.
        -- exact H5.
        -- simpl. destruct (successor (node r1 n1 r2)) eqn:Hsucc.
           ++ pose proof (successor_unfold r1 n1 r2 n2 Hsucc) as Hunf.
              rewrite Hunf. constructor.
              ** eapply successor_greater; eauto.
              ** exact H5.
              ** admit. 
              (* apply IHr. exact H6. *)
           ++ simpl in Hsucc. 
           admit. 
           (* destruct r1; discriminate. *)
    + destruct (x <? v) eqn:Hlt.
      * constructor; try assumption. apply IHl; assumption.
      * constructor; try assumption. apply IHr; assumption.
Admitted.

Hint Resolve successor_smaller : core.
Hint Resolve successor_unfold : core.
Hint Resolve successor_greater : core.
Hint Resolve successor_greater_than_left : core.
Hint Resolve smaller_delete_any : core.
Hint Resolve successor_smaller_than_right : core.
Hint Resolve successor_greater_root : core.
Hint Resolve greater_delete : core.

Lemma delete_sorted :
  forall t x, sorted t -> sorted (delete x t).
Proof.
   induction t; simpl; intros.
  - assumption.
  - inversion H; subst. destruct (n=?x) eqn:Heq.
    + (* Deleting the root *)
      destruct t1.
      * assumption.
      * destruct t2.
        -- assumption.
        -- (* Two-child case *)
           destruct (successor (node t2_1 n1 t2_2)) eqn:Hsucc.
           ++ simpl in Hsucc. destruct t2_1; try discriminate.
              ** (* Right child has no left subtree *)
                 injection Hsucc as Hsucc; subst.
                 simpl. constructor.
                 --- apply successor_greater_than_left with (v := n) (r := node leaf n2 t2_2); try eauto.
                 --- admit.
                  (* apply smaller_delete_any. 
                     apply successor_smaller_than_right with (r := node leaf n1 t2_2); assumption. *)
                 --- assumption.
                 --- apply IHt2. assumption.
              ** (* Right child has left subtree *)
                 constructor.
                 --- apply successor_greater_than_left with (v := n) (r := node (node t2_1_1 n2 t2_1_2) n1 t2_2); try eauto.
                 (* apply successor_greater_than_left with (r := node (node t2_1_1 n2 t2_1_2) n1 t2_2); assumption. *)
                 --- apply smaller_delete_any. admit.
                     (* apply successor_smaller_than_right with (r := node (node t2_1_1 n2 t2_1_2) n1 t2_2); assumption. *)
                 --- assumption.
                 --- apply IHt2. assumption.
           ++ simpl in Hsucc. admit.
    + (* Not deleting root, recurse *)
      destruct (x <? n) eqn:Hlt.
      * constructor; try eauto.
        -- apply greater_delete. assumption.
      * constructor; try eauto.
        -- apply smaller_delete_any. assumption.
Admitted.


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
  

