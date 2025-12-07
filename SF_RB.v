Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Lia.



Definition key := nat.
Inductive color := Red | Black.

Inductive tree  :=
| E : tree
| T : color -> tree -> nat -> tree -> tree.

Definition empty_tree : tree :=
  E.

(*   Arguments E {V}.
Arguments T {V}. *)

Definition balance (c : color) (t1 : tree) (k : nat) (t2 : tree) : tree :=
  match c with
  | Red => T Red t1 k t2
  | Black => 
      match t1 with
      | T Red (T Red a x b) y c =>
          T Red (T Black a x b) y (T Black c k t2)
      | T Red a x (T Red b y c) =>
          T Red (T Black a x b) y (T Black c k t2)
      | _ => 
          match t2 with
          | T Red (T Red b y c) z d =>
              T Red (T Black t1 k b) y (T Black c z d)
          | T Red b y (T Red c z d) =>
              T Red (T Black t1 k b) y (T Black c z d)
          | _ => T Black t1 k t2
          end
      end
  end.
Fixpoint ins (x : nat) (t : tree) : tree :=
  match t with
  | E => T Red E x E
  | T c a y b => 
      if ltb x y then balance c (ins x a) y b
      else if ltb y x then balance c a y (ins x b)
      else T c a x b
  end.
Definition make_black (t : tree) : tree :=
  match t with
  | E => E
  | T _ a vx b => T Black a vx b
  end.
Definition insert (vx : nat) (t : tree) :=
  make_black (ins vx t).

(* Fixpoint elements_aux (t : tree) (acc : list nat) : list nat :=
  match t with
  | E => acc
  | T _ l k r => elements_aux l (k :: elements_aux r acc)
  end.

Definition elements (t : tree) : list nat :=
  elements_aux t [].
 *)
Lemma ins_not_E : forall (vx : nat) (t : tree),
    ins vx t <> E.
Proof.
  intros. destruct t; simpl.
  - discriminate.
  - unfold balance.
    repeat
      match goal with
      | |- (if ?x then _ else _) <> _ => destruct x
      | |- match ?c with Red => _ | Black => _ end <> _ => destruct c
      | |- match ?t with E => _ | T _ _ _ _ => _ end <> _ => destruct t
      | |- T _ _ _ _ <> E => discriminate
      end.
Qed.


Fixpoint ForallT (P: nat -> Prop) (t : tree) : Prop :=
  match t with
  | E => True
  | T c l k r => P k /\ ForallT P l /\ ForallT P r
  end.

Inductive BST : tree -> Prop :=
| ST_E : BST E
| ST_T : forall (c : color) (l : tree) (k : nat) (r : tree),
    ForallT (fun k' => k' < k) l ->
    ForallT (fun k' => k' > k) r ->
    BST l ->
    BST r ->
    BST (T c l k r).
Lemma empty_tree_BST : forall (V : Type), BST (empty_tree).

Proof.
  unfold empty_tree. constructor.
Qed.


Lemma ForallT_imp : forall (P Q : nat -> Prop) t,
    ForallT P t ->
    (forall k, P k -> Q k) ->
    ForallT Q t.
Proof.
  induction t; intros.
  - auto.
  - destruct H as [? [? ?]]. repeat split; auto.
Qed.

Lemma ForallT_greater : forall (t : tree) (k k0 : nat),
    ForallT (fun k' => k' > k) t ->
    k > k0 ->
    ForallT (fun k' => k' > k0) t.
Proof.
  intros. eapply ForallT_imp; eauto.
  intros. simpl in H1. lia.
Qed.

Lemma ForallT_less : forall (t : tree) (k k0 : nat),
    ForallT (fun k' => k' < k) t ->
    k < k0 ->
    ForallT (fun k' => k' < k0) t.
Proof.
  intros; eapply ForallT_imp; eauto.
  intros. simpl in H1. lia.
Qed.

Ltac inv H := inversion H; subst; clear H.

Lemma balance_BST: forall (c : color) (l : tree)
                     (v : nat) (r : tree),
    ForallT (fun k' => ( k') < ( v)) l ->
    ForallT (fun k' => ( k') > ( v)) r ->
    BST l ->
    BST r ->
    BST (balance c l v r).
Proof.
  intros. unfold balance.
  repeat
    match goal with
    | H: ForallT _ (T _ _ _ _) |- _ => destruct H as [? [? ?] ]
    | H: BST (T _ _ _ _) |- _ => inv H
    | |- BST (match ?c with Red => _ | Black => _ end) => destruct c
    | |- BST (match ?t with E => _ | T _ _ _ _ => _ end) => destruct t
    | |- BST (T _ _ _ _) => constructor
    | |- ForallT _ (T _ _ _ _) => repeat split
    end;
    auto; try lia.
  all: try eapply ForallT_greater; try eapply ForallT_less; eauto; try lia.
Qed.

Lemma balanceP : forall (P : nat -> Prop) (c : color) (l r : tree)
                        (v : nat),
    ForallT P l ->
    ForallT P r ->
    P v ->
    ForallT P (balance c l v r).
Proof.
  intros.
  unfold balance.
  repeat match goal with

(* If we know P holds for a node, it holds for the key and subtrees. *)
  | H: ForallT _ (T _ _ _ _) |- _ => destruct H as [? [? ?]]
  
  
(*  Destruct the variables being matched on inside 'balance'. *)
  | |- ForallT _ (match ?c with Red => _ | Black => _ end) => destruct c
  | |- ForallT _ (match ?t with E => _ | T _ _ _ _ => _ end) => destruct t
  
  (* 3. Solve the Goal: 
        The result is always a T node. Split the ForallT goal into its 3 parts. *)
  | |- ForallT _ (T _ _ _ _) => repeat split
  end;
  auto.
Qed.


Lemma insP : forall (P : nat -> Prop) (t : tree) (v : nat),
    ForallT P t ->
    P v ->
    ForallT P (ins v t).
Proof.
  induction t; intros.
  - repeat split; assumption.
  - simpl.
    destruct H as [H_curr [H_left H_right]].
    destruct (v <? n).
    + apply balanceP; auto.
    + destruct (n <? v); try apply balanceP; auto.
      repeat split; assumption.
Qed.

Lemma ins_BST : forall (t : tree) (v : nat),
    BST t ->
    BST (ins v t).
Proof.
  induction t; intros.
  - simpl. constructor; try assumption; split.
  - inversion H; subst. simpl. destruct (v <? n) eqn:Hlt.
    + apply balance_BST.
      * apply insP; rewrite Nat.ltb_lt in Hlt; assumption.
      * assumption.
      * apply IHt1; assumption.
      * assumption.
    + destruct (n <? v) eqn:Hgt.
      * apply balance_BST; try assumption.
        -- apply insP; rewrite Nat.ltb_lt in Hgt; assumption.
        -- apply IHt2; assumption.
      * constructor; auto.
        -- assert (v = n).
           { rewrite Nat.ltb_ge in Hgt, Hlt. lia. }
           subst. assumption.
        -- assert (v = n).
           { rewrite Nat.ltb_ge in Hgt, Hlt. lia. }
           subst. assumption.
Qed.
         
       
Theorem insert_BST : forall (t : tree) (v : nat),
    BST t ->
    BST (insert v t).
Proof.
  intros.
  unfold insert.
  pose proof (ins_BST t v H) as H_ins.
  unfold make_black.
  destruct (ins v t); [assumption|].
  inversion H_ins; subst. constructor; assumption.
Qed.

Inductive RB : tree -> color -> nat -> Prop :=
| RB_leaf: forall (c : color), RB E c 0
| RB_r: forall (l r : tree) (k : nat) (n : nat),
    RB l Red n ->
    RB r Red n ->
    RB (T Red l k r) Black n
| RB_b: forall (c : color) (l r : tree) (k : nat) (n : nat),
    RB l Black n ->
    RB r Black n ->
    RB (T Black l k r) c (S n).

Lemma RB_blacken_parent : forall (t : tree) (n : nat),
    RB t Red n -> RB t Black n.
Proof.
  intros.
  inversion H; subst; constructor; assumption.
Qed.

Inductive NearlyRB : tree -> nat -> Prop :=
| NearlyRB_r : forall (l r : tree) (v : nat) (n : nat),
    RB l Black n ->
    RB r Black n ->
    NearlyRB (T Red l v r) n
| NearlyRB_b : forall (l r : tree) (v : nat) (n : nat),
    RB l Black n ->
    RB r Black n ->
    NearlyRB (T Black l v r) (S n).

Ltac prove_RB :=
  admit.
Lemma ins_RB : forall (v : nat) (t : tree) (n : nat),
    (RB t Black n -> NearlyRB (ins v t) n) /\
      (RB t Red n -> RB (ins v t) Black n).
Proof.
  induction t; split; intros; inv H; repeat constructor; simpl.
  - (* Instantiate the inductive hypotheses. *)
    specialize (IHt1 n). specialize (IHt2 n).
    (* Derive what propositional facts we can from the hypotheses. *)
    intuition.
    (* Get rid of some extraneous hypotheses. *)
    clear H H1.
    (* Finish with automation. *)
    prove_RB.
  - specialize (IHt1 n). specialize (IHt2 n). intuition.
    clear H0 H2.
    prove_RB.
  - specialize (IHt1 n). specialize (IHt2 n). intuition.
    clear H0 H2.
    prove_RB.
Admitted.

Corollary ins_red : forall (t : tree) (v : nat) (n : nat),
    RB t Red n -> RB (ins v t) Black n.
Proof.
  intros. apply ins_RB. assumption.
Qed.

Lemma RB_blacken_root : forall (t : tree) (n : nat),
    RB t Black n ->
    exists (n' : nat), RB (make_black t) Red n'.
Proof.
  intros.
  destruct t.
  - exists 0. constructor.
  - simpl. inversion H; subst.
    + exists (S n). constructor; apply RB_blacken_parent; assumption.
    + exists (S n1). constructor; assumption.
Qed.
   
Lemma insert_RB : forall (t : tree) (v : nat) (n : nat),
    RB t Red n ->
    exists (n' : nat), RB (insert v t) Red n'.
Proof.
  intros.
  unfold insert.
  apply ins_red with (v := v) in H.
  apply RB_blacken_root with n; assumption.
Qed. 

