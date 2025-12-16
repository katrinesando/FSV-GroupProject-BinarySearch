Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Lia.

Inductive color := 
  | Red 
  | Black.

Inductive tree  :=
  | leaf : tree
  | node : color -> tree -> nat -> tree -> tree.

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

Definition balance (c : color) (t1 : tree) (k : nat) (t2 : tree) : tree :=
  match c with
  | Red => node Red t1 k t2
  | Black => 
      match t1 with
      | node Red (node Red a x b) y c =>
          node Red (node Black a x b) y (node Black c k t2)
      | node Red a x (node Red b y c) =>
          node Red (node Black a x b) y (node Black c k t2)
      | _ => 
          match t2 with
          | node Red (node Red b y c) z d =>
              node Red (node Black t1 k b) y (node Black c z d)
          | node Red b y (node Red c z d) =>
              node Red (node Black t1 k b) y (node Black c z d)
          | _ => node Black t1 k t2
          end
      end
  end.
Fixpoint ins (x : nat) (t : tree) : tree :=
  match t with
  | leaf => node Red leaf x leaf
  | node c a y b => 
      if ltb x y then balance c (ins x a) y b
      else if ltb y x then balance c a y (ins x b)
      else node c a x b
  end.

Definition make_black (t : tree) : tree :=
  match t with
  | leaf => leaf
  | node _ a vx b => node Black a vx b
  end.
Definition insert (vx : nat) (t : tree) :=
  make_black (ins vx t).

Example simple_insert : insert 2 tree1 =
  node Black (node Black leaf 2 leaf) 
  5
  (node Black leaf 10 (node Red leaf 15 leaf)).
Proof. unfold tree1. unfold insert. simpl. reflexivity. Qed.

Example complex_insert : insert 7 tree_complex =
  node Black (node Red (node Black leaf 1 leaf) 2 (node Black leaf 3 leaf))
  4
  (node Red (node Black leaf 5 leaf) 
    6 
    (node Black (node Red leaf 7 leaf) 8 (node Red leaf 9 leaf))).
Proof. unfold tree1. unfold insert. simpl. reflexivity. Qed.

Lemma ins_not_leaf : forall (vx : nat) (t : tree),
    ins vx t <> leaf.
Proof.
  intros. destruct t; simpl.
  - discriminate.
  - unfold balance.
    repeat
      match goal with
      | |- (if ?x then _ else _) <> _ => destruct x
      | |- match ?c with Red => _ | Black => _ end <> _ => destruct c
      | |- match ?t with leaf => _ | node _ _ _ _ => _ end <> _ => destruct t
      | |- node _ _ _ _ <> leaf => discriminate
      end.
Qed.

Fixpoint ForallNodes (P: nat -> Prop) (t : tree) : Prop :=
  match t with
  | leaf => True
  | node c l k r => P k /\ ForallNodes P l /\ ForallNodes P r
  end.

Inductive sorted : tree -> Prop :=
| ST_E : sorted leaf
| ST_T : forall (c : color) (l : tree) (k : nat) (r : tree),
    ForallNodes (fun k' => k' < k) l ->
    ForallNodes (fun k' => k' > k) r ->
    sorted l ->
    sorted r ->
    sorted (node c l k r).

Lemma ForallNodes_imp : forall (P Q : nat -> Prop) t,
    ForallNodes P t ->
    (forall k, P k -> Q k) ->
    ForallNodes Q t.
Proof.
  induction t; intros.
  - auto.
  - destruct H as [HPk [HFl HFr]]. repeat split; auto.
Qed.

Lemma ForallNodes_greater : forall (t : tree) (k k0 : nat),
    ForallNodes (fun k' => k' > k) t ->
    k > k0 ->
    ForallNodes (fun k' => k' > k0) t.
Proof.
  intros. eapply ForallNodes_imp; eauto.
  intros. simpl in H1. lia.
Qed.

Lemma ForallNodes_less : forall (t : tree) (k k0 : nat),
    ForallNodes (fun k' => k' < k) t ->
    k < k0 ->
    ForallNodes (fun k' => k' < k0) t.
Proof.
  intros; eapply ForallNodes_imp; eauto.
  intros. simpl in H1. lia.
Qed.

Ltac inv H := inversion H; subst; clear H.

Lemma balance_sorted: forall (c : color) (l : tree)
                     (v : nat) (r : tree),
    ForallNodes (fun k' => k' < v) l ->
    ForallNodes (fun k' => k' > v) r ->
    sorted l ->
    sorted r ->
    sorted (balance c l v r).
Proof.
  intros. unfold balance.
  repeat
    match goal with
    | H: ForallNodes _ (node _ _ _ _) |- _ => destruct H as [? [? ?] ]
    | H: sorted (node _ _ _ _) |- _ => inv H
    | |- sorted (match ?c with Red => _ | Black => _ end) => destruct c
    | |- sorted (match ?t with leaf => _ | node _ _ _ _ => _ end) => destruct t
    | |- sorted (node _ _ _ _) => constructor
    | |- ForallNodes _ (node _ _ _ _) => repeat split
    end;
    auto; try lia.
  all: try eapply ForallNodes_greater; try eapply ForallNodes_less; eauto; try lia.
Qed.

Lemma balanceP : forall (P : nat -> Prop) (c : color) (l r : tree)
                        (v : nat),
    ForallNodes P l ->
    ForallNodes P r ->
    P v ->
    ForallNodes P (balance c l v r).
Proof.
  intros.
  unfold balance.
  repeat match goal with
  | H: ForallNodes _ (node _ _ _ _) |- _ => destruct H as [? [? ?]]
  | |- ForallNodes _ (match ?c with Red => _ | Black => _ end) => destruct c
  | |- ForallNodes _ (match ?t with leaf => _ | node _ _ _ _ => _ end) => destruct t
  | |- ForallNodes _ (node _ _ _ _) => repeat split
  end;
  auto.
Qed.


Lemma insP : forall (P : nat -> Prop) (t : tree) (v : nat),
    ForallNodes P t ->
    P v ->
    ForallNodes P (ins v t).
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
    sorted t ->
    sorted (ins v t).
Proof.
  induction t; intros.
  - simpl. constructor; try assumption; split.
  - inversion H; subst. simpl. destruct (v <? n) eqn:Hlt.
    + apply balance_sorted.
      * apply insP; rewrite Nat.ltb_lt in Hlt; assumption.
      * assumption.
      * apply IHt1; assumption.
      * assumption.
    + destruct (n <? v) eqn:Hgt.
      * apply balance_sorted; try assumption.
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
    sorted t ->
    sorted (insert v t).
Proof.
  intros.
  unfold insert.
  pose proof (ins_BST t v H) as H_ins.
  unfold make_black.
  destruct (ins v t); [assumption|].
  inversion H_ins; subst. constructor; assumption.
Qed.

Inductive RB : tree -> color -> nat -> Prop :=
| RB_leaf: forall (c : color), RB leaf c 0
| RB_r: forall (l r : tree) (k : nat) (n : nat),
    RB l Red n ->
    RB r Red n ->
    RB (node Red l k r) Black n
| RB_b: forall (c : color) (l r : tree) (k : nat) (n : nat),
    RB l Black n ->
    RB r Black n ->
    RB (node Black l k r) c (S n).

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
    NearlyRB (node Red l v r) n
| NearlyRB_b : forall (l r : tree) (v : nat) (n : nat),
    RB l Black n ->
    RB r Black n ->
    NearlyRB (node Black l v r) (S n).

Ltac prove_RB :=
unfold balance;
  repeat match goal with
  | [ |- context [if (?x <? ?y) then _ else _] ] => 
      destruct (x <? y)
  | [ H : RB (node Red _ _ _) Red _ |- _ ] => 
      inversion H
  | [ H : NearlyRB ?t _ |- context [match ?t with _ => _ end] ] => 
      inv H
  | [ H : RB ?t _ _ |- context [match ?t with _ => _ end] ] => 
      inv H
  | [ |- NearlyRB (node _ _ _ _) _ ] => constructor
  | [ |- RB _ _ _ ] => constructor
    | [ H : RB ?t Red _ |- RB ?t Black _ ] => 
      apply RB_blacken_parent; assumption
  end;
  subst; simpl; auto.

Lemma ins_RB : forall (v : nat) (t : tree) (n : nat),
    (RB t Black n -> NearlyRB (ins v t) n) /\
      (RB t Red n -> RB (ins v t) Black n).
Proof.
 
   induction t; split; intros; inv H; simpl.
  - repeat constructor.
  - repeat constructor.
  - specialize (IHt1 n0). specialize (IHt2 n0).
    intuition.
    prove_RB.
  - specialize (IHt1 n1). specialize (IHt2 n1). 
    intuition.
    prove_RB.
  - specialize (IHt1 n1). specialize (IHt2 n1). 
    intuition.
    prove_RB.
Qed.

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

Definition validRBTree (t : tree) : Prop :=
  sorted t /\ (exists n, RB t Red n).

Theorem insert_is_valid : forall (t : tree) (v : nat),
    validRBTree t ->
    validRBTree (insert v t).
Proof.
  intros t v H.
  unfold validRBTree in *.
  destruct H as [H_bst H_rb].
  destruct H_rb as [n H_rb_prop].

  split.
  - apply insert_BST.
    assumption.

  - pose proof (insert_RB t v n H_rb_prop) as H_result.
    destruct H_result as [n' H_new_rb].
    exists n'.
    assumption.
Qed.