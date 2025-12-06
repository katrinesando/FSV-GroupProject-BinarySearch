Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Lia.



Definition key := nat.
Inductive color := Red | Black.
Inductive tree (V : Type) : Type :=
| E : tree V
| T : color -> tree V -> key -> V -> tree V -> tree V.
Arguments E {V}.
Arguments T {V}.
Definition empty_tree (V : Type) : tree V :=
  E.

Definition balance
           {V : Type} (c : color) (t1 : tree V) (k : key) (vk : V)
           (t2 : tree V) : tree V :=
  match c with
  | Red => T Red t1 k vk t2
  | _ => match t1 with
        | T Red (T Red a x vx b) y vy c =>
            T Red (T Black a x vx b) y vy (T Black c k vk t2)
        | T Red a x vx (T Red b y vy c) =>
            T Red (T Black a x vx b) y vy (T Black c k vk t2)
        | _ => match t2 with
              | T Red (T Red b y vy c) z vz d =>
                  T Red (T Black t1 k vk b) y vy (T Black c z vz d)
              | T Red b y vy (T Red c z vz d) =>
                  T Red (T Black t1 k vk b) y vy (T Black c z vz d)
              | _ => T Black t1 k vk t2
              end
        end
  end.
Fixpoint ins {V : Type} (x : key) (vx : V) (t : tree V) : tree V :=
  match t with
  | E => T Red E x vx E
  | T c a y vy b => if ltb x y then balance c (ins x vx a) y vy b
                   else if ltb y x then balance c a y vy (ins x vx b)
                        else T c a x vx b
  end.
Definition make_black {V : Type} (t : tree V) : tree V :=
  match t with
  | E => E
  | T _ a x vx b => T Black a x vx b
  end.
Definition insert {V : Type} (x : key) (vx : V) (t : tree V) :=
  make_black (ins x vx t).



Fixpoint elements_aux {V : Type} (t : tree V) (acc: list (key * V))
  : list (key * V) :=
  match t with
  | E => acc
  | T _ l k v r => elements_aux l ((k, v) :: elements_aux r acc)
  end.

Definition elements {V : Type} (t : tree V) : list (key * V) :=
  elements_aux t [].

Lemma ins_not_E : forall (V : Type) (x : key) (vx : V) (t : tree V),
    ins x vx t <> E.
Proof.
  intros. destruct t; simpl.
  - discriminate.
  - unfold balance.
    repeat
      match goal with
      | |- (if ?x then _ else _) <> _ => destruct x
      | |- match ?c with Red => _ | Black => _ end <> _=> destruct c
      | |- match ?t with E => _ | T _ _ _ _ _ => _ end <> _=> destruct t
      | |- T _ _ _ _ _ <> E => discriminate
      end.
Qed.


Fixpoint ForallT {V : Type} (P: nat -> V -> Prop) (t : tree V) : Prop :=
  match t with
  | E => True
  | T c l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.
Inductive BST {V : Type} : tree V -> Prop :=
| ST_E : BST E
| ST_T : forall (c : color) (l : tree V) (k : key) (v : V) (r : tree V),
    ForallT (fun k' _ => k' < k) l ->
    ForallT (fun k' _ => k' > k) r ->
    BST l ->
    BST r ->
    BST (T c l k v r).
Lemma empty_tree_BST : forall (V : Type), BST (@empty_tree V).

Proof.
  unfold empty_tree. constructor.
Qed.


Lemma ForallT_imp : forall (V : Type) (P Q : nat -> V -> Prop) t,
    ForallT P t ->
    (forall k v, P k v -> Q k v) ->
    ForallT Q t.
Proof.
  induction t; intros.
  - auto.
  - destruct H as [? [? ?]]. repeat split; auto.
Qed.
Lemma ForallT_greater : forall (V : Type) (t : tree V) (k k0 : key),
    ForallT (fun k' _ => k' > k) t ->
    k > k0 ->
    ForallT (fun k' _ => k' > k0) t.
Proof.
  intros. eapply ForallT_imp; eauto.
  intros. simpl in H1. lia.
Qed.
Lemma ForallT_less : forall (V : Type) (t : tree V) (k k0 : key),
    ForallT (fun k' _ =>  k' <  k) t ->
    k <  k0 ->
    ForallT (fun k' _ =>  k' <  k0) t.
Proof.
  intros; eapply ForallT_imp; eauto.
  intros. simpl in H1. lia.
Qed.

Ltac inv H := inversion H; subst; clear H.

Lemma balance_BST: forall (V : Type) (c : color) (l : tree V) (k : key)
                     (v : V) (r : tree V),
    ForallT (fun k' _ => ( k') < ( k)) l ->
    ForallT (fun k' _ => ( k') > ( k)) r ->
    BST l ->
    BST r ->
    BST (balance c l k v r).
Proof.
  intros. unfold balance.
  repeat
    match goal with
    | H: ForallT _ (T _ _ _ _ _) |- _ => destruct H as [? [? ?] ]
    | H: BST (T _ _ _ _ _) |- _ => inv H
    | |- BST (T _ _ _ _ _) => constructor
    | |- BST (match ?c with Red => _ | Black => _ end) => destruct c
    | |- BST (match ?t with E => _ | T _ _ _ _ _ => _ end) => destruct t
    | |- ForallT _ (T _ _ _ _ _) => repeat split
    end;
    auto; try lia.
  (* all: t applies t to every subgoal. *)
  all: try eapply ForallT_greater; try eapply ForallT_less; eauto; try lia.
Qed.

Lemma balanceP : forall (V : Type) (P : key -> V -> Prop) (c : color) (l r : tree V)
                   (k : key) (v : V),
    ForallT P l ->
    ForallT P r ->
    P k v ->
    ForallT P (balance c l k v r).
Proof.
  intros.
  unfold balance.
  repeat match goal with

(* If we know P holds for a node, it holds for the key and subtrees. *)
  | H: ForallT _ (T _ _ _ _ _) |- _ => destruct H as [? [? ?]]
  
  
(*  Destruct the variables being matched on inside 'balance'. *)
  | |- ForallT _ (match ?c with Red => _ | Black => _ end) => destruct c
  | |- ForallT _ (match ?t with E => _ | T _ _ _ _ _ => _ end) => destruct t
  
  (* 3. Solve the Goal: 
        The result is always a T node. Split the ForallT goal into its 3 parts. *)
  | |- ForallT _ (T _ _ _ _ _) => repeat split
  end;
  auto.
Qed.


Lemma insP : forall (V : Type) (P : key -> V -> Prop) (t : tree V) (k : key) (v : V),
    ForallT P t ->
    P k v ->
    ForallT P (ins k v t).
Proof.
  induction t; intros.
  - repeat split; assumption.
  - simpl.
    destruct H as [H_curr [H_left H_right]].
    destruct (k0 <? k).
    + apply balanceP; auto.
    + destruct (k <? k0); try apply balanceP; auto.
      repeat split; assumption.
Qed.

Lemma ins_BST : forall (V : Type) (t : tree V) (k : key) (v : V),
    BST t ->
    BST (ins k v t).
Proof.
  induction t; intros.
  - simpl. constructor; try assumption; split.
  - inversion H; subst. simpl. destruct (k0 <? k) eqn:Hlt.
    + apply balance_BST.
      * apply insP; rewrite Nat.ltb_lt in Hlt; assumption.
      * assumption.
      * apply IHt1; assumption.
      * assumption.
    + destruct (k <? k0) eqn:Hgt.
      * apply balance_BST; try assumption.
        -- apply insP; rewrite Nat.ltb_lt in Hgt; assumption.
        -- apply IHt2; assumption.
      * constructor; auto.
        -- assert (k = k0).
           { rewrite Nat.ltb_ge in Hgt, Hlt. lia. }
           subst. assumption.
        -- assert (k = k0).
           { rewrite Nat.ltb_ge in Hgt, Hlt. lia. }
           subst. assumption.
Qed.
         
       
Theorem insert_BST : forall (V : Type) (t : tree V) (v : V) (k : key),
    BST t ->
    BST (insert k v t).
Proof.
  intros.
  unfold insert.
  pose proof (ins_BST V t k v H) as H_ins.
  unfold make_black.
  destruct (ins k v t); [assumption|].
  inversion H_ins; subst. constructor; assumption.
Qed.


Inductive RB {V : Type} : tree V -> color -> nat -> Prop :=
| RB_leaf: forall (c : color), RB E c 0
| RB_r: forall (l r : tree V) (k : key) (v : V) (n : nat),
    RB l Red n ->
    RB r Red n ->
    RB (T Red l k v r) Black n
| RB_b: forall (c : color) (l r : tree V) (k : key) (v : V) (n : nat),
    RB l Black n ->
    RB r Black n ->
    RB (T Black l k v r) c (S n).

Lemma RB_blacken_parent : forall (V : Type) (t : tree V) (n : nat),
    RB t Red n -> RB t Black n.
Proof.
  intros.
  inversion H; subst; constructor; assumption.
Qed.

Inductive NearlyRB {V : Type} : tree V -> nat -> Prop :=
| NearlyRB_r : forall (l r : tree V) (k : key) (v : V) (n : nat),
    RB l Black n ->
    RB r Black n ->
    NearlyRB (T Red l k v r) n
| NearlyRB_b : forall (l r : tree V) (k : key) (v : V) (n : nat),
    RB l Black n ->
    RB r Black n ->
    NearlyRB (T Black l k v r) (S n).

Ltac prove_RB := 
  unfold balance;
  repeat match goal with
  (* 1. CRITICAL: Handle Impossible Leaves (Prune branches where E has height > 0) *)
  | H: NearlyRB E _ |- _ => inv H
  | H: RB E _ _ |- _ => inv H

  (* 2. Deconstruct Hypotheses on Nodes (Get facts about children) *)
  | H: RB (T _ _ _ _ _) _ _ |- _ => inv H
  | H: NearlyRB (T _ _ _ _ _) _ |- _ => inv H
  
  (* 3. Drive the Case Analysis (Destruct "match" and "if" in the program) *)
  (* Note: We destruct 'b' in 'if b then' and 'c'/'t' in match expressions *)
  | |- context [if ?b then _ else _] => destruct b
  | |- context [match ?c with Red => _ | Black => _ end] => destruct c
  | |- context [match ?t with E => _ | T _ _ _ _ _ => _ end] => destruct t
  
  (* 4. Construct the Result *)
  (* Try to build the tree. If n is wrong, the loop will retry after 'inv' fixes n. *)
  | |- NearlyRB (T _ _ _ _ _) _ => constructor
  | |- RB E _ _ => constructor
  | |- RB (T _ _ _ _ _) _ _ => constructor
  
  (* 5. Fix Color Mismatches *)
  (* If we have a Red parent proof but need a Black parent proof, convert it. *)
  | H: RB ?t Red ?n |- RB ?t Black ?n => apply RB_blacken_parent; assumption
  end;
  auto.

Lemma ins_RB : forall (V : Type) (k : key) (v : V) (t : tree V) (n : nat),
    (RB t Black n -> NearlyRB (ins k v t) n) /\
      (RB t Red n -> RB (ins k v t) Black n).
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
  - specialize (IHt1 n0). specialize (IHt2 n0). intuition.
    clear H0 H2.
    prove_RB.
  - specialize (IHt1 n0). specialize (IHt2 n0). intuition.
    clear H0 H2.
    prove_RB.
Qed.

Corollary ins_red : forall (V : Type) (t : tree V) (k : key) (v : V) (n : nat),
    RB t Red n -> RB (ins k v t) Black n.
Proof.
  intros. apply ins_RB. assumption.
Qed.

Lemma RB_blacken_root : forall (V : Type) (t : tree V) (n : nat),
    RB t Black n ->
    exists (n' : nat), RB (make_black t) Red n'.
Proof.
  intros.
  destruct t.
  - exists 0. constructor.
  - simpl. inversion H; subst.
    + exists (S n). constructor; apply RB_blacken_parent; assumption.
    + exists (S n0). constructor; assumption.
Qed.
   
Lemma insert_RB : forall (V : Type) (t : tree V) (k : key) (v : V) (n : nat),
    RB t Red n ->
    exists (n' : nat), RB (insert k v t) Red n'.
Proof.
  intros.
  unfold insert.
  apply ins_red with (k := k) (v := v) in H.
  apply RB_blacken_root with n; assumption.
Qed. 

