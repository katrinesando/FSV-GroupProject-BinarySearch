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


(* simple inversion lemmas to reuse everywhere *)
Lemma rb_sorted_node_inv :
  forall c l v r,
    rb_sorted (node c l v r) ->
    greater v l /\ smaller v r /\ rb_sorted l /\ rb_sorted r.
Proof.
  intros c l v r H.
  inversion H; subst; clear H.
  repeat split; assumption.
Qed.

Lemma greater_node_inv :
  forall n c l v r,
    greater n (node c l v r) -> n > v /\ greater n l /\ greater n r.
Proof.
  intros n c l v r H.
  inversion H; subst; clear H.
  repeat split; assumption.
Qed.

Lemma smaller_node_inv :
  forall n c l v r,
    smaller n (node c l v r) -> n < v /\ smaller n l /\ smaller n r.
Proof.
  intros n c l v r H.
  inversion H; subst; clear H.
  repeat split; assumption.
Qed.

Ltac inv H := inversion H; subst; clear H.

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
    constructor; assumption.
  - (* originally black *)
    constructor; assumption.
Qed.

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
  apply Nat.eqb_eq in Heq; subst. 
  inversion H; subst k. clear H. simpl.
  destruct c; simpl; rewrite Hl, Hr; rewrite Nat.eqb_refl; try reflexivity.
  - rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma balance_node_never_leaf :
  forall c l v r, balance (node c l v r) <> leaf.
Proof.
  intros c l v r.
  destruct c; destruct l; destruct r; simpl; intro H; try discriminate.
  (* The remaining branches contain nested pattern matches *)
    all: repeat ( (*<- Custom automation pattern - some cases were nested pattern matches that hadnt not been evaluated yet, so a single discriminate didnt work*)
      match goal with
      | H : context[match ?x with _ => _ end] |- _ =>
          destruct x; simpl in H
      end; try discriminate
    ).
Qed.
Lemma smaller_decrease : forall m n t,
  m < n ->
  smaller n t ->
  smaller m t.
Proof.
  intros m n t Hlt.
  induction t; simpl; intros Hsm; try (inversion Hsm; constructor).
  inversion Hsm; subst; clear Hsm.
  - lia.
  - apply IHt1; assumption.
  - apply IHt2; assumption.
Qed.


Lemma balance_case_left_left_sorted:
  forall a x b y c v r,
    rb_sorted (node Black (node Red (node Red a x b) y c) v r) ->
    rb_sorted (node Red (node Black a x b) y (node Black c v r)).
Proof.
  intros a x b y c v r H.
  (* outer node facts *)
  apply rb_sorted_node_inv in H.
  destruct H as [Hgt_outer [Hsm_outer [Hrb_l Hrb_r]]].
  (* left = node Red (node Red a x b) y c *)
  apply rb_sorted_node_inv in Hrb_l.
  destruct Hrb_l as [Hgt_l [Hsm_l [Hrb_ll Hrb_lr]]].
  (* inner left = node Red a x b *)
  apply rb_sorted_node_inv in Hrb_ll.
  destruct Hrb_ll as [Hgt_ll [Hsm_ll [Hrb_lla Hrb_llr]]].
  simpl.
  constructor.
  - (* greater y (node Black a x b) *)
    (* Hgt_l : greater y (node Red a x b) -> gives y > x and greater y a and greater y b *)
    apply greater_node_inv in Hgt_l.
    destruct Hgt_l as [Hy_gt_x [Hy_ga Hy_gb]].
    constructor; assumption.
  - (* smaller y (node Black c v r) *)
    apply greater_node_inv in Hgt_outer.
    destruct Hgt_outer as [Hv_gt_y [Hv_g_left Hv_g_c]].
    constructor; try assumption. apply smaller_decrease with (m:=y) (n:=v) (t:=r); [ exact Hv_gt_y | exact Hsm_outer ].  
  - (* rb_sorted (node Black a x b) *)
    constructor; try assumption.
  - (* rb_sorted (node Black c v r) *)
    constructor; try assumption.
    + (* greater v c *) apply greater_node_inv in Hgt_outer; destruct Hgt_outer as [_ [_ Hv_g_right]]. assumption.
Qed.

Lemma greater_monotone :
  forall m n t,
    m > n ->
    greater n t ->
    greater m t.
Proof.
  intros m n t Hmn.
  induction t; simpl; intros H; try (inversion H; constructor).
  inversion H; subst; clear H.
  - lia.
  - apply IHt1; assumption.
  - apply IHt2; assumption.
Qed.
Lemma balance_left_left_sorted :
  forall lv_l lr1 n lr2 v rl1 n0 rl2 rv_r,
    greater v (node Red leaf lv_l (node Red lr1 n lr2)) ->
    smaller v (node Black (node Black rl1 n0 rl2) rv_r leaf) ->
    rb_sorted (node Red leaf lv_l (node Red lr1 n lr2)) ->
    rb_sorted (node Black (node Black rl1 n0 rl2) rv_r leaf) ->
    rb_sorted
      (node Black (node Red leaf lv_l (node Red lr1 n lr2)) v
                 (node Black (node Black rl1 n0 rl2) rv_r leaf)) ->
    rb_sorted
      (node Red (node Black leaf lv_l lr1) n
                (node Black lr2 v (node Black (node Black rl1 n0 rl2) rv_r leaf))).
Proof. Admitted. 
Ltac prepare_inv :=
  repeat match goal with
  | [ H: rb_sorted (node _ _ _ _) |- _ ] => apply rb_sorted_node_inv in H
  | [ H: smaller _ (node _ _ _ _) |- _ ] => apply smaller_node_inv in H
  | [ H: greater _ (node _ _ _ _) |- _ ] => apply greater_node_inv in H
  end.

Ltac try_finish_one :=
  try (pose proof (greater_monotone _ _ _) as _; [ lia | idtac ]);
  try (eapply smaller_decrease; [ lia | eassumption ]);
  (* try to finish by constructor using available facts / recolor helper *)
  try (constructor; try assumption; try (apply recolor_preserves_rb_sorted; assumption);
       try (eassumption); try lia).

Ltac finish_balance_branch :=
  prepare_inv;
  repeat match goal with
  | [ |- context[node ?c ?l ?v ?r] ] => idtac
  end;
  try repeat (try_finish_one);
  try lia. 

Ltac fast_inv :=
  repeat match goal with
  | [ H: rb_sorted (node _ _ _ _) |- _ ] => apply rb_sorted_node_inv in H
  | [ H: smaller _ (node _ _ _ _) |- _ ] => apply smaller_node_inv in H
  | [ H: greater _ (node _ _ _ _) |- _ ] => apply greater_node_inv in H
  end.

Ltac finish_goal :=
  try (eapply greater_monotone; [lia | eassumption]);
  try (eapply smaller_decrease; [lia | eassumption]);
  try (constructor; try assumption; try (apply recolor_preserves_rb_sorted; assumption); try lia).

Ltac solve_balance :=
  fast_inv;
  repeat (finish_goal; fast_inv);
  try lia.

Ltac maybe_smaller_decrease :=
  repeat (try (eapply smaller_decrease; eauto)).

Ltac maybe_rb_sorted_destruct :=
  match goal with
  | [ H: rb_sorted _ /\ rb_sorted _ |- _ ] =>
      let Hl := fresh "Hleft" in let Hr := fresh "Hright" in
      destruct H as [Hl Hr];
      try (let Htmp := fresh "Htmp" in pose proof Hr as Htmp;
           apply rb_sorted_node_inv in Htmp; destruct Htmp as [? [? [? ?]]];
           constructor; eauto)
  | [ H: rb_sorted _ |- _ ] =>
      let Htmp := fresh "Htmp" in
      pose proof H as Htmp;
      apply rb_sorted_node_inv in Htmp; destruct Htmp as [? [? [? ?]]];
      constructor; eauto
  | _ => idtac
end.

Ltac finish_bal_branch :=
  constructor; try (constructor; eauto); try (apply node_smaller); eauto; try lia;
  maybe_smaller_decrease; maybe_rb_sorted_destruct. 

Ltac maybe_smaller_decrease_one :=
  match goal with
  | [ |- smaller ?m ?t ] =>
      match goal with
      | [ H: smaller ?n ?t |- _ ] =>
          eapply (smaller_decrease m n t); [ lia | exact H ]
      end
  end.

Ltac maybe_rb_sorted_expand :=
  repeat match goal with
  | [ H: _ /\ _ |- _ ] => destruct H
  | [ H: rb_sorted (node ?c ?l ?v ?r) |- _ ] =>
      let Htmp := fresh "Hrb" in pose proof H as Htmp;
      apply rb_sorted_node_inv in Htmp;
      let Hgt := fresh "Hrb_gt" in let Hsm := fresh "Hrb_sm" in let Hl := fresh "Hrb_l" in let Hr := fresh "Hrb_r" in
      destruct Htmp as [Hgt [Hsm [Hl Hr]]]
  end.

Ltac finish_bal_branch_test :=
  constructor; try (constructor; eauto); try (apply node_smaller); eauto; try lia;
  (* apply up to 3 smaller_decrease steps if applicable (bounded to avoid loops) *)
  do 3 (try maybe_smaller_decrease_one);
  maybe_rb_sorted_expand.


Ltac expand_rb_sorted H :=
  let Htmp := fresh "Hrb" in pose proof H as Htmp;
  apply rb_sorted_node_inv in Htmp;
  let Hgt := fresh "Hgt" in let Hsm := fresh "Hsm" in let Hl := fresh "Hl" in let Hr := fresh "Hr" in
  destruct Htmp as [Hgt [Hsm [Hl Hr]]].

Ltac expand_greater H :=
  let Htmp := fresh "Hgr" in pose proof H as Htmp;
  apply greater_node_inv in Htmp;
  let Hgtv := fresh "Hgtv" in let Hgl := fresh "Hgl" in let Hgrr := fresh "Hgrr" in
  destruct Htmp as [Hgtv [Hgl Hgrr]].

Ltac expand_smaller H :=
  let Htmp := fresh "Hsm" in pose proof H as Htmp;
  apply smaller_node_inv in Htmp;
  let Hlt := fresh "Hlt" in let Hsl := fresh "Hsl" in let Hsr := fresh "Hsr" in
  destruct Htmp as [Hlt [Hsl Hsr]].

Ltac expand_all_invs :=
  repeat (
    match goal with
    | [ H: rb_sorted (node _ _ _ _) |- _ ] => expand_rb_sorted H
    | [ H: greater _ (node _ _ _ _) |- _ ] => expand_greater H
    | [ H: smaller _ (node _ _ _ _) |- _ ] => expand_smaller H
    end).

Ltac try_finish_step :=
  first
    [ (* straightforward: constructor + eauto *)
      (constructor; try eauto 6)
    | (* recolor case *)
      (apply recolor_preserves_rb_sorted; eauto 6)
    | (* lift greater using monotonicity *)
      (eapply greater_monotone; [lia | eassumption])
    | (* decrease smaller using inequality *)
      (eapply smaller_decrease; [lia | eassumption])
    | lia ].

(* bounded finishing loop to avoid infinite loops *)
Ltac finish_balance_case :=
  (* Expand only the principal whole-tree hypothesis and do a small, bounded set of cheap steps.
     Avoids global repeats and huge backtracking. *)
  match goal with
  | [ Hfull: rb_sorted (node _ _ _ _) |- _ ] =>
      let H := fresh "Hfullinv" in pose proof Hfull as H;
      apply rb_sorted_node_inv in H;
      destruct H as [Hgt_v [Hsm_v [Hrb_l Hrb_r]]];
      (* bounded deterministic attempts *)
      try (eapply greater_monotone; [ lia | eassumption ]);
      try (eapply smaller_decrease; [ lia | eassumption ]);
      try (constructor; try eassumption; try (apply recolor_preserves_rb_sorted; eassumption); try lia)
  | _ => idtac
  end.


Ltac finish_balance_step :=
  match goal with
  | [ Hfull: rb_sorted (node _ _ _ _) |- rb_sorted (node ?c ?l ?v ?r) ] =>
    let H := fresh "Hfullinv" in pose proof Hfull as H;
    apply rb_sorted_node_inv in H;
    destruct H as [Hgt_full Hsm_full];
    constructor;
    [ first [ eassumption
            | eapply greater_monotone; [ lia | eassumption ] ]
    | first [ eassumption
            | eapply smaller_decrease; [ lia | eassumption ] ]
    | first [ eassumption
            | (apply recolor_preserves_rb_sorted; eassumption) ]
    | first [ eassumption
            | (apply recolor_preserves_rb_sorted; eassumption) ] ]
  end.

Ltac finish_balance_test := do 6 (try finish_balance_step); try lia.

Lemma balance_case_left_right_sorted :
  forall a x b y c v r,
    rb_sorted (node Black (node Red a x (node Red b y c)) v r) ->
    rb_sorted (node Red (node Black a x b) y (node Black c v r)).
Admitted.

Lemma balance_case_right_left_sorted :
  forall l a x b y c v,
    rb_sorted (node Black l v (node Red (node Red a x b) y c)) ->
    rb_sorted (node Red (node Black l v a) x (node Black b y c)).
Admitted.

Lemma balance_case_right_right_sorted :
  forall l a x b y c v,
    rb_sorted (node Black l v (node Red a x (node Red b y c))) ->
    rb_sorted (node Red (node Black l v a) x (node Black b y c)).
Admitted.

Lemma balance_black_ll_compute :
  forall a x b y c v r,
    balance (node Black (node Red (node Red a x b) y c) v r) =
    node Red (node Black a x b) y (node Black c v r).
Proof. intros; simpl; reflexivity. Qed. 

Lemma balance_red_root_identity :
  forall l v r, balance (node Red l v r) = node Red l v r.
Proof. intros; simpl. reflexivity. Qed.

Lemma balance_black_lr_compute :
  forall a x b y c v r,
    balance (node Black (node Red a x (node Red b y c)) v r) =
    node Red (node Black a x b) y (node Black c v r).
Proof. 
  intros.
  destruct a; simpl.
  - reflexivity.
  - destruct c0; simpl.
    + (* a = node Black*) reflexivity.
    + (* a = node Red *) 
      destruct b; simpl; admit.
Admitted.

Lemma balance_black_rl_compute :
  forall l a x b y c v,
    balance (node Black l v (node Red (node Red a x b) y c) ) =
    node Red (node Black l v a) x (node Black b y c).
Proof. intros. destruct l; try(destruct l1); try(destruct c0). simpl; try reflexivity. simpl. Admitted.

Lemma balance_black_rr_compute :
  forall l a x b y c v,
    balance (node Black l v (node Red a x (node Red b y c))) =
    node Red (node Black l v a) x (node Black b y c).
Proof. intros; simpl. Admitted.


Ltac finish_balance_goal Hfull :=
    match type of Hfull with
    | rb_sorted (node Red ?l' ?v' ?r') =>
        rewrite (balance_red_root_identity l' v' r'); eauto
    | rb_sorted (node Black (node Red (node Red ?a ?x ?b) ?y ?c1) ?v' ?r') =>
        rewrite (balance_black_ll_compute a x b y c1 v' r');
        apply balance_case_left_left_sorted; eauto
    | rb_sorted (node Black (node Red ?a ?x (node Red ?b ?y ?c1)) ?v' ?r') =>
        rewrite (balance_black_lr_compute a x b y c1 v' r');
        apply balance_case_left_right_sorted; eauto
    | rb_sorted (node Black ?l' ?v' (node Red (node Red ?a ?x ?b) ?y ?c1)) =>
        rewrite (balance_black_rl_compute l' a x b y c1 v');
        apply balance_case_right_left_sorted; eauto
    | rb_sorted (node Black ?l' ?v' (node Red ?a ?x (node Red ?b ?y ?c1))) =>
        rewrite (balance_black_rr_compute l' a x b y c1 v');
        apply balance_case_right_right_sorted; eauto
    | rb_sorted ?T =>
        let TT := constr:(T) in change (rb_sorted (balance TT)) with (rb_sorted TT); eauto
    end.

Ltac solve_non_rotation_goal :=
  match goal with
  | [ |- rb_sorted (node Black leaf ?v (node Red ?rl_l ?rl_v (node Red ?rl_r ?rv_r leaf))) ] =>
      (* Goal 1: tree structure doesn't match rotation patterns *)
      constructor; [
        constructor |  (* greater v leaf *)
        constructor; [ lia | constructor | constructor; [ lia | constructor | constructor ] ] |
        constructor |  (* rb_sorted leaf *)
        constructor; [ lia | constructor | constructor; [ lia | constructor | constructor ] ]
      ]
  | [ |- rb_sorted (node Black leaf ?v (node Red ?rl_l ?rl_v (node Red ?rl_r ?rv_r (node Black ?rr_l ?rr_v ?rr_r)))) ] =>
      (* Goal 2: similar structure *)
      constructor; [
        constructor |
        constructor; [ lia | constructor | constructor; [ lia | constructor | constructor ] ] |
        constructor |
        constructor; [ lia | constructor | constructor; [ lia | constructor | constructor ] ]
      ]
  | [ |- rb_sorted (node Black leaf ?v (node Red ?rl_l ?rl_v (node Red ?rl_r ?rv_r (node Red ?rr_l ?rr_v ?rr_r)))) ] =>
      (* Goal 3: similar structure *)
      constructor; [
        constructor |
        constructor; [ lia | constructor | constructor; [ lia | constructor | constructor ] ] |
        constructor |
        constructor; [ lia | constructor | constructor; [ lia | constructor | constructor ] ]
      ]
  | _ => 
      (* fallback: try to construct manually using available hypotheses *)
      constructor; try assumption; try constructor; try lia
  end.

Ltac solve_rb_sorted_components :=
  repeat (
    first [
      (* extract from smaller v (node Red (node Red rl_l rl_v rl_r) rv_r leaf) *)
      match goal with
      | [ H: smaller ?v (node Red (node Red ?rl_l ?rl_v ?rl_r) ?rv_r ?rr) |- ?v < ?rl_v ] =>
          apply smaller_node_inv in H as [_ [H_left _]];
          apply smaller_node_inv in H_left as [Hlt _]; exact Hlt
      | [ H: smaller ?v (node Red (node Red ?rl_l ?rl_v ?rl_r) ?rv_r ?rr) |- smaller ?v ?rl_l ] =>
          apply smaller_node_inv in H as [_ [H_left _]];
          apply smaller_node_inv in H_left as [_ [Hsm _]]; exact Hsm
      | [ H: smaller ?v (node Red (node Red ?rl_l ?rl_v ?rl_r) ?rv_r ?rr) |- smaller ?v (node Red ?rl_r ?rv_r ?rr) ] =>
          apply smaller_node_inv in H as [_ [H_left H_right]];
          apply smaller_node_inv in H_left as [_ [_ Hsm_rl_r]];
          constructor; [lia | exact Hsm_rl_r | exact H_right]
      (* extract from rb_sorted (node Red (node Red rl_l rl_v rl_r) rv_r leaf) *)
      | [ H: rb_sorted (node Red (node Red ?rl_l ?rl_v ?rl_r) ?rv_r ?rr) |- greater ?rl_v ?rl_l ] =>
          apply rb_sorted_node_inv in H as [H_left _];
          apply rb_sorted_node_inv in H_left as [Hgt _]; exact Hgt
      | [ H: rb_sorted (node Red (node Red ?rl_l ?rl_v ?rl_r) ?rv_r ?rr) |- smaller ?rl_v (node Red ?rl_r ?rv_r ?rr) ] =>
          apply rb_sorted_node_inv in H as [H_left [Hsm _]];
          apply rb_sorted_node_inv in H_left as [_ [Hsm_inner _]];
          constructor; [lia | exact Hsm_inner | exact Hsm]
      | [ H: rb_sorted (node Red (node Red ?rl_l ?rl_v ?rl_r) ?rv_r ?rr) |- rb_sorted ?rl_l ] =>
          apply rb_sorted_node_inv in H as [H_left _];
          apply rb_sorted_node_inv in H_left as [_ [_ [Hrb _]]]; exact Hrb
      | [ H: rb_sorted (node Red (node Red ?rl_l ?rl_v ?rl_r) ?rv_r ?rr) |- rb_sorted (node Red ?rl_r ?rv_r ?rr) ] =>
          apply rb_sorted_node_inv in H as [H_left [Hsm [H_inner Hrb_rr]]];
          apply rb_sorted_node_inv in H_left as [_ [_ [_ Hrb_rl_r]]];
          constructor; [lia | exact Hsm | exact Hrb_rl_r | exact Hrb_rr]
      (* fallback tactics *)
      | [ |- _ < _ ] => lia
      | [ |- smaller _ _ ] => constructor; try lia
      | [ |- greater _ _ ] => constructor; try lia  
      | [ |- rb_sorted _ ] => constructor; try assumption
      end
      ]
    );
  try assumption;
  try lia.
  
Ltac extract_rb_sorted_facts :=
  repeat match goal with
  | [ H: smaller ?v (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- ?rv_r > ?v ] =>
      apply smaller_node_inv in H as [Hlt _]; lia
  | [ H: smaller ?v (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- ?rv_r < ?rr_v ] =>
      apply smaller_node_inv in H as [_ [_ Hsm_right]];
      apply smaller_node_inv in Hsm_right as [Hlt _]; exact Hlt
  | [ H: smaller ?v (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- smaller ?rv_r ?rr_l ] =>
      apply smaller_node_inv in H as [_ [_ Hsm_right]];
      apply smaller_node_inv in Hsm_right as [_ [Hsm _]]; exact Hsm
  | [ H: smaller ?v (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- smaller ?rv_r ?rr_r ] =>
      apply smaller_node_inv in H as [_ [_ Hsm_right]];
      apply smaller_node_inv in Hsm_right as [_ [_ Hsm]]; exact Hsm
  | [ H: rb_sorted (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- greater ?rr_v ?rr_l ] =>
      apply rb_sorted_node_inv in H as [_ [_ [_ Hrb_right]]];
      apply rb_sorted_node_inv in Hrb_right as [Hgt _]; exact Hgt
  | [ H: rb_sorted (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- smaller ?rr_v ?rr_r ] =>
      apply rb_sorted_node_inv in H as [_ [_ [_ Hrb_right]]];
      apply rb_sorted_node_inv in Hrb_right as [_ [Hsm _]]; exact Hsm
  | [ H: rb_sorted (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- rb_sorted ?rr_l ] =>
      apply rb_sorted_node_inv in H as [_ [_ [_ Hrb_right]]];
      apply rb_sorted_node_inv in Hrb_right as [_ [_ [Hrb _]]]; exact Hrb
  | [ H: rb_sorted (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- rb_sorted ?rr_r ] =>
      apply rb_sorted_node_inv in H as [_ [_ [_ Hrb_right]]];
      apply rb_sorted_node_inv in Hrb_right as [_ [_ [_ Hrb]]]; exact Hrb
  | [ |- rb_sorted (match ?c with Black => _ | Red => _ end) ] =>
      destruct c; solve_non_rotation_goal
  | [ |- _ ] => solve_non_rotation_goal
  end. 
Ltac solve_all_rb_sorted_goals :=
  repeat (first [
    (* Use existing hypotheses directly *)
    assumption |
    (* Extract facts from Hsm_v *)
    match goal with
    | [ H: smaller ?v (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- ?rv_r > ?v ] =>
        apply smaller_node_inv in H as [Hlt _]; exact Hlt
    | [ H: smaller ?v (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- ?rv_r < ?rr_v ] =>
        apply smaller_node_inv in H as [_ [_ Hsm_right]];
        apply smaller_node_inv in Hsm_right as [Hlt _]; exact Hlt
    | [ H: smaller ?v (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- smaller ?rv_r ?rr_l ] =>
        apply smaller_node_inv in H as [_ [_ Hsm_right]];
        apply smaller_node_inv in Hsm_right as [_ [Hsm _]]; exact Hsm
    | [ H: smaller ?v (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- smaller ?rv_r ?rr_r ] =>
        apply smaller_node_inv in H as [_ [_ Hsm_right]];
        apply smaller_node_inv in Hsm_right as [_ [_ Hsm]]; exact Hsm
    (* Extract facts from Hrb_r *)
    | [ H: rb_sorted (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- greater ?rr_v ?rr_l ] =>
        apply rb_sorted_node_inv in H as [_ [_ [_ Hrb_right]]];
        apply rb_sorted_node_inv in Hrb_right as [Hgt _]; exact Hgt
    | [ H: rb_sorted (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- smaller ?rr_v ?rr_r ] =>
        apply rb_sorted_node_inv in H as [_ [_ [_ Hrb_right]]];
        apply rb_sorted_node_inv in Hrb_right as [_ [Hsm _]]; exact Hsm
    | [ H: rb_sorted (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- rb_sorted ?rr_l ] =>
        apply rb_sorted_node_inv in H as [_ [_ [_ Hrb_right]]];
        apply rb_sorted_node_inv in Hrb_right as [_ [_ [Hrb _]]]; exact Hrb
    | [ H: rb_sorted (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- rb_sorted ?rr_r ] =>
        apply rb_sorted_node_inv in H as [_ [_ [_ Hrb_right]]];
        apply rb_sorted_node_inv in Hrb_right as [_ [_ [_ Hrb]]]; exact Hrb
    (* Handle goals that mention rl_* variables that don't exist in context *)
    | [ |- _ > _ ] => lia
    | [ |- smaller _ _ ] => constructor; try lia; try assumption
    | [ |- greater _ _ ] => constructor; try lia; try assumption
    | [ |- rb_sorted _ ] => constructor; try assumption
    end
  ]);
  try lia.

Ltac inv_all :=
  repeat match goal with
  | H : rb_sorted (node _ _ _ _) |- _ =>
      apply rb_sorted_node_inv in H; destruct H as [? [? [? ?]]]
  | H : greater _ (node _ _ _ _) |- _ =>
      apply greater_node_inv in H; destruct H as [? [? ?]]
  | H : smaller _ (node _ _ _ _) |- _ =>
      apply smaller_node_inv in H; destruct H as [? [? ?]]
  end.

Ltac rb_constructor :=
  constructor; try assumption;
  try (eapply greater_monotone; [lia | eassumption]);
  try (eapply smaller_decrease; [lia | eassumption]);
  try assumption.

Ltac solve_balance_by_shape :=
  (* Red root → identity *)
  match goal with
  | [ H : rb_sorted (node Red ?l ?v ?r) |- _ ] =>
      rewrite (balance_red_root_identity l v r);
      rb_constructor
  end ||

  (* Left-left case *)
  match goal with
  | [ H : rb_sorted (node Black (node Red (node Red ?a ?x ?b) ?y ?c) ?v ?r) |- _ ] =>
      rewrite (balance_black_ll_compute a x b y c v r);
      apply balance_case_left_left_sorted; assumption
  end ||

  (* Left-right case *)
  match goal with
  | [ H : rb_sorted (node Black (node Red ?a ?x (node Red ?b ?y ?c)) ?v ?r) |- _ ] =>
      rewrite (balance_black_lr_compute a x b y c v r);
      apply balance_case_left_right_sorted; assumption
  end ||

  (* Right-left case *)
  match goal with
  | [ H : rb_sorted (node Black ?l ?v (node Red (node Red ?a ?x ?b) ?y ?c)) |- _ ] =>
      rewrite (balance_black_rl_compute l a x b y c v);
      apply balance_case_right_left_sorted; assumption
  end ||

  (* Right-right case *)
  match goal with
  | [ H : rb_sorted (node Black ?l ?v (node Red ?a ?x (node Red ?b ?y ?c))) |- _ ] =>
      rewrite (balance_black_rr_compute l a x b y c v);
      apply balance_case_right_right_sorted; assumption
  end.

Ltac solve_balance :=
  intros t Hsorted; destruct t; simpl; try constructor;
  rename c into col;

  (* non-leaf *)
  inv_all;
  destruct col; simpl;
  try solve_balance_by_shape;
  (* If none of the rotation patterns matched: identity *)
  rb_constructor.



(* Lemma skeletons to prove *)
Lemma balance_preserves_sorted:
  forall t, rb_sorted t -> rb_sorted (balance t).
Proof.
  intros [| c l v r] H.
  - constructor.
  - pose proof H as Hfull. (*NECCESARY!! without this it cant do the later cases - keeps full original hyp*)   
    destruct c.
    + (*Black root*)
      apply rb_sorted_node_inv in H as [Hgt_v [Hsm_v [Hrb_l Hrb_r]]].
      destruct l as [| cl ll lv_l lr]; destruct r as [| cr rl rv_r rr]; simpl; eauto.
      * destruct cr; eauto.
        destruct rl as [| rl_c rl_l rl_v rl_r]; 
        destruct rr as [| rr_c rr_l rr_v rr_r];
        simpl; try assumption; try solve_rb_sorted_components; finish_balance_goal Hfull;
        try(destruct rl_c); eauto;
        try(destruct rr_c); eauto;
        simpl; try assumption; try solve_rb_sorted_components; try solve_non_rotation_goal; try extract_rb_sorted_facts; 
        finish_balance_goal Hfull; solve_all_rb_sorted_goals; eauto. admit.
      * destruct cl; eauto.
       destruct ll as [| llc lll lvl llr]; simpl; eauto.
       -- destruct lr; eauto.
          destruct c; eauto.
          try solve_non_rotation_goal; finish_balance_goal Hfull; eauto; admit.
       --  match goal with
             | [ Hfull : rb_sorted (node Black (node Red (node Red ?a ?x ?b) ?y ?c1) ?v ?r) |- _ ] =>
                 apply balance_case_left_left_sorted; eauto
             | [ Hfull : rb_sorted (node Black (node Red ?a ?x (node Red ?b ?y ?c1)) ?v ?r) |- _ ] =>
                 apply balance_case_left_right_sorted; eauto
             | _ => eauto
             end.
          admit.
      * destruct cl; eauto.
       destruct ll as [| llc lll lvl llr]; simpl; eauto.
    + (*Red root*)
    inv H.
      simpl.
      match goal with
      | [ Hfull: rb_sorted (node Black (node Red (node Red ?a ?x ?b) ?y ?c1) ?v ?r) |- _ ] =>
          apply balance_case_left_left_sorted; exact Hfull
      | [ Hfull: rb_sorted (node Black (node Red ?a ?x (node Red ?b ?y ?c1)) ?v ?r) |- _ ] =>
          apply balance_case_left_right_sorted; exact Hfull
      | [ Hfull: rb_sorted (node Black ?l ?v (node Red (node Red ?a ?x ?b) ?y ?c1)) |- _ ] =>
          apply balance_case_right_left_sorted; exact Hfull
      | [ Hfull: rb_sorted (node Black ?l ?v (node Red ?a ?x (node Red ?b ?y ?c1))) |- _ ] =>
          apply balance_case_right_right_sorted; exact Hfull
      | _ =>
          (* none of the rotation shapes: balance returns t unchanged *)
          constructor; eauto
      end.
    
    
    destruct l; destruct r; simpl; try (now constructor).
    +  (* Black, l = node Red (node Red a x b) y c1 *)
      destruct c; simpl; try constructor; try assumption.
      destruct r1; try (now constructor);try assumption.
      * destruct r2;  try (now constructor);try assumption;
        destruct c; simpl; try constructor; try eauto.
        inversion H5; clear H5; subst.                     (* yields v < n and smaller v ... *)
        inversion H7; clear H7; subst.                     (* yields greater n leaf, smaller n (node Red r2_1 n0 r2_2), rb_sorted (node Red r2_1 n0 r2_2) *)
        inversion H3; clear H3; subst.
        (* build rb_sorted for node Red (node Black a x b) y (node Black c1 v (node Black r2_1 n0 r2_2)) *)  
        -- constructor; try lia; try constructor. 
        -- constructor; try lia; try constructor.
        -- constructor; try eauto; 
        inversion H5; subst; clear H5.
        inversion H7; subst; clear H7.
        inversion H3; subst; clear H3.
        inversion H8 as [| Hlt Hsm_l Hsm_r].
          ++ assumption.
          ++ inversion H8; subst. eauto.
          ++ inversion H10 as [| Hlt Hsm_l Hsm_r]; subst. 
             inversion H7 as [ | Hgt Hsm Hrb_l Hrb_r]; subst; clear H7. 
             inversion H5 as [ | Hgt Hsm Hrb_l Hrb_r]; subst; clear H5. eauto.
          ++ inversion H10 as [| Hlt Hsm_l Hsm_r]; subst. 
             inversion H7 as [ | Hgt Hsm Hrb_l Hrb_r]; subst; clear H7. 
             inversion H5 as [ | Hgt Hsm Hrb_l Hrb_r]; subst; clear H5. eauto.
        -- constructor; try (inversion H7; subst; clear H7;
            inversion H10; subst; clear H10;
            assumption ).
      * destruct c;  try (now constructor);try assumption.
      destruct r2; simpl; try constructor; try eauto.
      destruct c; simpl; try constructor; try eauto.
      inversion H5; clear H5; subst.   
      inversion H7; clear H7; subst.   
      inversion H3; clear H3; subst; try eauto.
        --  inversion H7 as [| ? ? ? ? Hgt_outer Hsm_outer Hrb_l Hrb_r]; subst; clear H7.
              inversion Hsm_outer as [| ? ? l' n' r' Hlt Hsm_l Hsm_r]; subst; clear Hsm_outer.
              constructor; try eauto.
        --  apply smaller_node_inv in H5.
            destruct H5 as [Hvlt [Hsm_left Hsm_right]].
            apply rb_sorted_node_inv in H7.
            destruct H7 as [HgtN [HsmN [Hrb_left Hrb_right]]].
            constructor; try eauto.
        -- apply rb_sorted_node_inv in H7.
          destruct H7 as [_ [_ [_ Hrb_r]]].
          exact (recolor_preserves_rb_sorted Red r2_1 n1 r2_2 Hrb_r).
        -- apply rb_sorted_node_inv in H7;
          destruct H7 as [Hgt_n [Hsm_n [Hrb_left Hrb_right]]];
          apply rb_sorted_node_inv in Hrb_left;
          destruct Hrb_left as [Hgt_n0 [Hsm_n0 [Hrb_r11 Hrb_r12]]];
          apply smaller_node_inv in H5;
          destruct H5 as [Hv_lt [Hsm_left Hsm_right]];
          constructor; try eauto. constructor; try eauto; try (constructor; eauto); try (apply smaller_decrease with (n:=n); assumption).
          ++ apply smaller_node_inv in Hsm_left.
             destruct Hsm_left. eauto.
          ++ apply greater_node_inv in Hgt_n.
            destruct Hgt_n. constructor; eauto.
            apply smaller_decrease with (m:=n0) (n:=n) (t:=r2); [lia | exact Hsm_n].
          ++ apply smaller_node_inv in Hsm_left.
              destruct Hsm_left. destruct H0.
              constructor; try eauto.
          ++ apply greater_node_inv in Hgt_n.
             destruct Hgt_n. destruct H0. constructor; try eauto.
    + destruct c;simpl; try constructor; try assumption.
      destruct l1. 
      *   inv H6. inv H8. apply node_sorted; try eauto. 
          --  destruct c. inv H10. inv H12. eauto. 
              assert (HR : rb_sorted (node Black (node c l0 v1 r0) v0 r)).
              { constructor; eauto. }
              assert (Hsm_n : smaller n (node Black (node c l0 v1 r0) v0 r)).
              { constructor; eauto. }
              assert (HL : rb_sorted (node Red leaf n (node Black (node c l0 v1 r0) v0 r))).
              { constructor; eauto. }
              assert (L : rb_sorted (node Black leaf n (node c l0 v1 r0))).
              { constructor; eauto. }
              assert (R : rb_sorted (node Black r v leaf)).
              { constructor; eauto. admit. }
              ++ constructor; eauto.
              ++ simpl. constructor; eauto;
              apply rb_sorted_node_inv in H10;
              destruct H10 as [Hgt_v0_l [Hsm_v0_r [Hrb_l Hrb_r]]];
              
              apply greater_node_inv in H4;
              destruct H4 as [Hv_gt_n [Hv_g_left Hv_g_right]];
              apply greater_node_inv in Hv_g_right;
              destruct Hv_g_right as [Hv_gt_v0 [Hv_g_l Hv_g_r]]; try eauto. 
        * destruct c; simpl; destruct l2; try constructor; eauto. 
          --  admit.
          -- simpl. constructor; try eauto;
              apply rb_sorted_node_inv in H6;
              destruct H6 as [Hgt_v0_l [Hsm_v0_r [Hrb_l Hrb_r]]];
              apply greater_node_inv in H4;
              destruct H4 as [Hv_gt_n [Hv_g_left Hv_g_right]];
              apply greater_node_inv in Hgt_v0_l;
              destruct Hgt_v0_l, H0; assumption.
          --  apply rb_sorted_node_inv in H6; destruct H6, H0, H1;
              apply greater_node_inv in H4; destruct H4;
              constructor; assumption. 
          --  constructor;
              apply rb_sorted_node_inv in H6; destruct H6, H0, H1;
              apply rb_sorted_node_inv in H1; destruct H1, H3, H6;
              assumption.
          --  constructor;
              apply rb_sorted_node_inv in H6;
              destruct H6 as [Hgt_v0_l [Hsm_v0_r [Hrb_l Hrb_r]]];
              apply greater_node_inv in H4;
              destruct H4 as [Hv_gt_n [Hv_g_left Hv_g_right]];
              apply greater_node_inv in Hgt_v0_l;
              destruct Hgt_v0_l, H0; assumption.
          -- constructor;
              apply rb_sorted_node_inv in H6;
              destruct H6 as [Hgt_v0_l [Hsm_v0_r [Hrb_l Hrb_r]]];
              apply greater_node_inv in H4;
              destruct H4 as [Hv_gt_n [Hv_g_left Hv_g_right]];
              apply greater_node_inv in Hgt_v0_l;
              destruct Hgt_v0_l, H0; admit.
          -- constructor;
              apply rb_sorted_node_inv in H6; destruct H6, H0, H1;
              apply rb_sorted_node_inv in H1; destruct H1, H3, H6;
              assumption.
          -- constructor;
              apply rb_sorted_node_inv in H6;
              destruct H6 as [Hgt_v0_l [Hsm_v0_r [Hrb_l Hrb_r]]];
              apply greater_node_inv in H4;
              destruct H4 as [Hv_gt_n [Hv_g_left Hv_g_right]];
              apply greater_node_inv in Hgt_v0_l;
              destruct Hgt_v0_l, H0; assumption.     
    + destruct c; destruct l1; destruct l2; simpl.
      * destruct c0; destruct r1; try constructor; try eauto.
        -- destruct r2; try (destruct c); apply node_sorted; try eauto;
           apply rb_sorted_node_inv in H7; destruct H7, H0, H1; try assumption;
           try (constructor; apply rb_sorted_node_inv in H2; destruct H2, H3, H7; assumption);
          inv H0; constructor; try constructor; eauto; apply greater_node_inv in H4; destruct H4, H3;
          apply smaller_node_inv in H5; destruct H5, H2, H7; try lia.  
        -- destruct c; destruct r2; try (destruct c).
            ++ constructor; try assumption.
            ++ constructor; try assumption.
            ++ constructor; try constructor; try assumption;
              apply rb_sorted_node_inv in H7;
              apply smaller_node_inv in H5;
              apply greater_node_inv in H4;
              destruct H7, H0, H1, H5, H4, H7, H5; try lia; try assumption;
              apply rb_sorted_node_inv in H2;
              destruct H2 as [Hsort1 [Hsort2 [Hsort3 Hsort4]]];
              try assumption;
              apply smaller_node_inv in H0;
              destruct H0, H2; try assumption.
              constructor; try lia; eauto.
            ++ constructor; try constructor; try assumption;
              apply rb_sorted_node_inv in H7;
              apply smaller_node_inv in H5;
              apply greater_node_inv in H4;
              destruct H7, H0, H1, H5, H4, H7, H5; try lia; try assumption;
              apply rb_sorted_node_inv in H1;
              destruct H1 as [Hsort1 [Hsort2 [Hsort3 Hsort4]]];
              try assumption;
              apply smaller_node_inv in H5;
              destruct H5, H5;
              try constructor;
              apply greater_node_inv in H; destruct H, H11;
              try lia; eauto.
            ++ constructor; try constructor; try assumption;
              apply rb_sorted_node_inv in H7;
              apply smaller_node_inv in H5;
              apply greater_node_inv in H4;
              destruct H7, H0, H1, H5, H4, H7, H5; try lia; try assumption;
              apply rb_sorted_node_inv in H1;
              destruct H1 as [Hsort1 [Hsort2 [Hsort3 Hsort4]]];
              try assumption;
              apply smaller_node_inv in H5;
              destruct H5, H5; try lia;
              try constructor;
              apply greater_node_inv in H; destruct H, H11;
              try lia; eauto;
              apply smaller_node_inv in H0;
              destruct H0, H13; try lia;
              eapply smaller_decrease; eauto.
           ++  constructor; try constructor; try assumption;
              apply rb_sorted_node_inv in H7;
              apply smaller_node_inv in H5;
              apply greater_node_inv in H4;
              destruct H7, H0, H1, H5, H4, H7, H5; try lia; try assumption;
              apply rb_sorted_node_inv in H1;
              destruct H1 as [Hsort1 [Hsort2 [Hsort3 Hsort4]]];
              try assumption;
              apply smaller_node_inv in H5;
              destruct H5, H5; try lia;
              try constructor;
              apply greater_node_inv in H; destruct H, H11;
              try lia; eauto;
              apply smaller_node_inv in H0;
              destruct H0, H13; try lia;
              eapply smaller_decrease; eauto.
      * destruct c0.
        -- (* c0 = Black: straightforward *)
          simpl. apply node_sorted; try assumption.
        -- (* c0 = Red: need to inspect r1,r2 *)
          destruct r1; destruct r2; simpl.
          ++ (* r1 = leaf, r2 = leaf *)
            constructor; try assumption.
          ++ (* r1 = leaf, r2 = node Red c1 v0 r : rotation case *)
            (* expose components of the right rb_sorted and left rb_sorted *)
            apply rb_sorted_node_inv in H7 as [Hgt_n0 [Hsm_n0 [Hrb_r1 Hrb_r2]]].
            apply rb_sorted_node_inv in H6 as [Hgt_left [Hsm_left [Hrb_ll Hrb_lr]]].
            destruct c0; simpl.
            ** (* c0 = Black *)
              apply rb_sorted_node_inv in Hfull as [Hgt_root [Hsm_root [Hrb_left Hrb_right]]].
              constructor; try assumption.
            **(* c0 = Red *)
              apply rb_sorted_node_inv in Hfull as [Hgt_root [Hsm_root [Hrb_left Hrb_right]]].
              apply rb_sorted_node_inv in Hrb_right as [Hgt_n1 [Hsm_n1 [Hrb_r3 Hrb_r4]]].
              (* now build the rotated node *)
              constructor; eauto.
                --- constructor;
                    apply rb_sorted_node_inv in Hrb_left as [Hgt_left1 [Hsm_left1 [Hrb_ll1 Hrb_lr1]]]; eauto; 
                    apply smaller_node_inv in H5. destruct H5 as [Hv_lt_n0 _];
                    lia.
                    apply (greater_monotone n0 v (node Black leaf n (node c l2_1 n1 l2_2))); try lia.
                    assumption. 
                --- constructor;
                    apply smaller_node_inv in Hsm_n1 as [Hv_lt_n0 [Hsm_inner1 Hsm_inner2]]; assumption.
                --- constructor; apply rb_sorted_node_inv in Hrb_r2  as [Hgt_n2 [Hsm_n2 [Hrb_r5 Hrb_r6]]]; assumption.
          ++ destruct c0; simpl; eauto; 
            apply rb_sorted_node_inv in Hfull as [Hgt_root [Hsm_root [Hrb_left Hrb_right]]].
            (* Hrb_right : rb_sorted (node Red (node Red r1_1 n2 r1_2) n0 leaf) *)
            apply rb_sorted_node_inv in Hrb_right as [Hgt_n0 [Hsm_n0 [Hrb_rl Hrb_rr]]].
            apply rb_sorted_node_inv in Hrb_rl as [Hgt_n2 [Hsm_n2 [Hrb_r11 Hrb_r12]]].
            (* get v < n2 from Hsm_root *)
            apply smaller_node_inv in Hsm_root as [Hv_lt_n0 [Hsm_inner1 Hsm_inner2]]. 
            apply smaller_node_inv in Hsm_inner1 as [Hv_lt_n2 [Hsm_r11 Hsm_r12]].
            apply greater_monotone with (n:=v) (m:=n2) in Hgt_root; [| lia].
            constructor; try (constructor; eauto). 
            ** inversion Hgt_n0. lia.
            ** apply greater_node_inv in Hgt_n0 as [Hv_gt_n0 [Hsm_inner3 Hsm_inner4]]. assumption.
          ++ destruct c0; destruct c1; simpl; eauto;
            apply rb_sorted_node_inv in Hfull as [Hgt_root [Hsm_root [Hrb_left Hrb_right]]];
            apply rb_sorted_node_inv in Hrb_right as [Hgt_n0 [Hsm_n0 [Hrb_rleft Hrb_rright]]];
            apply smaller_node_inv in Hsm_root as [Hv_lt_n0 _];
            pose proof (greater_monotone n0 v (node Black leaf n (node c l2_1 n1 l2_2)) Hv_lt_n0 H4) as Hgt_n0_left;
            inv Hsm_n0; apply smaller_node_inv in H5 as [Hv_lt_n1 [Hsm_v_rleft Hsm_v_rright]].
            ** apply rb_sorted_node_inv in Hrb_rright as [Hgt_n3_rleft [Hsm_n3_rright [Hrb_r21 Hrb_r22]]];
              constructor; try ( constructor; eauto).
            ** apply rb_sorted_node_inv in Hrb_rleft as [Hgt_n2_r1[ Hsm_n2_r12 [Hrb_r11 Hrb_r12]]].
                apply smaller_node_inv in Hsm_v_rleft as [Hv_lt_n2 [Hsm_v_r11 Hsm_v_r12]].
                apply greater_node_inv in Hgt_root as [Hv_gt_n [Hv_g_left Hv_g_right]].
                apply greater_node_inv in Hgt_n0 as [Hn0_gt_n2 [Hn0_g_r1_1 Hn0_g_r1_2]].
                constructor; try (constructor; eauto); try (exact (greater_monotone n2 v (node Black leaf n (node c l2_1 n1 l2_2)) Hv_lt_n2 H4)).
                --- constructor; try lia; eapply smaller_decrease; eauto. 
            **apply rb_sorted_node_inv in Hrb_rleft as [Hgt_n2_r1 [Hsm_n2_r12 [Hrb_r11 Hrb_r12]]].
              (* v < n2 from smaller v (node Red r1_1 n2 r1_2) *)
              apply smaller_node_inv in Hsm_v_rleft as [Hv_lt_n2 [Hsm_v_r11 Hsm_v_r12]].
              pose proof (greater_monotone n2 v (node Black leaf n (node c l2_1 n1 l2_2)) Hv_lt_n2 H4) as Hgt_n2_left.
              apply rb_sorted_node_inv in H7 as [Hgt_n0_full [Hsm_n0_right [Hrb_rleft' Hrb_rright']]].
              apply greater_node_inv in Hgt_n0 as [Hn0_gt_n2 [Hn0_g_r11 Hn0_g_r12]].
              pose proof (smaller_decrease n2 n0 (node Red r2_1 n3 r2_2) Hn0_gt_n2 Hsm_n0_right) as Hsm_n2_rright.
              constructor; try (constructor; eauto). 
      * destruct c0; destruct r1; destruct r2; try (destruct c0); eauto;
        apply smaller_node_inv in H5 as [Hv_lt_n0 _];
        pose proof (greater_monotone n0 v (node Black (node c l1_1 n1 l1_2) n leaf) Hv_lt_n0 H4) as Hgt_n0_left;
        apply rb_sorted_node_inv in H7 as [Hgt_n0_leaf [Hsm_n0_right [Hrb_leaf Hrb_rright]]];
        try (apply smaller_node_inv in Hsm_n0_right as [Hn0_lt_n2 [Hsm_n0_r21 Hsm_n0_r22]]).
        --- constructor; try (constructor; eauto);
            apply rb_sorted_node_inv in Hrb_rright as [Hgt_n1 [Hsm_n1_right [Hrb_leaf1 Hrb_rright1]]]; assumption.
        --- apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [Hrb_left Hrb_right]]].
            apply smaller_node_inv in Hsm_v as [Hv_lt_n1 [Hsm_v_right Hsm_v_leaf]].
            apply smaller_node_inv in Hsm_v_right as [Hv_lt_n2 [Hsm_v_r11 Hsm_v_r12]].
            apply rb_sorted_node_inv in Hrb_leaf as [Hgt_n2 [Hsm_n2 [Hrb_r11 Hrb_r12]]].
            apply greater_node_inv in Hgt_n0_leaf as [Hn0_gt_n2 [Hn0_g_r11 Hn0_g_r12]].
            constructor; try(constructor; eauto). apply greater_monotone with (n:=v); eauto.
        --- destruct c1; eauto.
            apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [Hrb_left Hrb_right]]].
            apply smaller_node_inv in Hsm_v as [Hv_lt_n2 [Hsm_v_r11 Hsm_v_r12]].
            constructor; try (constructor; eauto);
            apply rb_sorted_node_inv in Hrb_rright as [Hgt_n1 [Hsm_n1_right [Hrb_leaf1 Hrb_rright1]]]; try assumption.
        --- apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [Hrb_left Hrb_right]]].
            apply smaller_node_inv in Hsm_v as [Hv_lt_n1 [Hsm_v_right Hsm_v_leaf]].
            apply smaller_node_inv in Hsm_v_right as [Hv_lt_n2 [Hsm_v_r11 Hsm_v_r12]].
            apply rb_sorted_node_inv in Hrb_leaf as [Hgt_n2 [Hsm_n2 [Hrb_r11 Hrb_r12]]].
            apply greater_node_inv in Hgt_n0_leaf as [Hn0_gt_n2 [Hn0_g_r11 Hn0_g_r12]].
            constructor; try(constructor; eauto). apply greater_monotone with (n:=v); eauto.
            constructor; try lia; eapply smaller_decrease; eauto.
      * destruct c0; destruct r1; destruct r2; try (destruct c0); try (destruct c2); eauto;
        apply smaller_node_inv in H5 as [Hv_lt_n0 [Hsm_v_left Hsm_v_right]];
        apply rb_sorted_node_inv in H7 as [Hgt_n0 [Hsm_n0 [Hrb_rleft Hrb_rright]]];
        try (apply rb_sorted_node_inv in Hrb_rleft as [Hgt_n3_r1 [Hsm_n3_r1 [Hrb_r11 Hrb_r12]]]);
        pose proof (greater_monotone n0 v _ Hv_lt_n0 H4) as Hgt_n0_left.
        apply smaller_node_inv in Hsm_n0 as [Hv_lt_n1 [Hsm_v_left1 Hsm_v_right1]];
        apply rb_sorted_node_inv in Hrb_rright as [Hgt_n1 [Hsm_n1 [Hrb_rleft1 Hrb_rright1]]];
        constructor; eauto; try(constructor; eauto); try(apply smaller_node_inv in Hsm_n0 as [Hv_lt_n1 [Hsm_v_left1 Hsm_v_right1]]; assumption).
        ++ apply smaller_node_inv in Hsm_v_left as [Hv_lt_n3 [Hsm_v_r11 Hsm_v_r12]].
          apply greater_node_inv in Hgt_n0 as [Hn0_gt_n3 [Hn0_g_r11 Hn0_g_r12]].
          pose proof (greater_monotone n3 v (node Black (node c l1_1 n1 l1_2) n (node c1 l2_1 n2 l2_2))Hv_lt_n3 H4) as Hgt_n3_left.
          constructor; try (constructor; eauto).
        ++ apply smaller_node_inv in Hsm_n0 as [Hn0_lt_n4 [Hsm_n0_r21 Hsm_n0_r22]].
           apply rb_sorted_node_inv in Hrb_rright as [Hgt_n1 [Hsm_n1 [Hrb_rleft1 Hrb_rright1]]];
           constructor; try (constructor; eauto).
        ++ apply smaller_node_inv in Hsm_v_left as [Hv_lt_n3 [Hsm_v_r11 Hsm_v_r12]].
          apply greater_node_inv in Hgt_n0 as [Hn0_gt_n3 [Hn0_g_r11 Hn0_g_r12]].
          pose proof (greater_monotone n3 v (node Black (node c l1_1 n1 l1_2) n (node c1 l2_1 n2 l2_2)) Hv_lt_n3 H4) as Hgt_n3_left.
          pose proof (smaller_decrease n3 n0 (node Black r2_1 n4 r2_2) Hn0_gt_n3 Hsm_n0) as Hsm_n3_rright.
          constructor; try (constructor; eauto).
        ++ apply smaller_node_inv in Hsm_v_left as [Hv_lt_n3 [Hsm_v_r11 Hsm_v_r12]].
          pose proof (greater_monotone n3 v (node Black (node c l1_1 n1 l1_2) n (node c1 l2_1 n2 l2_2))Hv_lt_n3 H4) as Hgt_n3_left.
          apply greater_node_inv in Hgt_n0 as [Hn0_gt_n3 [Hn0_g_r11 Hn0_g_r12]].
          pose proof (smaller_decrease n3 n0 (node Red r2_1 n4 r2_2) Hn0_gt_n3 Hsm_n0) as Hsm_n3_rright.
          constructor; try (constructor; eauto).
      * destruct c0; destruct r1; destruct r2; try (destruct c); try (destruct c0); eauto;
        apply smaller_node_inv in H5 as [Hv_lt_n0 [Hsm_v_left Hsm_v_right]];
        apply rb_sorted_node_inv in H7 as [Hgt_n0 [Hsm_n0 [Hrb_rleft Hrb_rright]]].
        ++ apply smaller_node_inv in Hsm_n0 as [Hv_lt_n3 [Hsm_v_r11 Hsm_v_r12]];
          apply rb_sorted_node_inv in Hrb_rright as [Hgt_n1 [Hsm_n1 [Hrb_rleft1 Hrb_rright1]]];
          apply greater_node_inv in H4 as [Hn0_gt_n3 [Hn0_g_r11 Hn0_g_r12]];
          apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [_ _]]];
          apply greater_node_inv in Hgt_v as [Hv_gt_n _];
          apply smaller_node_inv in Hsm_v as [Hv_lt_n1 _];
          constructor; try(constructor; eauto). apply node_greater; [lia | exact Hgt_n0 | exact Hgt_n0].
        ++ apply smaller_node_inv in Hsm_v_left as [Hv_lt_n1 [Hsm_v_r11 Hsm_v_r12]].
           pose proof (greater_monotone n1 v (node Red leaf n leaf) Hv_lt_n1 H4) as Hgt_n1_left.
           apply rb_sorted_node_inv in Hrb_rleft as [Hgt_n1_r1 [Hsm_n1_r2 [Hrb_r11 Hrb_r12]]].
           apply greater_node_inv in Hgt_n0 as [Hn0_gt_n1 [Hn0_g_r11 Hn0_g_r12]].
           constructor; try(constructor; eauto). 
        ++ apply smaller_node_inv in Hsm_n0 as [Hn0_lt_n2 [Hsm_n0_r21 Hsm_n0_r22]].
          apply rb_sorted_node_inv in Hrb_rright as [Hgt_n1 [Hsm_n1 [Hrb_rleft1 Hrb_rright1]]];
           pose proof (greater_monotone n0 v (node Red leaf n leaf) Hv_lt_n0 H4) as Hgt_n0_leftchild.
          constructor; try(constructor; eauto).
        ++ apply smaller_node_inv in Hsm_v_left as [Hv_lt_n1 [Hsm_v_r11 Hsm_v_r12]].
           pose proof (greater_monotone n1 v (node Red leaf n leaf) Hv_lt_n1 H4) as Hgt_n1_left.
           apply rb_sorted_node_inv in Hrb_rleft as [Hgt_n1_r1 [Hsm_n1_r2 [Hrb_r11 Hrb_r12]]].
           apply greater_node_inv in Hgt_n0 as [Hn0_gt_n1 [Hn0_g_r11 Hn0_g_r12]].
           constructor; try(constructor; eauto). apply smaller_decrease with (n:=n0); [ lia | exact Hsm_n0 ].
        ++ apply smaller_node_inv in Hsm_v_left as [Hv_lt_n1 [Hsm_v_r11 Hsm_v_r12]].
           pose proof (greater_monotone n1 v (node Red leaf n leaf) Hv_lt_n1 H4) as Hgt_n1_left.
           apply rb_sorted_node_inv in Hrb_rleft as [Hgt_n1_r1 [Hsm_n1_r2 [Hrb_r11 Hrb_r12]]].
           apply greater_node_inv in Hgt_n0 as [Hn0_gt_n1 [Hn0_g_r11 Hn0_g_r12]].
           constructor; try(constructor; eauto). apply smaller_decrease with (n:=n0); [ lia | exact Hsm_n0 ].
      * destruct c0; destruct r1; destruct r2; try (destruct c); try (destruct c0); try(destruct c1); eauto;
        apply smaller_node_inv in H5 as [Hsmall1 [Hsmall2 Hsmall3]]; apply rb_sorted_node_inv in H7 as [Hn0_gt_n1 [Hn0_g_r11 Hn0_g_r12]];
        apply rb_sorted_node_inv in H6 as [Hgt_n [Hsm_right [Hrb_leaf Hrb_right]]];
        apply rb_sorted_node_inv in Hrb_right as [Hgt_n1 [Hsm_n1 [Hrb_l21 Hrb_l22]]];
        apply smaller_node_inv in Hsm_right as [Hn_lt_n1 [Hsm_n_l21 Hsm_n_l22]];
        apply greater_node_inv in H4 as [Hv_gt_n [Hv_g_leaf Hv_g_right]];
        apply greater_node_inv in Hv_g_right as [Hv_gt_n1 [Hv_g_r21 Hv_g_r22]].
        ++ finish_bal_branch.
        ++ finish_bal_branch.
        ++ finish_bal_branch.
        ++ constructor;try(constructor; eauto); try (apply node_smaller); eauto; try lia.
          --- eapply smaller_decrease; eauto. 
          --- destruct Hn0_g_r12; apply rb_sorted_node_inv in H as [Hsort1 [Hsort2 [Hsort3 Hsort4]]]. constructor; eauto. 
        ++ constructor;try(constructor; eauto); try (apply node_smaller); eauto; try lia.
          --- eapply smaller_decrease; eauto. 
          --- destruct Hn0_g_r12; apply rb_sorted_node_inv in H as [Hsort1 [Hsort2 [Hsort3 Hsort4]]]. constructor; eauto. 
        ++ finish_bal_branch.
        ++ finish_bal_branch.
        ++ finish_bal_branch.
        ++ finish_bal_branch.
        ++ finish_bal_branch. 
        ++ apply smaller_node_inv in Hn0_g_r11 as [Hn0_lt_n2 [Hsm_n0_r21 Hsm_n0_r22]].
           inv Hfull.
           destruct Hn0_g_r12.
           apply rb_sorted_node_inv in H0 as [Hgt_n2 [Hsm_right2 [Hrb_leaf2 Hrb_right2]]].
           pose proof (greater_monotone n0 v (node Red leaf n (node Black l2_1 n1 l2_2)) Hsmall1 H3) as Hgt_n0_left.
           constructor;try(constructor; eauto); try (apply node_smaller); eauto; try lia.
        ++ apply smaller_node_inv in Hn0_g_r11 as [Hn0_lt_n2 [Hsm_n0_r21 Hsm_n0_r22]].
           destruct Hn0_g_r12.
           apply rb_sorted_node_inv in H0 as [Hgt_n2 [Hsm_right2 [Hrb_leaf2 Hrb_right2]]].
           constructor;try(constructor; eauto); try (apply node_smaller); eauto; try lia. eapply smaller_decrease; eauto. 
        ++ apply smaller_node_inv in Hn0_g_r11 as [Hn0_lt_n2 [Hsm_n0_r21 Hsm_n0_r22]].
           destruct Hn0_g_r12.
           apply rb_sorted_node_inv in H0 as [Hgt_n2 [Hsm_right2 [Hrb_leaf2 Hrb_right2]]].
           constructor;try(constructor; eauto); try (apply node_smaller); eauto; try lia. eapply smaller_decrease; eauto. 
        ++ apply smaller_node_inv in Hsmall2 as [Hn0_lt_n2 [Hsm_n0_r21 Hsm_n0_r22]].
           destruct Hn0_g_r12.
           apply rb_sorted_node_inv in H as [Hgt_n2 [Hsm_right2 [Hrb_leaf2 Hrb_right2]]].
           apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [Hrb_left Hrb_right]]].
           apply greater_node_inv in Hn0_gt_n1 as [Hn0_gt_n2 [Hn0_g_r11_g Hn0_g_r12_g]].
           pose proof (greater_monotone n2 v (node Red leaf n (node Black l2_1 n1 l2_2)) Hn0_lt_n2 Hgt_v) as Hgt_n2_tree.
           apply greater_node_inv in Hgt_n2_tree as [_ [_ Hgt_n2_right]].
           apply greater_node_inv in Hgt_n2_right as [Hgt [Hgt_n2_l21 Hgt_n2_l22]].
           constructor;repeat (try(constructor; eauto; try lia)).
        ++ apply smaller_node_inv in Hsmall2 as [Hn0_lt_n2 [Hsm_n0_r21 Hsm_n0_r22]].
           destruct Hn0_g_r12.
           apply rb_sorted_node_inv in H as [Hgt_n2 [Hsm_right2 [Hrb_leaf2 Hrb_right2]]].
           apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [Hrb_left Hrb_right]]].
           apply greater_node_inv in Hn0_gt_n1 as [Hn0_gt_n2 [Hn0_g_r11_g Hn0_g_r12_g]].
           constructor;repeat (try(constructor; eauto; try lia)); try(eapply smaller_decrease); eauto.
        ++ apply smaller_node_inv in Hsmall2 as [Hn0_lt_n2 [Hsm_n0_r21 Hsm_n0_r22]].
           destruct Hn0_g_r12.
           apply rb_sorted_node_inv in H as [Hgt_n2 [Hsm_right2 [Hrb_leaf2 Hrb_right2]]].
           apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [Hrb_left Hrb_right]]].
           apply greater_node_inv in Hn0_gt_n1 as [Hn0_gt_n2 [Hn0_g_r11_g Hn0_g_r12_g]].
           apply smaller_node_inv in Hsm_v as [Hv_lt_n0 [Hsm_v_left Hsm_v_right]].
           apply smaller_node_inv in Hsm_v_left as [Hv_lt_n2 [Hsm_v_r11 Hsm_v_r12]].
           constructor;repeat (try(constructor; eauto; try lia)); try(eapply smaller_decrease); eauto.
        ++ apply smaller_node_inv in Hsmall2 as [Hn0_lt_n2 [Hsm_n0_r21 Hsm_n0_r22]].
           destruct Hn0_g_r12.
           apply rb_sorted_node_inv in H as [Hgt_n2 [Hsm_right2 [Hrb_leaf2 Hrb_right2]]].
           apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [Hrb_left Hrb_right]]].
           apply greater_node_inv in Hn0_gt_n1 as [Hn0_gt_n2 [Hn0_g_r11_g Hn0_g_r12_g]].
           apply smaller_node_inv in Hsm_v as [Hv_lt_n0 [Hsm_v_left Hsm_v_right]].
           apply smaller_node_inv in Hsm_v_left as [Hv_lt_n2 [Hsm_v_r11 Hsm_v_r12]].
           apply rb_sorted_node_inv in Hrb_right as [Hgt_n0_full [Hsm_n0_full [Hrb_r1 Hrb_r2]]].
           apply smaller_node_inv in Hn0_g_r11 as [Hn0_lt_n3 [Hsm_n0_r31 Hsm_n0_r32]].
           pose proof (greater_monotone n0 v (node Red leaf n (node Black l2_1 n1 l2_2)) Hsmall1 Hgt_v) as Hn0_leftpart.
           assert (Hn0_r1: greater n0 (node Black r1_1 n2 r1_2)).
           { apply node_greater; eauto. }
           apply rb_sorted_node_inv in H0 as [Hgt_n3_r [Hsm_n3_r [Hrb_r21 Hrb_r22]]].
           constructor;repeat (try(constructor; eauto; try lia)); try(eapply node_greater); eauto. 
        ++ apply smaller_node_inv in Hsmall2 as [Hn0_lt_n2 [Hsm_n0_r21 Hsm_n0_r22]].
           destruct Hn0_g_r12.
           apply rb_sorted_node_inv in H as [Hgt_n2 [Hsm_right2 [Hrb_leaf2 Hrb_right2]]].
           apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [Hrb_left Hrb_right]]].
           apply greater_node_inv in Hn0_gt_n1 as [Hn0_gt_n2 [Hn0_g_r11_g Hn0_g_r12_g]].
           apply smaller_node_inv in Hsm_v as [Hv_lt_n0 [Hsm_v_left Hsm_v_right]].
           apply smaller_node_inv in Hsm_v_left as [Hv_lt_n2 [Hsm_v_r11 Hsm_v_r12]].
           apply rb_sorted_node_inv in Hrb_right as [Hgt_n0_full [Hsm_n0_full [Hrb_r1 Hrb_r2]]].
           apply smaller_node_inv in Hn0_g_r11 as [Hn0_lt_n3 [Hsm_n0_r31 Hsm_n0_r32]].
           pose proof (greater_monotone n0 v (node Red leaf n (node Black l2_1 n1 l2_2)) Hsmall1 Hgt_v) as Hn0_leftpart.
           assert (Hn0_r1: greater n0 (node Black r1_1 n2 r1_2)).
           { apply node_greater; eauto. }
           apply rb_sorted_node_inv in H0 as [Hgt_n3_r [Hsm_n3_r [Hrb_r21 Hrb_r22]]].
           apply greater_node_inv in Hgt_v as [_ [_ Hgv_right]].
          pose proof (greater_monotone n2 v (node Black l2_1 n1 l2_2) Hv_lt_n2 Hgv_right) as Hgt_n2_tree.
           apply greater_node_inv in Hgt_n2_tree as [_ [Hgt_n2_l21 Hgt_n2_l22]].
           constructor;repeat (try(constructor; eauto; try lia)); try(eapply smaller_decrease); eauto. 
        ++ apply smaller_node_inv in Hsmall2 as [Hn0_lt_n2 [Hsm_n0_r21 Hsm_n0_r22]].
           destruct Hn0_g_r12.
           apply rb_sorted_node_inv in H as [Hgt_n2 [Hsm_right2 [Hrb_leaf2 Hrb_right2]]].
           apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [Hrb_left Hrb_right]]].
           apply greater_node_inv in Hn0_gt_n1 as [Hn0_gt_n2 [Hn0_g_r11_g Hn0_g_r12_g]].
           apply smaller_node_inv in Hsm_v as [Hv_lt_n0 [Hsm_v_left Hsm_v_right]].
           apply smaller_node_inv in Hsm_v_left as [Hv_lt_n2 [Hsm_v_r11 Hsm_v_r12]].
           apply rb_sorted_node_inv in Hrb_right as [Hgt_n0_full [Hsm_n0_full [Hrb_r1 Hrb_r2]]].
           apply smaller_node_inv in Hn0_g_r11 as [Hn0_lt_n3 [Hsm_n0_r31 Hsm_n0_r32]].
           pose proof (greater_monotone n0 v (node Red leaf n (node Black l2_1 n1 l2_2)) Hsmall1 Hgt_v) as Hn0_leftpart.
           assert (Hn0_r1: greater n0 (node Black r1_1 n2 r1_2)).
           { apply node_greater; eauto. }
           apply rb_sorted_node_inv in H0 as [Hgt_n3_r [Hsm_n3_r [Hrb_r21 Hrb_r22]]].
           apply greater_node_inv in Hgt_v as [_ [_ Hgv_right]].
          pose proof (greater_monotone n2 v (node Black l2_1 n1 l2_2) Hv_lt_n2 Hgv_right) as Hgt_n2_tree.
           apply greater_node_inv in Hgt_n2_tree as [_ [Hgt_n2_l21 Hgt_n2_l22]].
           constructor;repeat (try(constructor; eauto; try lia)); try(eapply smaller_decrease); eauto. 
        ++ apply smaller_node_inv in Hsmall2 as [Hn0_lt_n2 [Hsm_n0_r21 Hsm_n0_r22]].
           destruct Hn0_g_r12.
           apply rb_sorted_node_inv in H as [Hgt_n2 [Hsm_right2 [Hrb_leaf2 Hrb_right2]]].
           apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [Hrb_left Hrb_right]]].
           apply greater_node_inv in Hn0_gt_n1 as [Hn0_gt_n2 [Hn0_g_r11_g Hn0_g_r12_g]].
           apply smaller_node_inv in Hsm_v as [Hv_lt_n0 [Hsm_v_left Hsm_v_right]].
           apply smaller_node_inv in Hsm_v_left as [Hv_lt_n2 [Hsm_v_r11 Hsm_v_r12]].
           apply rb_sorted_node_inv in Hrb_right as [Hgt_n0_full [Hsm_n0_full [Hrb_r1 Hrb_r2]]].
           apply smaller_node_inv in Hn0_g_r11 as [Hn0_lt_n3 [Hsm_n0_r31 Hsm_n0_r32]].
           assert (Hn0_r1: greater n0 (node Black r1_1 n2 r1_2)).
           { apply node_greater; eauto. }
           apply rb_sorted_node_inv in H0 as [Hgt_n3_r [Hsm_n3_r [Hrb_r21 Hrb_r22]]].
           apply greater_node_inv in Hgt_v as [_ [_ Hgv_right]].
           apply smaller_node_inv in Hsm_v_right as [Hv_lt_n3 [Hsm_v_r21 Hsm_v_r22]].
           constructor;repeat (try(constructor; eauto; try lia)); try(eapply smaller_decrease); eauto.
        ++ apply smaller_node_inv in Hsmall2 as [Hn0_lt_n2 [Hsm_n0_r21 Hsm_n0_r22]].
           destruct Hn0_g_r12.
           apply rb_sorted_node_inv in H as [Hgt_n2 [Hsm_right2 [Hrb_leaf2 Hrb_right2]]].
           apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [Hrb_left Hrb_right]]].
           apply greater_node_inv in Hn0_gt_n1 as [Hn0_gt_n2 [Hn0_g_r11_g Hn0_g_r12_g]].
           apply smaller_node_inv in Hsm_v as [Hv_lt_n0 [Hsm_v_left Hsm_v_right]].
           apply smaller_node_inv in Hsm_v_left as [Hv_lt_n2 [Hsm_v_r11 Hsm_v_r12]].
           apply rb_sorted_node_inv in Hrb_right as [Hgt_n0_full [Hsm_n0_full [Hrb_r1 Hrb_r2]]].
           apply smaller_node_inv in Hn0_g_r11 as [Hn0_lt_n3 [Hsm_n0_r31 Hsm_n0_r32]].
           pose proof (greater_monotone n0 v (node Red leaf n (node Red l2_1 n1 l2_2)) Hsmall1 Hgt_v) as Hn0_leftpart.
           assert (Hn0_r1: greater n0 (node Black r1_1 n2 r1_2)).
           { apply node_greater; eauto. }
           apply rb_sorted_node_inv in H0 as [Hgt_n3_r [Hsm_n3_r [Hrb_r21 Hrb_r22]]].
           apply smaller_node_inv in Hsm_v_right as [Hv_lt_n3 [Hsm_v_r21 Hsm_v_r22]].
           constructor;repeat (try(constructor; eauto; try lia)); try(eapply smaller_decrease); eauto. 
        ++ apply smaller_node_inv in Hsmall2 as [Hn0_lt_n2 [Hsm_n0_r21 Hsm_n0_r22]].
           destruct Hn0_g_r12.
           apply rb_sorted_node_inv in H as [Hgt_n2 [Hsm_right2 [Hrb_leaf2 Hrb_right2]]].
           apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [Hrb_left Hrb_right]]].
           apply greater_node_inv in Hn0_gt_n1 as [Hn0_gt_n2 [Hn0_g_r11_g Hn0_g_r12_g]].
           apply smaller_node_inv in Hsm_v as [Hv_lt_n0 [Hsm_v_left Hsm_v_right]].
           apply smaller_node_inv in Hsm_v_left as [Hv_lt_n2 [Hsm_v_r11 Hsm_v_r12]].
           apply rb_sorted_node_inv in Hrb_right as [Hgt_n0_full [Hsm_n0_full [Hrb_r1 Hrb_r2]]].
           apply smaller_node_inv in Hn0_g_r11 as [Hn0_lt_n3 [Hsm_n0_r31 Hsm_n0_r32]].
           pose proof (greater_monotone n0 v (node Red leaf n (node Red l2_1 n1 l2_2)) Hsmall1 Hgt_v) as Hn0_leftpart.
           assert (Hn0_r1: greater n0 (node Black r1_1 n2 r1_2)).
           { apply node_greater; eauto. }
           apply rb_sorted_node_inv in H0 as [Hgt_n3_r [Hsm_n3_r [Hrb_r21 Hrb_r22]]].
           apply smaller_node_inv in Hsm_v_right as [Hv_lt_n3 [Hsm_v_r21 Hsm_v_r22]].
           constructor;repeat (try(constructor; eauto; try lia)); try(eapply smaller_decrease); eauto. 
        ++ apply smaller_node_inv in Hsmall2 as [Hn0_lt_n2 [Hsm_n0_r21 Hsm_n0_r22]].
           destruct Hn0_g_r12.
           apply rb_sorted_node_inv in H as [Hgt_n2 [Hsm_right2 [Hrb_leaf2 Hrb_right2]]].
           apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [Hrb_left Hrb_right]]].
           apply greater_node_inv in Hn0_gt_n1 as [Hn0_gt_n2 [Hn0_g_r11_g Hn0_g_r12_g]].
           apply smaller_node_inv in Hsm_v as [Hv_lt_n0 [Hsm_v_left Hsm_v_right]].
           apply smaller_node_inv in Hsm_v_left as [Hv_lt_n2 [Hsm_v_r11 Hsm_v_r12]].
           apply rb_sorted_node_inv in Hrb_right as [Hgt_n0_full [Hsm_n0_full [Hrb_r1 Hrb_r2]]].
           apply smaller_node_inv in Hn0_g_r11 as [Hn0_lt_n3 [Hsm_n0_r31 Hsm_n0_r32]].
           pose proof (greater_monotone n0 v (node Red leaf n (node Red l2_1 n1 l2_2)) Hsmall1 Hgt_v) as Hn0_leftpart.
           assert (Hn0_r1: greater n0 (node Black r1_1 n2 r1_2)).
           { apply node_greater; eauto. }
           apply rb_sorted_node_inv in H0 as [Hgt_n3_r [Hsm_n3_r [Hrb_r21 Hrb_r22]]].
           apply smaller_node_inv in Hsm_v_right as [Hv_lt_n3 [Hsm_v_r21 Hsm_v_r22]].
           constructor;repeat (try(constructor; eauto; try lia)); try(eapply smaller_decrease); eauto. 
      * destruct c; destruct c0;  destruct r1; destruct r2; try (destruct c); try (destruct c0);
        apply smaller_node_inv in H5 as [Hv_lt_n0 [Hsm_v_left Hsm_v_right]];
        apply rb_sorted_node_inv in H7 as [Hgt_n0 [Hsm_n0 [Hrb_rleft Hrb_rright]]];
        eauto.
        ++ apply smaller_node_inv in Hsm_n0 as [Hv_lt_n3 [Hsm_v_r11 Hsm_v_r12]];
          apply rb_sorted_node_inv in Hrb_rright as [Hgt_n1 [Hsm_n1 [Hrb_rleft1 Hrb_rright1]]];
          apply greater_node_inv in H4 as [Hn0_gt_n3 [Hn0_g_r11 Hn0_g_r12]];
          apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [_ _]]];
          apply greater_node_inv in Hgt_v as [Hv_gt_n [Hv_gt_left Hv_gt_right]].
          apply greater_node_inv in Hv_gt_left  as [Hv_gt_n1 [Hv_gt_left1 Hv_gt_right1]].
          apply smaller_node_inv in Hsm_v as [Hv_lt_n1 _];
          pose proof (greater_monotone n0 v (node Black l1_1 n1 l1_2) Hv_lt_n0 Hn0_g_r11) as Hgt_n0_tree.
          apply greater_node_inv in Hgt_n0_tree as [_ [Hgt_n0_l1_1 Hgt_n0_l1_2]].
          constructor; try(constructor; eauto). apply node_greater;repeat(try(constructor;eauto; try lia)). lia.
        ++ apply smaller_node_inv in Hsm_v_left  as [Hv_lt_n3 [Hsm_v_r11 Hsm_v_r12]];
          apply rb_sorted_node_inv in Hrb_rleft  as [Hgt_n1 [Hsm_n1 [Hrb_rleft1 Hrb_rright1]]];
          apply greater_node_inv in H4 as [Hn0_gt_n3 [Hn0_g_r11 Hn0_g_r12]];
          apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [_ _]]];
          apply greater_node_inv in Hgt_v as [Hv_gt_n [Hv_gt_left Hv_gt_right]].
          apply greater_node_inv in Hv_gt_left  as [Hv_gt_n1 [Hv_gt_left1 Hv_gt_right1]].
          apply smaller_node_inv in Hsm_v as [Hv_lt_n1 _];
          pose proof (greater_monotone n0 v (node Black l1_1 n1 l1_2) Hv_lt_n0 Hn0_g_r11) as Hgt_n0_tree.
          apply greater_node_inv in Hgt_n0_tree as [_ [Hgt_n0_l1_1 Hgt_n0_l1_2]].
          constructor; try(constructor; eauto); try(apply node_greater); repeat(try(constructor;eauto; try lia)); try lia; admit.
        ++ apply smaller_node_inv in Hsm_v_left  as [Hv_lt_n3 [Hsm_v_r11 Hsm_v_r12]];
          apply rb_sorted_node_inv in Hrb_rleft  as [Hgt_n1 [Hsm_n1 [Hrb_rleft1 Hrb_rright1]]];
          apply greater_node_inv in H4 as [Hn0_gt_n3 [Hn0_g_r11 Hn0_g_r12]];
          apply rb_sorted_node_inv in Hfull as [Hgt_v [Hsm_v [_ _]]];
          apply greater_node_inv in Hgt_v as [Hv_gt_n [Hv_gt_left Hv_gt_right]].
          apply greater_node_inv in Hv_gt_left  as [Hv_gt_n1 [Hv_gt_left1 Hv_gt_right1]].
          apply smaller_node_inv in Hsm_v as [Hv_lt_n1 _];
          pose proof (greater_monotone n0 v (node Black l1_1 n1 l1_2) Hv_lt_n0 Hn0_g_r11) as Hgt_n0_tree.
          apply greater_node_inv in Hgt_n0_tree as [_ [Hgt_n0_l1_1 Hgt_n0_l1_2]].
          constructor; try(constructor; eauto); try(apply node_greater); repeat(try(constructor;eauto; try lia)); try lia; admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
        ++ admit.
      * match goal with
      | [ Hfull: rb_sorted (node Black (node Red (node Red ?a ?x ?b) ?y ?c1) ?v ?r) |- _ ] =>
          apply balance_case_left_left_sorted; exact Hfull
      | [ Hfull: rb_sorted (node Black (node Red ?a ?x (node Red ?b ?y ?c1)) ?v ?r) |- _ ] =>
          apply balance_case_left_right_sorted; exact Hfull
      | [ Hfull: rb_sorted (node Black ?l ?v (node Red (node Red ?a ?x ?b) ?y ?c1)) |- _ ] =>
          apply balance_case_right_left_sorted; exact Hfull
      | [ Hfull: rb_sorted (node Black ?l ?v (node Red ?a ?x (node Red ?b ?y ?c1))) |- _ ] =>
          apply balance_case_right_right_sorted; exact Hfull
      | _ =>
          (* none of the rotation shapes: balance is identity, just re-use Hfull *)
          constructor; assumption
      end.
      
      destruct c; destruct c0;  destruct r1; destruct r2; try (destruct c); try (destruct c1); try (destruct c0).
        all: finish_balance_case.
        match goal with
          | [ Hfull: rb_sorted (node Black (node Red (node Red ?a ?x ?b) ?y ?c1) ?v ?r) |- _ ] =>
              apply balance_case_left_left_sorted; exact Hfull
          | [ Hfull: rb_sorted (node Black (node Red ?a ?x (node Red ?b ?y ?c1)) ?v ?r) |- _ ] =>
              apply balance_case_left_right_sorted; exact Hfull
          | [ Hfull: rb_sorted (node Black ?l ?v (node Red (node Red ?a ?x ?b) ?y ?c1)) |- _ ] =>
              apply balance_case_right_left_sorted; exact Hfull
          | [ Hfull: rb_sorted (node Black ?l ?v (node Red ?a ?x (node Red ?b ?y ?c1))) |- _ ] =>
              apply balance_case_right_right_sorted; exact Hfull
          | _ => (* none of the rotation shapes -> balance does nothing useful *)
              constructor; assumption
          end.
        

        
(* END HERE *)

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

Lemma rb_insert_aux_never_leaf : forall x t, rb_insert_aux x t <> leaf.
Proof.
  intros x t; destruct t as [| c l v r]; simpl.
  - discriminate.
  -  intros H.
    destruct (v =? x) eqn:Heq.
    + discriminate H.
    + destruct (v <? x) eqn:Hlt.
      * simpl in H. pose proof (balance_node_never_leaf c l v (rb_insert_aux x r)) as N.
        apply N in H; assumption.
      * simpl in H. pose proof (balance_node_never_leaf c (rb_insert_aux x l) v r) as N.
        apply N in H; assumption.
Qed.

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