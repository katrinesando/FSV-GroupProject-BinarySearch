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

Definition root_black (t: rb_tree) : Prop :=
  match t with
  | node Black _ _ _ => True
  | leaf => True
  | _ => False
  end.

(* Definition rb_invariant (t: rb_tree) : Prop :=
  root_black t /\ rb_sorted t /\ no_red_red t /\ exists k, black_height t = Some k. *)

(* This is too weak - gives problems in rb_insert_aux*)
Definition rb_invariant (t: rb_tree) : Prop :=
  rb_sorted t /\ no_red_red t /\ exists k, black_height t = Some k.

Ltac inv H := inversion H; subst; clear H.
(* simple inversion lemmas to reuse everywhere *)
Lemma rb_sorted_node_inv :
  forall c l v r,
    rb_sorted (node c l v r) ->
    greater v l /\ smaller v r /\ rb_sorted l /\ rb_sorted r.
Proof.
  intros c l v r H.
  inv H. repeat split; assumption.
Qed.

Lemma greater_node_inv :
  forall n c l v r,
    greater n (node c l v r) -> n > v /\ greater n l /\ greater n r.
Proof.
  intros n c l v r H. inv H. repeat split; assumption.
Qed.

Lemma smaller_node_inv :
  forall n c l v r,
    smaller n (node c l v r) -> n < v /\ smaller n l /\ smaller n r.
Proof.
  intros n c l v r H. inv H. repeat split; assumption.
Qed.

(* recolor helper lemmas *)
Lemma recolor_preserves_rb_sorted :
  forall c l v r,
    rb_sorted (node c l v r) ->
    rb_sorted (node Black l v r).
Proof.
  intros * H. inv H. constructor; assumption.
Qed.

Lemma recolor_preserves_no_red_red :
  forall c l v r,
    no_red_red (node c l v r) ->
    no_red_red (node Black l v r).
Proof.
  intros c l v r H. inv H; constructor; assumption.
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
  induction t; simpl; intros Hsm; try (inversion Hsm; constructor);
  inv Hsm; eauto; lia.
Qed.

Lemma balance_case_left_left_sorted:
  forall a x b y c v r,
    rb_sorted (node Black (node Red (node Red a x b) y c) v r) ->
    rb_sorted (node Red (node Black a x b) y (node Black c v r)).
Proof.
  intros.
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
  induction t; simpl; intros H; try (inversion H; constructor);
  inv H; eauto; lia.
Qed.

Lemma balance_case_left_right_sorted :
  forall a x b y c v r,
    rb_sorted (node Black (node Red a x (node Red b y c)) v r) ->
    rb_sorted (node Red (node Black a x b) y (node Black c v r)).
Proof.
  intros. 
  apply rb_sorted_node_inv in H as [Hgt_outer [Hsm_outer [Hrb_l Hrb_r]]].
  apply rb_sorted_node_inv in Hrb_l as [Hgt_x [Hsm_x [Hrb_a Hrb_lr]]].
  apply rb_sorted_node_inv in Hrb_lr as [Hgt_y [Hsm_y [Hrb_b Hrb_c]]].
  apply smaller_node_inv in Hsm_x as [Hx_lt_y [Hsm_x_b Hsm_x_c]].
  apply greater_node_inv in Hgt_outer as [Hv_gt_x [Hv_g_left Hv_g_lr]].
  apply greater_node_inv in Hv_g_lr as [Hv_gt_y [Hv_g_b Hv_g_c]].
  constructor; eauto; try(constructor; eauto); try(eapply greater_monotone); try(eapply smaller_decrease); eauto.
Qed.

Lemma balance_case_right_left_sorted :
  forall l a x b y c v,
    rb_sorted (node Black l v (node Red (node Red a x b) y c)) ->
    rb_sorted (node Red (node Black l v a) x (node Black b y c)).
Proof.
  intros. 
  apply rb_sorted_node_inv in H as [Hgt_outer [Hsm_outer [Hrb_l Hrb_r]]].
  apply rb_sorted_node_inv in Hrb_r as [Hgt_x [Hsm_x [Hrb_a Hrb_lr]]].
  apply rb_sorted_node_inv in Hrb_a as [Hgt_y [Hsm_y [Hrb_b Hrb_c]]].
  apply greater_node_inv in Hgt_x as [Hx_gt_y [Hgt_x_b Hgt_x_c]].
  apply smaller_node_inv in Hsm_outer as [Hv_lt_y [Hv_l_left Hv_l_lr]].
  apply smaller_node_inv in Hv_l_left  as [Hv_lt_x [Hv_l_a Hv_l_b]].
  constructor; eauto; try(constructor; eauto); try(eapply greater_monotone); try(eapply smaller_decrease); eauto.
Qed.

Lemma balance_case_right_right_sorted :
  forall l a x b y c v,
    rb_sorted (node Black l v (node Red a x (node Red b y c))) ->
    rb_sorted (node Red (node Black l v a) x (node Black b y c)).
Proof.
  intros. 
  apply rb_sorted_node_inv in H as [Hgt_outer [Hsm_outer [Hrb_l Hrb_r]]].
  apply rb_sorted_node_inv in Hrb_r as [Hgt_x [Hsm_x [Hrb_a Hrb_lr]]].
  apply rb_sorted_node_inv in Hrb_lr as [Hgt_y [Hsm_y [Hrb_b Hrb_c]]].
  apply smaller_node_inv in Hsm_x as [Hx_lt_y [Hsm_x_b Hsm_x_c]].
  apply smaller_node_inv in Hsm_outer as [Hv_lt_y [Hv_l_left Hv_l_lr]].
  apply smaller_node_inv in Hv_l_lr  as [Hv_lt_x [Hv_l_a Hv_l_b]].
  constructor; eauto; try(constructor; eauto); try(eapply greater_monotone); try(eapply smaller_decrease); eauto.
Qed.

Ltac solve_rotation_goals :=
  repeat (first [
    (* Try to use existing hypotheses directly *)
    assumption |
    
    (* Extract facts from Hsm_v : smaller v (node Red leaf rv_r (node Red rr_l rr_v rr_r)) *)
    match goal with
    | [ H: smaller ?v (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- rb_sorted (node Red (node Black leaf ?v leaf) ?rv_r (node Black ?rr_l ?rr_v ?rr_r)) ] =>
        (* Goal 1: Extract v < rv_r and v < rr_v from H *)
        apply smaller_node_inv in H as [Hlt_rv [Hsm_leaf Hsm_right]];
        apply smaller_node_inv in Hsm_right as [Hlt_rr [Hsm_rr_l Hsm_rr_r]];
        constructor; [
          constructor; [constructor | constructor; [lia | constructor | constructor]] |
          constructor; [lia | constructor | constructor; [lia | constructor | constructor]] |
          constructor |
          constructor; [lia | constructor | constructor]
        ]
        
    | [ H: rb_sorted (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- rb_sorted (node Red (node Black leaf ?v ?rl_l) ?rl_v (node Black ?rl_r ?rv_r leaf)) ] =>
        (* Goal 2: Need to extract ordering facts and construct proof *)
        constructor; [
          constructor; [constructor | constructor | constructor] |
          constructor; [admit | constructor | constructor] |  (* Need rl_v facts *)
          constructor; [constructor | constructor | constructor] |
          constructor; [constructor | constructor | constructor]
        ]
        
    | [ H: rb_sorted (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- rb_sorted (node Red (node Black leaf ?v (node Black ?rl_l ?rl_v ?rl_r)) ?rv_r (node Black ?rr_l ?rr_v ?rr_r)) ] =>
        (* Goal 3: Extract facts and construct *)
        apply rb_sorted_node_inv in H as [Hgt_rv [Hsm_rv [Hrb_leaf Hrb_right]]];
        apply rb_sorted_node_inv in Hrb_right as [Hgt_rr [Hsm_rr [Hrb_rr_l Hrb_rr_r]]];
        constructor; [
          constructor; [constructor | constructor; [admit | constructor | constructor]] |
          constructor; [lia | constructor | constructor; [lia | constructor | constructor]] |
          constructor; [constructor | constructor; [admit | constructor | constructor] |
            constructor | constructor; [admit | constructor | constructor]] |
          constructor; [lia | constructor | constructor]
        ]
        
    | [ |- rb_sorted (node Red (node Black leaf ?v ?rl_l) ?rl_v (node Black ?rl_r ?rv_r (node Black ?rr_l ?rr_v ?rr_r))) ] =>
        (* Goal 4: Similar construction *)
        constructor; [
          constructor; [constructor | constructor | constructor] |
          constructor; [admit | constructor | constructor] |
          constructor; [constructor | constructor | constructor] |
          constructor; [constructor; [admit | constructor | constructor] |
            constructor; [admit | constructor | constructor] |
            constructor | constructor; [admit | constructor | constructor]]
        ]
        
    | [ |- rb_sorted (node Red (node Black leaf ?v ?rl_l) ?rl_v (node Black ?rl_r ?rv_r (node Red ?rr_l ?rr_v ?rr_r))) ] =>
        (* Goal 5: Similar construction *)
        constructor; [
          constructor; [constructor | constructor | constructor] |
          constructor; [admit | constructor | constructor] |
          constructor; [constructor | constructor | constructor] |
          constructor; [constructor; [admit | constructor | constructor] |
            constructor; [admit | constructor | constructor] |
            constructor | constructor; [admit | constructor | constructor]]
        ]
        
    | [ |- greater _ _ ] => constructor; try lia
    | [ |- smaller _ _ ] => constructor; try lia; try constructor
    | [ |- rb_sorted _ ] => constructor; try assumption
    | [ |- _ ] => admit  (* fallback for complex subgoals *)
    end
  ]);
  try lia.





Ltac solve_rotation_goals_minimal :=
  repeat (first [
    assumption |
    
    match goal with
    | [ H: smaller ?v (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- rb_sorted (node Red (node Black leaf ?v leaf) ?rv_r (node Black ?rr_l ?rr_v ?rr_r)) ] =>
        apply smaller_node_inv in H as [Hlt_rv [Hsm_leaf Hsm_right]];
        apply smaller_node_inv in Hsm_right as [Hlt_rr [Hsm_rr_l Hsm_rr_r]];
        constructor; [
          constructor; [constructor | constructor; [lia | constructor | constructor]] |
          constructor; [lia | constructor | constructor; [lia | constructor | constructor]] |
          constructor |
          constructor; [lia | constructor | constructor]
        ]
        
    | [ H: rb_sorted (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- rb_sorted (node Red (node Black leaf ?v ?rl_l) ?rl_v (node Black ?rl_r ?rv_r leaf)) ] =>
        constructor; [
          constructor; [constructor | constructor | constructor] |
          constructor; [constructor; lia | constructor | constructor] |
          constructor; [constructor | constructor | constructor] |
          constructor; [constructor | constructor | constructor]
        ]
        
    | [ H: rb_sorted (node Red leaf ?rv_r (node Red ?rr_l ?rr_v ?rr_r)) |- rb_sorted (node Red (node Black leaf ?v (node Black ?rl_l ?rl_v ?rl_r)) ?rv_r (node Black ?rr_l ?rr_v ?rr_r)) ] =>
        apply rb_sorted_node_inv in H as [Hgt_rv [Hsm_rv [Hrb_leaf Hrb_right]]];
        apply rb_sorted_node_inv in Hrb_right as [Hgt_rr [Hsm_rr [Hrb_rr_l Hrb_rr_r]]];
        constructor; [
          constructor; [constructor | constructor; [constructor; lia | constructor | constructor]] |
          constructor; [lia | constructor | constructor; [lia | constructor | constructor]] |
          constructor; [constructor | constructor; [constructor; lia | constructor | constructor] |
            constructor | constructor; [constructor; lia | constructor | constructor]] |
          constructor; [lia | constructor | constructor]
        ]
        
    | [ |- rb_sorted (node Red (node Black leaf ?v ?rl_l) ?rl_v (node Black ?rl_r ?rv_r (node Black ?rr_l ?rr_v ?rr_r))) ] =>
        constructor; [
          constructor; [constructor | constructor | constructor] |
          constructor; [constructor; lia | constructor | constructor] |
          constructor; [constructor | constructor | constructor] |
          constructor; [constructor; [constructor; lia | constructor | constructor] |
            constructor; [constructor; lia | constructor | constructor] |
            constructor | constructor; [constructor; lia | constructor | constructor]]
        ]
        
    | [ |- rb_sorted (node Red (node Black leaf ?v ?rl_l) ?rl_v (node Black ?rl_r ?rv_r (node Red ?rr_l ?rr_v ?rr_r))) ] =>
        constructor; [
          constructor; [constructor | constructor | constructor] |
          constructor; [constructor; lia | constructor | constructor] |
          constructor; [constructor | constructor | constructor] |
          constructor; [constructor; [constructor; lia | constructor | constructor] |
            constructor; [constructor; lia | constructor | constructor] |
            constructor | constructor; [constructor; lia | constructor | constructor]]
        ]
        
    | [ |- greater _ _ ] => constructor; lia
    | [ |- smaller _ _ ] => constructor; lia; constructor  
    | [ |- rb_sorted _ ] => constructor; assumption
    | [ |- _ ] => assumption  (* fallback instead of admit *)
    end
  ]);
  lia.




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
        simpl; try assumption; eauto;
        try(destruct rl_c); eauto;
        try(destruct rr_c); eauto;
        simpl; try assumption; try solve_rotation_goals_minimal;
        try( 
        apply smaller_node_inv in Hsm_v as [Hlt_rv [Hsm_leaf Hsm_right]];
        apply smaller_node_inv in Hsm_right as [Hlt_rr [Hsm_rr_l Hsm_rr_r]];
        apply rb_sorted_node_inv in Hrb_r as [Hgt_rv [Hsm_rv [Hrb_leaf Hrb_right]]];
        apply rb_sorted_node_inv in Hrb_right as [Hgt_rr [Hsm_rr [Hrb_rr_l Hrb_rr_r]]];
        apply smaller_node_inv in Hsm_rv as [Hlt_lt_rr [Hsm_l_rr_l Hsm_l_rr_r]]);
        try(
        apply smaller_node_inv in Hsm_v as [Hlt_rv [Hsm_left Hsm_right]];
        apply smaller_node_inv in Hsm_left as [Hlt_rl [Hsm_rl_l Hsm_rl_r]];
        apply rb_sorted_node_inv in Hrb_r as [Hgt_rv [Hsm_rv [Hrb_left Hrb_right]]];
        apply rb_sorted_node_inv in Hrb_left as [Hgt_rl [Hsm_rl [Hrb_rl_l Hrb_rl_r]]];
        apply greater_node_inv in Hgt_rv as [Hgt_lv[Hgt_lv_leaf Hgt_lv_right]]
        );
        try(
        apply smaller_node_inv in Hsm_leaf as [Hlt_rl [Hsm_rl_l Hsm_rl_r]];
        apply rb_sorted_node_inv in Hrb_leaf as [Hgt_rl [Hsm_rl [Hrb_rl_l Hrb_rl_r]]];
        apply greater_node_inv in Hgt_rv as [Hgt_rv_rl [Hgt_rv_rl_l Hgt_rv_rl_r]]
        );
        try(constructor; try(constructor; eauto); eauto);
        try(eapply smaller_decrease); eauto. 
      * destruct cl; eauto.
       destruct ll as [| llc lll lvl llr]; simpl; eauto.
       -- destruct lr; eauto.
          destruct c; eauto.
          apply greater_node_inv in Hgt_v as [Hv_gt_lv_l [Hv_g_leaf Hv_g_right]].
          apply greater_node_inv in Hv_g_right as [Hv_gt_n [Hv_g_lr1 Hv_g_lr2]].
          apply rb_sorted_node_inv in Hrb_l as [Hgt_lv_l [Hsm_lv_l [Hrb_leaf Hrb_right]]].
          apply rb_sorted_node_inv in Hrb_right as [Hgt_n [Hsm_n [Hrb_lr1 Hrb_lr2]]].
          apply smaller_node_inv in Hsm_lv_l as [Hv_lt_n [Hv_l_lr1 Hv_l_lr2]].
          constructor; repeat (try(constructor; eauto; try lia)); try (eapply smaller_decrease); eauto.
       --  destruct llc; eauto;
          try(destruct lr); eauto;
          try(destruct c); eauto;
          [ apply balance_case_left_right_sorted; eauto
          | apply balance_case_left_left_sorted; eauto
          | apply balance_case_left_left_sorted; eauto
          | apply balance_case_left_left_sorted; eauto].
      * destruct cl; destruct ll as [|ll_c ll_l ll_v ll_r]; destruct lr as [|lr_c lr_l lr_v lr_r].
        ++ simpl. destruct cr; eauto.
           destruct rl as [|rl_c rl_l rl_v rl_r].
           --- destruct rr as [|rr_c rr_l rr_v rr_r]; eauto.
              destruct rr_c; eauto.
              apply smaller_node_inv in Hsm_v as [Hlt_rv [Hsm_leaf Hsm_right]].
              apply smaller_node_inv in Hsm_right as [Hlt_rr [Hsm_rr_l Hsm_rr_r]].
              apply rb_sorted_node_inv in Hrb_r as [Hgt_rv [Hsm_rv [Hrb_leaf Hrb_right]]].
              apply rb_sorted_node_inv in Hrb_right as [Hgt_rr [Hsm_rr [Hrb_rr_l Hrb_rr_r]]].
              apply greater_node_inv in Hgt_v as [Hgt_lv_l [Hgt_leaf _]].
              apply smaller_node_inv in Hsm_rv as [Hlt_rv_rr [Hsm_rv_l Hsm_rv_r]].
              constructor; try(constructor; eauto; try lia); try (eapply smaller_decrease); try(eapply greater_monotone); eauto.
          ---  destruct rl_c; eauto.
            ** destruct rr as [|rr_c rr_l rr_v rr_r]; eauto.
               destruct rr_c; eauto. 
               apply smaller_node_inv in Hsm_v as [Hlt_rv [Hsm_leaf Hsm_right]].
              apply smaller_node_inv in Hsm_right as [Hlt_rr [Hsm_rr_l Hsm_rr_r]].
              apply rb_sorted_node_inv in Hrb_r as [Hgt_rv [Hsm_rv [Hrb_leaf Hrb_right]]].
              apply rb_sorted_node_inv in Hrb_right as [Hgt_rr [Hsm_rr [Hrb_rr_l Hrb_rr_r]]].
              apply greater_node_inv in Hgt_v as [Hgt_lv_l [Hgt_leaf _]].
              apply smaller_node_inv in Hsm_rv as [Hlt_rv_rr [Hsm_rv_l Hsm_rv_r]].
              constructor; try(constructor; eauto; try lia); try (eapply smaller_decrease); try(eapply greater_monotone); eauto.
            ** apply balance_case_right_left_sorted. eauto.
        ++ simpl. destruct cr; 
           destruct lr_c; eauto.
           --- destruct rl as [|rl_c rl_l rl_v rl_r].
            ** destruct rr as [|rr_c rr_l rr_v rr_r]; eauto.
              destruct rr_c; eauto.
              apply smaller_node_inv in Hsm_v as [Hlt_rv [Hsm_leaf Hsm_rv]].
              apply smaller_node_inv in Hsm_rv as [Hrv_lt_rr [Hsm_rv_rl Hsm_rv_rr]].
              pose proof (greater_monotone rv_r v (node Black leaf lv_l (node Black lr_l lr_v lr_r)) Hlt_rv Hgt_v) as Hgt_rv_left.
              assert (Hsm_rr_black : smaller rv_r (node Black rr_l rr_v rr_r)).
              { constructor; apply rb_sorted_node_inv in Hrb_r as [Hgt_rv' [Hsm_rv' [Hrb_leaf' Hrb_right']]];
              apply smaller_node_inv in Hsm_rv' as [Hrv_lt_rr1 [Hsm_rv_rl1 Hsm_rv_rr1]];
              eauto. }
              assert (Hrb_rr_black : rb_sorted (node Black rr_l rr_v rr_r)).
              { constructor; apply rb_sorted_node_inv in Hrb_r as [Hgt_rv' [Hsm_rv' [Hrb_leaf' Hrb_right']]]; 
              apply rb_sorted_node_inv in Hrb_right' as [Hgt_rr [Hsm_rr [Hrb_rr_l Hrb_rr_r]]]; eauto. }
              constructor; eauto.
            ** destruct rl_c; eauto.
                +++ destruct rr as [| rr_c rr_l rr_v rr_r]; eauto.
                    destruct rr_c; eauto. 
                    try(apply balance_case_right_right_sorted; eauto).
                +++ apply balance_case_right_left_sorted; eauto.
          ---  destruct rl as [|rl_c rl_l rl_v rl_r]; eauto.
            ** destruct rr as [| rr_c rr_l rr_v rr_r]; eauto.
                destruct rr_c; eauto. 
                try(apply balance_case_right_right_sorted; eauto).
            **  destruct rl_c as [| rr_c rr_l rr_v rr_r]; eauto.
                destruct rr; eauto.
                destruct c; eauto.
                try(apply balance_case_right_right_sorted; eauto).
                apply balance_case_right_left_sorted; eauto.
        ++ destruct cr; eauto.
          destruct rl as [|rl_c rl_l rl_v rl_r].
           --- destruct rr as [|rr_c rr_l rr_v rr_r]; eauto.
              destruct rr_c; eauto.
              try(apply balance_case_right_right_sorted; eauto).
          --- destruct rl_c; eauto.
              ** destruct rr as [| rr_c rr_l rr_v rr_r]; eauto.
                    destruct rr_c; eauto. 
                    try(apply balance_case_right_right_sorted; eauto).
              ** apply balance_case_right_left_sorted; eauto.
        ++ destruct cr; eauto.
          destruct rl as [|rl_c rl_l rl_v rl_r].
           --- destruct rr as [|rr_c rr_l rr_v rr_r]; eauto.
              destruct rr_c; eauto.
              try(apply balance_case_right_right_sorted; eauto).
          --- destruct rl_c; eauto.
              ** destruct rr as [| rr_c rr_l rr_v rr_r]; eauto.
                    destruct rr_c; eauto. 
                    try(apply balance_case_right_right_sorted; eauto).
              ** apply balance_case_right_left_sorted; eauto.
        ++ destruct cr; eauto.
          destruct rl as [|rl_c rl_l rl_v rl_r].
           --- destruct rr as [|rr_c rr_l rr_v rr_r]; eauto.
              destruct rr_c; eauto.
              try(apply balance_case_right_right_sorted; eauto).
          --- destruct rl_c; eauto.
              ** destruct rr as [| rr_c rr_l rr_v rr_r]; eauto.
                    destruct rr_c; eauto. 
                    try(apply balance_case_right_right_sorted; eauto).
              ** apply balance_case_right_left_sorted; eauto.
        ++ destruct cr; eauto.
          destruct rl as [|rl_c rl_l rl_v rl_r].
          --- destruct lr_c as [|rr_c rr_l rr_v rr_r]; eauto. apply balance_case_left_right_sorted. eauto.
          --- destruct lr_c; eauto.
              apply balance_case_left_right_sorted. eauto.
          --- destruct lr_c; eauto.
            ** destruct rl; eauto.
              +++ destruct rr; eauto;
                  destruct c; eauto.
                  apply balance_case_right_right_sorted; eauto.
              +++ destruct c; eauto;
                  try(destruct rr); eauto;
                  try(destruct c); eauto;
                  try(apply balance_case_right_right_sorted; eauto);
                  try(apply balance_case_left_right_sorted; eauto);
                  try(apply balance_case_right_left_sorted; eauto);
                  apply rb_sorted_node_inv in Hrb_r as [Hgt_rv [Hsm_rv [Hrb_rleft Hrb_rright]]];
                  apply rb_sorted_node_inv in Hrb_rleft as [Hgt_n [Hsm_n [Hrb_rl1 Hrb_rl2]]];
                  apply greater_node_inv in Hgt_rv as [Hrv_gt_n [Hrv_gt_rl1 Hrv_gt_rl2]];
                  apply smaller_node_inv in Hsm_v as [Hlt_rv [Hsm_left Hsm_right]];
                  apply smaller_node_inv in Hsm_left  as [Hlt_n [Hsm_rl1 Hsm_rl2]];
                  constructor; eauto.
                  *** apply smaller_node_inv in Hsm_rv as [Hrv_lt_n0 [Hsm_rv_rr1 Hsm_rv_rr2]].
                      assert (Hn_lt_rv: n < rv_r) by lia.
                      assert (Hsm_rv_black : smaller rv_r (node Black rr1 n0 rr2)).
                      { constructor; [ exact Hrv_lt_n0 | exact Hsm_rv_rr1 | exact Hsm_rv_rr2 ]. }
                      pose proof (smaller_decrease n rv_r (node Black rr1 n0 rr2) Hn_lt_rv Hsm_rv_black) as Hsm_n_rr_black.
                      assert (Hrb_right_rot : rb_sorted (node Red rl2 rv_r (node Black rr1 n0 rr2))).
                      { constructor; [ exact Hrv_gt_rl2 | exact Hsm_rv_black | exact Hrb_rl2 | exact Hrb_rright ]. }
                    constructor; eauto.
                  *** assert (Hn_lt_rv: n < rv_r) by lia.
                      pose proof (smaller_decrease n rv_r (node Red rr1 n0 rr2) Hn_lt_rv Hsm_rv) as Hsm_n_rr.
                      (* build rb_sorted for node Red rl2 rv_r (node Red rr1 n0 rr2) *)
                      assert (Hrb_right_node : rb_sorted (node Red rl2 rv_r (node Red rr1 n0 rr2))).
                      { constructor; eauto. }
                       constructor; eauto.
            ** apply balance_case_left_right_sorted. eauto.
        ++ destruct ll_c; eauto.
          --- destruct cr; eauto.
              destruct rl; eauto.
              ** destruct rr; eauto.
                 destruct c; eauto.
                 apply balance_case_right_right_sorted; eauto.
              ** destruct c; eauto.
                 try(destruct rr); eauto;
                 try(destruct c); eauto;
                 try(apply balance_case_right_right_sorted; eauto);
                 try(apply balance_case_left_left_sorted; eauto);
                 try(apply balance_case_right_left_sorted; eauto);
                 apply rb_sorted_node_inv in Hrb_r as [Hgt_rv [Hsm_rv [Hrb_rleft Hrb_rright]]];
                 apply rb_sorted_node_inv in Hrb_rleft as [Hgt_n [Hsm_n [Hrb_rl1 Hrb_rl2]]];
                 apply greater_node_inv in Hgt_rv as [Hrv_gt_n [Hrv_gt_rl1 Hrv_gt_rl2]];
                 apply smaller_node_inv in Hsm_v as [Hlt_rv [Hsm_left Hsm_right]];
                 apply smaller_node_inv in Hsm_left  as [Hlt_n [Hsm_rl1 Hsm_rl2]];
                 constructor; eauto.
                 apply balance_case_right_left_sorted.  eauto.
          --- apply balance_case_left_left_sorted. eauto.
        ++ destruct ll_c; eauto.
          --- destruct lr_c; eauto.
              ** destruct cr; eauto.
                destruct rl; eauto;
                try(destruct rr); eauto;
                try(destruct c); eauto;
                try(destruct c0); eauto;
                try(apply balance_case_right_right_sorted; eauto).  
                +++ apply smaller_node_inv in Hsm_v as [Hlt_rv [Hsm_left Hsm_right]].
                    apply rb_sorted_node_inv in Hrb_r as [Hgt_rv [Hsm_rv [Hrb_rl Hrb_rr]]].
                    apply rb_sorted_node_inv in Hrb_rl as [Hgt_n [Hsm_n [Hrb_rl1 Hrb_rl2]]].
                    apply greater_node_inv in Hgt_rv as [Hrv_gt_n [Hrv_gt_rl1 Hrv_gt_rl2]].
                    apply smaller_node_inv in Hsm_left as [Hlt_n [Hsm_v_rl1 Hsm_v_rl2]].
                    assert (Hsm_v_rl2_leaf : smaller v (node Red rl2 rv_r leaf)).
                    { constructor;  eauto. }
                    constructor; eauto. 
                +++ apply smaller_node_inv in Hsm_v as [Hlt_rv [Hsm_left Hsm_right]].
                    apply smaller_node_inv in Hsm_left as [Hlt_n [Hsm_v_rl1 Hsm_v_rl2]].
                    apply rb_sorted_node_inv in Hrb_r as [Hgt_rv [Hsm_rv [Hrb_rl Hrb_rr]]].
                    apply rb_sorted_node_inv in Hrb_rl as [Hgt_n [Hsm_n [Hrb_rl1 Hrb_rl2]]].  
                    apply greater_node_inv in Hgt_rv as [Hrv_gt_n [Hrv_gt_rl1 Hrv_gt_rl2]].
                    assert (Hn_lt_rv : n < rv_r) by lia.
                    pose proof (smaller_decrease n rv_r (node Black rr1 n0 rr2) Hn_lt_rv Hsm_rv) as Hsm_n_rr.
                    (* right subtree sorted: node Red rl2 rv_r (node Black rr1 n0 rr2) *)
                    assert (Hrb_right : rb_sorted (node Red rl2 rv_r (node Black rr1 n0 rr2))).
                    { constructor; assumption. }
                    constructor; eauto.
                +++ apply smaller_node_inv in Hsm_v as [Hlt_rv [Hsm_left Hsm_right]].
                    apply smaller_node_inv in Hsm_left as [Hlt_n [Hsm_v_rl1 Hsm_v_rl2]].
                    apply rb_sorted_node_inv in Hrb_r as [Hgt_rv [Hsm_rv [Hrb_rl Hrb_rr]]].
                    apply rb_sorted_node_inv in Hrb_rl as [Hgt_n [Hsm_n [Hrb_rl1 Hrb_rl2]]].  
                    apply greater_node_inv in Hgt_rv as [Hrv_gt_n [Hrv_gt_rl1 Hrv_gt_rl2]].
                    assert (Hn_lt_rv : n < rv_r) by lia.
                    pose proof (smaller_decrease n rv_r (node Red rr1 n0 rr2) Hn_lt_rv Hsm_rv) as Hsm_n_rr.
                    constructor; eauto.
              ** destruct rr; eauto;
                 apply balance_case_left_right_sorted; eauto.
            --- apply balance_case_left_left_sorted. eauto.
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
Qed.


Ltac solve_no_red_red :=
  repeat match goal with
  | [ |- no_red_red leaf ] => constructor
  | [ H: no_red_red ?t |- no_red_red ?t ] => exact H
  | [ |- no_red_red (node Black ?l ?x ?r) ] =>
      (* black node: both children must be no_red_red *)
      apply nr_node_black
  | [ |- no_red_red (node Red ?l ?x ?r) ] =>
      (* red node: children must not be Red and must satisfy no_red_red *)
      apply nr_node_red; try (match goal with
                              | [ H: context[node Red _ _ _] |- _ ] => discriminate
                              | _ => constructor
                              end)
  end; try assumption.
   
Lemma balance_preserves_no_red_red :
  forall t, no_red_red t -> no_red_red (balance t).
Proof.
  intros [|c l v r] H; simpl. 
  - constructor.
  - destruct c; try(solve_no_red_red).
    + inv H. 
      destruct l as [| lc ll lv_l lr]; destruct r as [| rc rl rv_r rr]; simpl;
      try(destruct lc);
      try(solve_no_red_red).
      * destruct rc; try(solve_no_red_red).
        destruct rl; try (destruct rr); try(solve_no_red_red);
        destruct c; try(solve_no_red_red);
        try(destruct c0); inv H2; inv H4; inv H6; inv H5; eauto;
        try(solve_no_red_red).
      * destruct ll; try(destruct lr); try(solve_no_red_red);
        destruct c; try(solve_no_red_red);
        try(destruct c0); inv H2; inv H4; inv H6; inv H5; eauto.
        repeat(constructor); eauto; inv H7; eauto.
      * destruct rc; try(destruct rl); try(destruct rr); try(solve_no_red_red);
        destruct c; try(destruct c0); inv H2; inv H4; inv H6; inv H5; eauto;
        repeat(constructor); eauto; inv H7; inv H8; eauto.
      * destruct ll; try(destruct lr); try(destruct rc); 
        try(destruct rl); try(destruct rr); 
        try(solve_no_red_red);
        destruct c;
        try(destruct c0); inv H2; inv H4; inv H6; inv H5; inv H7; eauto;
        try(solve_no_red_red); inv H10; eauto; inv  H9; eauto;
        repeat(constructor); eauto.
Qed.


Ltac bh_prepare H :=
  lazymatch type of H with
  | black_height (node Black ?l ?v ?r) = Some ?k =>
      let Heq := fresh "Hbh" in
      pose proof H as Heq; simpl in Heq;
      remember (black_height l) as Hbl eqn:Hl;
      remember (black_height r) as Hbr eqn:Hr;
      destruct Hbl as [hl|] eqn:Ehl; [ | discriminate Heq ];
      destruct Hbr as [hr|] eqn:Ehr; [ | discriminate Heq ];
      destruct (Nat.eqb hl hr) eqn:Heqbh; [ apply Nat.eqb_eq in Heqbh; subst hr | discriminate Heq ];
      injection Heq as Hk; clear Heq; subst k
  | _ => fail "bh_prepare: hypothesis must have form black_height (node Black l v r) = Some k"
  end.

Ltac bh_solve H :=
  lazymatch type of H with
  | black_height (node Black ?l ?v ?r) = Some ?k =>
      let Heq := fresh "Hbh" in
      pose proof H as Heq; simpl in Heq;
      remember (black_height l) as Hbl eqn:Hl;
      remember (black_height r) as Hbr eqn:Hr;
      destruct Hbl as [hl|] eqn:Ehl; [ | discriminate Heq ];
      destruct Hbr as [hr|] eqn:Ehr; [ | discriminate Heq ];
      destruct (Nat.eqb hl hr) eqn:Heqbh; [ apply Nat.eqb_eq in Heqbh; subst hr | discriminate Heq ];
      injection Heq; intros; clear Heq;
      (* simplify the goal using the recorded Hl/Hr and finish if possible *)
      repeat (rewrite Hl || rewrite Hr); simpl; try reflexivity
  | _ => fail "bh_solve: hypothesis must have form black_height (node Black l v r) = Some k"
  end.


Ltac bh_solve_test H :=
  lazymatch type of H with
  | black_height (node Black ?l ?v ?r) = Some ?k =>
      let Heq := fresh "Hbh" in
      pose proof H as Heq; simpl in Heq;
      remember (black_height l) as Hbl eqn:Hl1;
      remember (black_height r) as Hbr eqn:Hr1;
      destruct Hbl as [hl|] eqn:Ehl1; [ | discriminate Heq ];
      destruct Hbr as [hr|] eqn:Ehr1; [ | discriminate Heq ];
      destruct (Nat.eqb hl hr) eqn:Heqbh; [ apply Nat.eqb_eq in Heqbh; subst hr | discriminate Heq ];
      injection Heq; intros; clear Heq;
      (* simplify the goal using the recorded Hl/Hr and finish if possible *)
      repeat (rewrite Hl1 || rewrite Hr1); simpl; try reflexivity
  | _ => fail "bh_solve: hypothesis must have form black_height (node Black l v r) = Some k"
  end.

Lemma balance_preserves_bh :
  forall t k, black_height t = Some k -> black_height (balance t) = Some k.
Proof.
  intros [|c l v r] k H; simpl. 
  - assumption.
  - destruct c;
    try(bh_solve H); eauto.
    destruct l; destruct r; simpl.
    + repeat (rewrite Hl || rewrite Hr); eauto.
    + simpl in Hl;
      inv Hl;
      symmetry in Hr. 
      destruct c; simpl. 
      * eauto. 
      * destruct r1; simpl.
        -- destruct r2; eauto. destruct c; eauto.  
            simpl in Hr.
            remember (black_height (node Red r2_1 n0 r2_2)) as hrr eqn:Ehrr.
            destruct hrr as [h|] eqn:Ehrr'.
            ++ simpl in Hr. destruct (0 =? h) eqn:E0h. 
              **  apply Nat.eqb_eq in E0h. subst h.
                  simpl in Ehrr. 
                  remember (black_height r2_1) as hb1 eqn:Ehb1.
                  remember (black_height r2_2) as hb2 eqn:Ehb2.
                  destruct hb1 as [b1|] eqn:E1; [ | discriminate Ehrr ]. destruct hb2 as [b2|] eqn:E2; [ | discriminate Ehrr ].
                  destruct (Nat.eqb b1 b2) eqn:Ebb; [ apply Nat.eqb_eq in Ebb; subst b2 | discriminate Ehrr ].
                  injection Ehrr as Hb; rewrite Nat.add_0_r in Hb.          (* Hb : 0 = b1 *)
                  symmetry in Hb. subst b1. simpl. rewrite <- Ehb1, <- Ehb2.
                  simpl. reflexivity. 
              **  simpl in Ehrr.
                  remember (black_height r2_1) as A eqn:EA.
                  remember (black_height r2_2) as B eqn:EB.
                  destruct A as [h1|]; try discriminate.
                  destruct B as [h2|]; try discriminate.
                  destruct (Nat.eqb h1 h2) eqn:E12; try discriminate.
                  apply Nat.eqb_eq in E12; subst h2.
                  inversion Ehrr; subst h; clear Ehrr.
                  simpl in Hr.
                  inversion Hr;
                  destruct h1; simpl in Hr; [discriminate E0h | discriminate Hr].
            ++ simpl in Hr.  
              remember (black_height r2_1) as A eqn:EA.
              remember (black_height r2_2) as B eqn:EB.
              destruct A as [h1|]; try discriminate.
              destruct B as [h2|]; try discriminate.
              destruct (Nat.eqb h1 h2) eqn:E12; try discriminate.
              apply Nat.eqb_eq in E12; subst h2.
              inversion Ehrr.
              simpl in Hr.
              inversion Hr.
              rewrite H1 in H2. simpl in H2.
              symmetry in EA; symmetry in EB.
              simpl. rewrite EA, EB.    
              destruct h1; simpl in Hr; [rewrite H1; eauto | discriminate Hr].
        -- destruct r2; simpl; destruct c; try (destruct c0); eauto.
            ++ simpl in H.
              remember (black_height (node Red (node Red r1_1 n0 r1_2) n leaf)) as hr eqn:Eh.
              destruct hr as [h|] eqn:Ehr.
              simpl in H.
              destruct (0 =? h) eqn:E0h.
               **  apply Nat.eqb_eq in E0h. subst h.
                  simpl in Eh. 
                  remember (black_height r1_1) as hb1 eqn:Ehb1.
                  remember (black_height r1_2) as hb2 eqn:Ehb2.
                  destruct hb1 as [b1|] eqn:E1; [ | discriminate Eh ]. destruct hb2 as [b2|] eqn:E2; [ | discriminate Eh ].
                  destruct (Nat.eqb b1 b2) eqn:Ebb; [ apply Nat.eqb_eq in Ebb; subst b2 | discriminate Eh ].
                  rewrite Nat.add_0_r in Eh. subst hb1.          (* Hb : 0 = b1 *)
                  symmetry in Eh.  simpl. rewrite <- Ehb1, <- Ehb2.
                  simpl. eauto. admit. 
              **  simpl in Eh.
                  remember (black_height r1_1) as A eqn:EA.
                  remember (black_height r1_2) as B eqn:EB.
                  destruct A as [h1|]; try discriminate.
                  destruct B as [h2|]; try discriminate.
                  destruct (Nat.eqb h1 h2) eqn:E12; try discriminate.
                  apply Nat.eqb_eq in E12; subst h2.
                  inversion Eh; subst hr; clear Eh.
                  simpl in Hr.
                  inversion Hr. simpl; admit.
                  (* destruct h1; simpl in Hr; [discriminate E0h | discriminate Hr]. *)
                ** admit.
            ++ admit.
            ++ admit.
            ++ admit.
    + destruct c; eauto. destruct l1.
      * destruct l2; eauto. destruct c; eauto. 
        simpl in Hr. injection Hr. clear Hr.   
        intros.
        rewrite H1 in Hl;      
        remember (black_height (node Red l2_1 n0 l2_2)) as hrr eqn:Ehrr.
        destruct hrr as [h|] eqn:Ehrr'.
        --  subst k. destruct (0 =? h) eqn:E0h.
          ++ (*true*)
            apply Nat.eqb_eq in E0h. subst h.
            simpl in Ehrr. 
            remember (black_height l2_1) as hb1 eqn:Ehb1.
            remember (black_height l2_2) as hb2 eqn:Ehb2.
            destruct hb1 as [b1|] eqn:E1; [ | discriminate Ehrr ]. destruct hb2 as [b2|] eqn:E2; [ | discriminate Ehrr ].
            destruct (Nat.eqb b1 b2) eqn:Ebb; [ apply Nat.eqb_eq in Ebb; subst b2 | discriminate Ehrr ].
            injection Ehrr as Hb; rewrite Nat.add_0_r in Hb.          (* Hb : 0 = b1 *)
            symmetry in Hb. subst b1. simpl. rewrite <- Ehb1, <- Ehb2.
            simpl. rewrite H1. reflexivity. 
        ++ (* false *) 
           simpl in Ehrr.
           remember (black_height l2_1) as A eqn:EA.
           remember (black_height l2_2) as B eqn:EB.
           destruct A as [h1|]; try discriminate.
           destruct B as [h2|]; try discriminate.
           destruct (Nat.eqb h1 h2) eqn:E12; try discriminate.
           apply Nat.eqb_eq in E12; subst h2.
           inversion Ehrr; subst h; clear Ehrr.
           simpl in Hl.
           rewrite <- EB in Hl. 
           rewrite <- EA in Hl. 
           rewrite Nat.eqb_refl in Hl.
           inversion Hl;
           destruct h1; simpl in Hl; [discriminate E0h | discriminate Hl].
      -- simpl in Hl.  
        remember (black_height l2_1) as A eqn:EA.
        remember (black_height l2_2) as B eqn:EB.
        destruct A as [h1|]; try discriminate.
        destruct B as [h2|]; try discriminate.
        destruct (Nat.eqb h1 h2) eqn:E12; try discriminate.
        apply Nat.eqb_eq in E12; subst h2.
        inversion Ehrr.
        simpl in Hl.
        inversion Hl.
        rewrite H1 in H0. simpl in H0. subst k.
        symmetry in EA; symmetry in EB.
        simpl. rewrite EA, EB. rewrite <- H1.   
        destruct h1; simpl in Hl; [rewrite H1; eauto | discriminate Hl].
      * destruct c; eauto; destruct l2; admit.
    + admit.
Admitted.

(* Helper Lemmas for rb_insert_aux_preservers_invariant*)
Lemma rb_invariant_subtrees :
forall c l v r k,
    black_height (node c l v r) = Some k ->
    rb_sorted (node c l v r) ->
    no_red_red (node c l v r) ->
    (rb_sorted l /\ no_red_red l /\ exists nl, black_height l = Some nl) /\
    (rb_sorted r /\ no_red_red r /\ exists nr, black_height r = Some nr).
Proof. 
  intros c l v r k Hbh Hsorted Hnored.
  simpl in Hbh.
  destruct (black_height l) eqn:Hl; [ | discriminate Hbh ].
  destruct (black_height r) eqn:Hr; [ | discriminate Hbh ].
  destruct (Nat.eqb n n0) eqn:Heq; [ apply Nat.eqb_eq in Heq; subst n0 | discriminate Hbh ].
  injection Hbh; intros; clear Hbh; subst k.
  apply rb_sorted_node_inv in Hsorted as [Hgt_lv [Hsm_vr [Hrb_l Hrb_r]]].
  inversion Hnored as [| ? ? ? Hnored_l Hnored_r | ? ? ? ? ? Hnored_l Hnored_r]; clear Hnored.
  repeat(split; eauto). repeat (split); eauto.
Qed.

Lemma smaller_preserved_by_insert_right :
  forall v x r,
    smaller v r ->
    v <? x = true ->
    smaller v (rb_insert_aux x r).
Proof.
  intros. unfold rb_insert_aux. simpl. eauto.
Admitted. 
Lemma greater_preserved_by_insert_left :
  forall v x l,
    greater v l ->
    x <? v = true ->
    greater v (rb_insert_aux x l).
Proof. Admitted.

Lemma rb_insert_aux_preserves_bh_subtree :
  forall x t k,
    black_height t = Some k ->
    black_height (rb_insert_aux x t) = Some k.
Proof. Admitted.


Ltac bh_prepare_new H :=
  lazymatch type of H with
  | black_height (node Black ?l ?v ?r) = Some ?k =>
      let Hcopy := fresh "Hbh_copy" in
      let Heqn := fresh "Hbh_eq" in
      remember H as Hcopy eqn:Heqn;
      simpl in Heqn;
      remember (black_height l) as Hbl eqn:Hl;
      remember (black_height r) as Hbr eqn:Hr;
      destruct Hbl as [hl|] eqn:Ehl; [ | discriminate Heqn ];
      destruct Hbr as [hr|] eqn:Ehr; [ | discriminate Heqn ];
      destruct (Nat.eqb hl hr) eqn:Heqbh; [ apply Nat.eqb_eq in Heqbh; subst hr | discriminate Heqn ];
      injection Heqn as Hk; clear Heqn; subst k
  | _ => fail "bh_prepare: hypothesis must have form black_height (node Black l v r) = Some k"
  end.

Lemma balance_preserves_black_height :
  forall t k, black_height t = Some k ->
              black_height (balance t) = Some k.
Proof.
Admitted.


(* Maybe change to this and then undo the change to invarient *)
(* forall x t,
    rb_invariant t ->
    root_black t ->                      (* ADDED *)
    rb_sorted (rb_insert_aux x t) /\ no_red_red (rb_insert_aux x t) /\
    exists k, black_height (rb_insert_aux x t) = Some k. *)



Lemma rb_insert_aux_preserves_invariant :
  forall x t,
    rb_invariant t ->
    root_black t ->                      (* ADDED *)
    rb_sorted (rb_insert_aux x t) /\ no_red_red (rb_insert_aux x t) /\
    exists k, black_height (rb_insert_aux x t) = Some k. 
Proof.
Admitted.
  (* intros x t Hinv.
  revert k Hbh.
  induction t as [| c l IHl v r IHr]; intros k Hbh; simpl.
  - (* leaf *)
    repeat split; try constructor; eauto.
  - (* node *)
    destruct (v =? x) eqn:Heq.
    + (* equal: unchanged *)
      repeat split; eauto.
    + destruct (v <? x) eqn:Hlt.
      * (* insert into right *)
        pose proof (rb_invariant_subtrees c l v r k Hbh Hsorted Hnored) as [Hinvl Hinvr].
        destruct Hinvr as [Hsorted_r [Hnored_r [kr Hkr]]];
        specialize (IHr Hsorted_r Hnored_r kr Hkr);
        destruct IHr as [Hsorted_r' [Hnored_r' [kr' Hkr']]];
        (* pre-balance: node c l v r' is sorted *)
        assert (Hnode_sorted : rb_sorted (node c l v (rb_insert_aux x r))).
        { apply rb_sorted_node_inv in Hsorted as [Hgt [Hsm [Hrl Hrr]]].
          constructor; eauto. try (apply smaller_preserved_by_insert_right); eauto. }
        remember (rb_insert_aux x r) as r'.
        destruct Hinvl as [Hsorted_l [Hnored_l [kl Hkl]]].
        pose proof (nr_node_black v l r' Hnored_l Hnored_r') as Hpre_no_red.
        destruct c.
        --  pose proof (balance_preserves_sorted (node Black l v r') Hnode_sorted) as Hbal_sorted.
            pose proof (balance_preserves_no_red_red (node Black l v r') Hpre_no_red) as Hbal_nored.
            simpl in Hbh.
            rewrite Hkl in Hbh.    (* black_height l = Some kl *)
            rewrite Hkr in Hbh.    (* black_height r = Some kr *)
            destruct (Nat.eqb kl kr) eqn:Heqbh; [ apply Nat.eqb_eq in Heqbh; subst kr | discriminate Hbh ].
            injection Hbh as Hk; subst k.
            pose proof (rb_insert_aux_preserves_bh_subtree x r kl Hkr) as Hbr'.
            rewrite <- Heqr' in Hbr'.   (* now Hbr' : black_height r' = Some kl *)
            split; eauto.
            split;eauto.
            exists (kl + 1).
            assert (Hbht : black_height (node Black l v r') = Some (kl + 1)).
            { simpl. rewrite Hkl, Hbr'. rewrite Nat.eqb_refl. reflexivity. }
            pose proof (balance_preserves_black_height (node Black l v r') (kl + 1) Hbht) as Hbh_bal. eauto.
        -- pose proof (balance_preserves_sorted (node Red l v r') Hnode_sorted) as Hbal_sorted.
           (* pose proof (balance_preserves_no_red_red (node Red l v r') Hpre_no_red) as Hbal_nored. *)
           simpl in Hbh.
           rewrite Hkl in Hbh.    
           rewrite Hkr in Hbh.
            destruct (Nat.eqb kl kr) eqn:Heqbh; [ apply Nat.eqb_eq in Heqbh; subst kr | discriminate Hbh ].
            injection Hbh as Hk; subst k.
            pose proof (rb_insert_aux_preserves_bh_subtree x r kl Hkr) as Hbr'.
            rewrite <- Heqr' in Hbr'.   (* now Hbr' : black_height r' = Some kl *)
            split; eauto.
            split;eauto.
            ++ admit.
            ++ exists (kl + 1).
            assert (Hbht : black_height (node Red l v r') = Some (kl + 1)).
            { simpl. rewrite Hkl, Hbr'. rewrite Nat.eqb_refl.  eauto. }
            pose proof (balance_preserves_black_height (node Red l v r') (kl + 1) Hbht) as Hbh_bal. eauto.
            
        (* inv Hnored. 
          destruct r' as [ | rc rl rv rr ] eqn:Er'.
          ++ exfalso. apply (rb_insert_aux_never_leaf x r). symmetry. assumption.
          ++ destruct rc.
        (* sortedness after balance *)
        apply balance_preserves_sorted; eauto. *)
        (* no-red-red after balance *)
    * admit.
Admitted. *)
(*   intros x t [Hsorted [Hnored [k Hbh]]].
  revert k Hbh.
  induction t as [| c l IHl v r IHr]; intros k Hbr; simpl.
  - (*leaf*)
    repeat(split); try(constructor); eauto.
  -(*node*)
    destruct(v=?x) eqn:Heq.
    + (*equal: do nothing*)
      repeat(split); eauto.
    + destruct(v <? x) eqn:Hlt.
       pose proof (rb_invariant_subtrees c l v r k Hbr Hsorted Hnored) as [Hinvl Hinvr].
        destruct Hinvr as [Hsorted_r [Hnored_r [kr Hkr]]].
        specialize (IHr Hsorted_r Hnored_r kr Hkr).
        destruct IHr as [Hsorted_r' [Hnored_r' [kr' Hkr']]].
        assert (Hnode_sorted : rb_sorted (node c l v (rb_insert_aux x r))).
        { apply rb_sorted_node_inv in Hsorted as [Hgt [Hsm [Hrl Hrr]]].
          constructor; eauto. apply smaller_preserved_by_insert_right; eauto. }
        assert (Hnode_no_red : no_red_red (node c l v (rb_insert_aux x r))).
        { inv Hnored. apply nr_node_black; eauto. apply nr_node_red; eauto. constructor; eauto. constructor; eauto.  }


      pose proof (IHr kr Hkr Hsorted_r Hnored_r) as IHr_res.
      pose proof (rb_invariant_subtrees c l r IHl k Hbh Hsorted Hnored) as [Hinvl Hinvr].
      destruct Hinvr as [Hsorted_r [Hnored_r [kr Hkr]]].
      (* destruct IHr as [Hsorted_r' [Hnored_r' [kr' Hkr']]]. *)
      (* insert into left subtree *)
      pose proof (IHr Hsorted_r Hnored_r Hkr) as IHr_res.
      destruct IHr_res as [Hsorted_r' [Hnored_r' [kr' Hkr']]].
        specialize (IHr x Hinvr).
        destruct IHr as [Hsorted_r' [Hnored_r' [kr Hkr]]].
        (* node before balance is sorted/no_red_red and has bh *)
        assert (Hnode_sorted : rb_sorted (node c l v (rb_insert_aux x r))).
        { (* greater v l from original sorted; smaller v (rb_insert_aux x r) from helper *)
          apply rb_sorted_node_inv in Hsorted as [Hgt [Hsm [Hrl Hrr]]].
          constructor.
          - (* greater v l *) assumption.
          - (* smaller v new right *) apply smaller_preserved_by_insert_right; assumption.
          - (* rb_sorted l *) assumption.
          - (* rb_sorted new right *) assumption.
        }
        assert (Hnode_no_red : no_red_red (node c l v (rb_insert_aux x r))).
        { apply nr_node_black || apply nr_node_red. inv Hnored; assumption. } *)

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
  intros x t Hinv.
  unfold rb_insert.
  pose proof (rb_insert_aux_preserves_invariant x t Hinv) as Haux.
  (* destruct Hinv as [Hsorted [Hnored [Hno_red_red [k Hbh]]]]. *)
  remember (rb_insert_aux x t) as t'.
  destruct t' as [ | c l v r ] eqn:E.
  - (* impossible by lemma *)
    exfalso. apply (rb_insert_aux_never_leaf x t). symmetry. assumption.
  -  
    destruct Haux as [Hsorted' [Hnored' [k' Hbh']]].
    +  (* sortedness preserved *)
       
    + split.
      *  (* no-red-red preserved *)
      apply rb_sorted_node_inv in Hsorted' as [Hgt [Hsm [Hrl Hrr]]].
      constructor; eauto.
      *  (* black-height preserved *)
      pose proof (recolor_preserves_no_red_red c l v r Hnored') as Hnored_black.
      split; [eauto | exists k; eauto]. admit.
      (* apply rb_insert_aux_preserves_bh_subtree.
      -- split; [eauto | exists k; eauto].  *)
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