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

Ltac solve_bh_from_hyp :=
  match goal with
  | [ H : _ |- _ ] =>
    let Ht := fresh "Hbh" in
    (* Work on a local copy so we can clear it after inversion *)
    pose proof H as Ht;
    simpl in Ht;
    (* remember and destruct any nested black_height calls *)
    repeat match type of Ht with
    | context[black_height ?t] =>
        let He := fresh "He" in
        remember (black_height t) as He eqn:He;
        destruct (black_height t) eqn:He; [ clear He | discriminate Ht ]
    end;
    (* destruct Nat.eqb occurrences, turning true branches into equalities *)
    repeat match type of Ht with
    | context[Nat.eqb ?a ?b] =>
        let E := fresh "E" in
        destruct (Nat.eqb a b) eqn:E;
        [ apply Nat.eqb_eq in E; subst a | discriminate Ht ]
    end;
    (* now Ht must be of shape Some _ = Some _; invert it to get numeric equalities *)
    inversion Ht; clear Ht; try subst
  end.

(* usage: `solve_bh_from_hyp.` after you have `H1` (or whichever hyp) in context,
   then `simpl; reflexivity.` to close the goal. *)

Ltac invert_bh H :=
  simpl in H;
  (* 1. Handle the nested match black_heights *)
  repeat match type of H with
  | context[match black_height ?t with _ => _ end] =>
      destruct (black_height t) eqn:?; try discriminate
  end;
  (* 2. Handle the boolean equality checks *)
  repeat match type of H with
  | context[if Nat.eqb ?n ?m then _ else _] =>
      (* Generate a unique name "Heq" to avoid conflicts in the loop *)
      let Heq := fresh "Heq" in
      (* Destruct using that specific name *)
      destruct (Nat.eqb n m) eqn:Heq; 
      [ 
        (* Now we can apply specifically to Heq *)
        apply Nat.eqb_eq in Heq; 
        subst 
      | 
        (* The false case *)
        discriminate 
      ]
  end;
  (* 3. Final cleanup *)
  inversion H; subst; clear H.
Ltac solve_balance_bh :=
  repeat match goal with
    (* Solve impossible constructor equalities *)
    | [ |- None = Some _ ] => 
        exfalso; try congruence; try lia
    | [ |- Some _ = None ] => 
        exfalso; try congruence; try lia

    (* Merge conflicting black_height hypotheses *)
    | [ H1: black_height ?t = Some ?v1, H2: black_height ?t = Some ?v2 |- _ ] => 
        assert (v1 = v2) by (rewrite H1 in H2; injection H2; auto);
        subst; 
        clear H2

    | [H: black_height _ = Some _ |- _] => 
        invert_bh H; simpl
    | [ H: Some _ = Some _ |- _ ] => 
        injection H as H; try subst
    | [ H: ?x = ?y |- _ ] => 
        first [ 
            discriminate H 
          | is_var x; subst x 
          | is_var y; subst y 
        ]

    (* Destruct stuck boolean checks (Goal) *)
    | [ |- context [ if ?n =? ?m then _ else _ ] ] => 
        destruct (Nat.eqb_spec n m); simpl

    (* Destruct stuck Nat matches (Goal) *)
    | [ |- context [ match ?n with | 0 => _ | S _ => _ end ] ] => 
        is_var n; destruct n; simpl

    (* Destruct stuck Colors/Variables *)
    | [ |- context [ match ?c with | Red => _ | Black => _ end ] ] => 
        is_var c; 
        destruct c; 
        simpl in *

    (* 9. Destruct stuck Boolean checks inside Hypotheses *)
    | [ H: context [ match (if ?n =? ?m then _ else _) with _ => _ end ] |- _ ] => 
        destruct (Nat.eqb_spec n m); simpl in H

    (* Arithmetic Simplification *)
    | [ |- context [ color_eqb _ ] ] => unfold color_eqb      
    | [ |- context [ ?n =? ?n ] ] => rewrite Nat.eqb_refl
    | [ |- context [ _ + 1 ] ] => rewrite Nat.add_1_r; simpl
    | [ H: context [ _ + 1] |- _] => rewrite Nat.add_1_r in H; simpl in H
    | [ |- context [ _ + 0 ] ] => rewrite Nat.add_0_r
    | [ H: context [ _ + 0 ] |- _ ] => rewrite Nat.add_0_r in H

    (* Final Solvers *)
    | [ |- black_height _ = _ ] => simpl
    | [ Heqon: black_height _ = Some _ |- _] => rewrite Heqon
    | [ |- _ = _ ] => reflexivity
    | [ |- _ ] => assumption
  end.


Lemma balance_preserves_bh :
  forall t k, black_height t = Some k -> black_height (balance t) = Some k.
Proof.
  intros [|c l v r] k H; simpl; [assumption|].
  destruct c; [| simpl in *; assumption].
  destruct l as [|lc ll lv lr]; destruct r as [|rc rl rv rr].
  - assumption.
  - destruct rc; [assumption|].
    destruct rl as [| rlc rll rlv rlr]; destruct rr as [| rrc rrl rrv rrr]; try (simpl; assumption).
    + destruct rrc; try assumption. invert_bh H; simpl; rewrite H1; simpl. rewrite Heqo; rewrite Heqo0.
      rewrite Nat.eqb_refl.  replace (n0 + 0) with n0 in H1 by lia. destruct n0 eqn:Hn0.
      * injection H1; intros; subst. simpl. reflexivity.
      * inversion H1.
    + destruct rlc; try assumption. invert_bh H; simpl; rewrite H1; simpl. rewrite Heqo; rewrite Heqo0.
      replace (n0 + 0 + 0) with n0 in H1 by lia. destruct n0 eqn:Hn0.
      * rewrite Nat.eqb_refl. simpl. assumption.
      * inversion H1.
    + destruct rlc; destruct rrc; try assumption.
      * invert_bh H; simpl. rewrite H1. rewrite Heqo. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. rewrite Nat.eqb_refl.
        replace (n0 + 1 + 0) with (n0 + 1) in H1 by lia. Search(_+1). rewrite Nat.add_1_r in H1. inversion H1.
      * invert_bh H; simpl. rewrite H1. rewrite Heqo. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. rewrite Nat.eqb_refl.
        replace (n0 + 0 + 0) with (n0 + 0) in H1 by lia. rewrite Heq in H1. rewrite Nat.add_1_r in H1. inversion H1.
      * invert_bh H; simpl. rewrite H1. rewrite Heqo. rewrite Heqo0. rewrite Heqo1. rewrite Heqo2. rewrite Nat.eqb_refl.
        replace (n0 + 0 + 0) with (n0) in H1 by lia. destruct n0 eqn:Hn0.
        -- rewrite <- Heq. simpl. assumption.
        -- assumption.
  - destruct lc; [assumption|].
    destruct ll as [| llc lll llv llr]; destruct lr as [|lrc lrl lrv lrr]; try (simpl; assumption).
    + destruct lrc; try assumption. invert_bh H; simpl. rewrite H1. rewrite Heqo; rewrite Heqo0.
      replace (n0 + 0) with n0 in H1 by lia. destruct n0.
      * simpl in *. assumption.
      * assumption.
    + destruct llc; try assumption. invert_bh H; simpl. rewrite Heqo. rewrite Heqo0. 
      replace (n0 + 0) with n0 in Heq by lia. rewrite Heq. simpl in *. reflexivity.

    + destruct llc; destruct lrc; try assumption.
      * invert_bh H; simpl. lia.
      * invert_bh H; simpl. lia. 
      * invert_bh H; simpl. rewrite Heqo, Heqo0, Heqo1, Heqo2. repeat rewrite Nat.eqb_refl.
        assert (n2 = 0) by lia. rewrite H. rewrite Nat.eqb_refl. assert (n0 = 0) by lia. rewrite H0. simpl. reflexivity. 
  - destruct lc; destruct rc; try assumption.
    + destruct rl as [| rlc rll rlv rlr]; destruct rr as [| rrc rrl rrv rrr]; try assumption.
      * destruct rrc; try assumption. invert_bh H; simpl. rewrite Heqo, Heqo0, Heqo1, Heqo2.
        repeat rewrite Nat.eqb_refl. rewrite H1. rewrite Nat.add_1_r. simpl. destruct (n2+0).
        -- rewrite Nat.add_1_r in H1. simpl in H1. assumption.
        -- assumption.
      * destruct rlc; try assumption. invert_bh H; simpl. rewrite Heqo, Heqo0, Heqo1, Heqo2. 
        replace (n0+1) with n2 by lia. replace (n2) with 0 by lia.  repeat rewrite Nat.eqb_refl. reflexivity.
      
      * destruct rlc; destruct rrc; try assumption.
        -- invert_bh H; simpl; rewrite Heqo, Heqo0, Heqo1, Heqo2, Heqo3, Heqo4.
           replace (n0 + 1) with (n2 + 1) by lia. 
           repeat rewrite Nat.eqb_refl.
           replace (n2 + 1 + 1) with (n4 + 1) by lia. 
           rewrite Nat.eqb_refl. auto.
        -- invert_bh H; simpl; rewrite Heqo, Heqo0, Heqo1, Heqo2, Heqo3, Heqo4.
           replace (n0 + 1) with (n2 ) by lia. 
           repeat rewrite Nat.eqb_refl.
           replace (n2) with (n4 + 1) by lia. 
           repeat rewrite Nat.eqb_refl. auto. 
        -- invert_bh H; simpl; rewrite Heqo, Heqo0, Heqo1, Heqo2, Heqo3, Heqo4.
           replace (n0 + 1) with (n2 ) by lia. 
           repeat rewrite Nat.eqb_refl.
           replace (n2) with (n4 + 0) by lia. 
           repeat rewrite Nat.eqb_refl. auto.      
    + destruct ll as [| llc lll llv llr]; destruct lr as [| lrc lrl lrv lrr]; try assumption.
      * destruct lrc; try assumption. invert_bh H; simpl; rewrite H1.
        -- rewrite Heqo, Heqo0, Heqo1, Heqo2. destruct n0 eqn:Hn0; destruct (n1 =? n2) eqn:Heq; try assumption.
           rewrite Nat.add_1_r. simpl in *. rewrite Nat.add_1_r in H1. assumption.
        -- rewrite Heqo, Heqo0, Heqo1, Heqo2. destruct n0; try assumption.
        -- rewrite Heqo, Heqo0, Heqo1. destruct n0; try assumption.
    
      * invert_bh H; simpl. destruct llc; simpl; try assumption.
        -- unfold color_eqb in Heq. rewrite Nat.add_1_r in Heq. inversion Heq. 
        -- unfold color_eqb in Heq0, Heq. lia.
      
      * destruct llc; try assumption; invert_bh H; simpl.
        -- destruct lrc; try assumption; simpl. rewrite Heqo, Heqo0, Heqo1, Heqo2, Heqo3, Heqo4;
           repeat rewrite Nat.eqb_refl.
           --- unfold color_eqb in Heq. rewrite Heq. rewrite Nat.eqb_refl. replace (n2+1+0) with (n4+1) by lia.
               rewrite Nat.eqb_refl. reflexivity.
           --- simpl in *. replace (n0+1) with n2 by lia. rewrite Heqo, Heqo0, Heqo1, Heqo2, Heqo3, Heqo4. repeat rewrite Nat.eqb_refl. replace n2 with (n4+1) by lia.
               repeat rewrite Nat.eqb_refl. rewrite Nat.add_0_r. replace (n0+1) with (n4+1) by lia. repeat rewrite Nat.eqb_refl. auto.
        -- rewrite Heqo, Heqo0, Heqo1, Heqo2, Heqo3, Heqo4. repeat rewrite Nat.eqb_refl. destruct (color_eqb lrc).
           --- replace (n2 + 0) with (n4 + 1) by lia. rewrite Nat.eqb_refl. replace (n0+1) with (n4+1+1) by lia.
               rewrite Nat.eqb_refl. replace (n4+1+1+0) with (n0+0+0+1) by lia. reflexivity.
           --- replace (n2 + S n) with (n4+1) by lia. rewrite Nat.eqb_refl. replace (n0+1) with (n4+1+1) by lia. rewrite Nat.eqb_refl.
               replace (n4+1+1+0) with (n0+0+0+1) by lia. reflexivity.     
    + destruct ll; destruct lr; destruct rl; destruct rr; try assumption; simpl;
    
    repeat match goal with

      (* Solve impossible constructor equalities*)
      | [ |- None = Some _ ] => 
          exfalso; try congruence; try lia
      | [ |- Some _ = None ] => 
          exfalso; try congruence; try lia

      (* Merge conflicting black_height hypotheses *)
      | [ H1: black_height ?t = Some ?v1, H2: black_height ?t = Some ?v2 |- _ ] => 
          assert (v1 = v2) by (rewrite H1 in H2; injection H2; auto);
          subst; 
          clear H2

      (* Invert domain-specific hypotheses *)
      | [H: black_height _ = Some k |- _] => 
          invert_bh H; simpl

      (* Inject/Subst simple equalities *)
      | [ H: Some _ = Some _ |- _ ] => 
          injection H as H; try subst
      | [ H: ?x = ?y |- _ ] => 
          first [ 
              discriminate H 
            | is_var x; subst x 
            | is_var y; subst y 
          ]

      (* Destruct stuck boolean checks (Goal) *)
      | [ |- context [ if ?n =? ?m then _ else _ ] ] => 
          destruct (Nat.eqb_spec n m); simpl

      (* Destruct stuck Nat matches (Goal) *)
      | [ |- context [ match ?n with | 0 => _ | S _ => _ end ] ] => 
          is_var n; destruct n; simpl

      (* Destruct stuck Colors/Variables *)
      | [ |- context [ match ?c with | Red => _ | Black => _ end ] ] => 
          is_var c; 
          destruct c; 
          simpl in *

      (* Destruct stuck Boolean checks inside Hypotheses *)
      | [ H: context [ match (if ?n =? ?m then _ else _) with _ => _ end ] |- _ ] => 
          destruct (Nat.eqb_spec n m); simpl in H

      (* Arithmetic Simplification *)
      | [ |- context [ color_eqb _ ] ] => unfold color_eqb      
      | [ |- context [ ?n =? ?n ] ] => rewrite Nat.eqb_refl
      | [ |- context [ _ + 1 ] ] => rewrite Nat.add_1_r; simpl
      | [ H: context [ _ + 1] |- _] => rewrite Nat.add_1_r in H; simpl in H
      | [ |- context [ _ + 0 ] ] => rewrite Nat.add_0_r
      | [ H: context [ _ + 0 ] |- _ ] => rewrite Nat.add_0_r in H

      (*  Final Solvers *)
      | [ |- black_height _ = _ ] => simpl
      | [ Heqon: black_height _ = Some _ |- _] => rewrite Heqon
      | [ |- _ = _ ] => reflexivity
      | [ |- _ ] => assumption
    end.
Qed.

Lemma balance_preserves_black_height :
  forall t k,
    black_height t = Some k ->
    exists k', black_height (balance t) = Some k'.
Proof.
  intros t k H.
  destruct t as [| c l v r]; simpl in *.
  - (* t = leaf *) inversion H; subst. simpl. exists 0. reflexivity.
  - (* t = node c l v r *)
    simpl in H.
    (* compute children black_heights *)
    destruct (black_height l) eqn:Hl; destruct (black_height r) eqn:Hr; try discriminate.
    destruct (Nat.eqb n n0) eqn:Heq; try discriminate.
    apply Nat.eqb_eq in Heq; subst.
    inversion H; subst k; clear H.
    (* Now do a case analysis on the shapes that `balance` matches.
       Most cases are simple: after simplification the black_height of
       the balanced tree is directly Some (...) using Hl and Hr. *)
    simpl.
    destruct c.
    + (* c = Black or Red: handle both the rotation patterns and no-op *)
      (* To handle the rotation patterns we inspect l and r constructors. *)
      destruct l as [| lc la lx lb]; simpl; try (exists (n + color_eqb Black); (simpl; rewrite Hl, Hr, Nat.eqb_refl; reflexivity)).
      * (* l = leaf *) 
        destruct r as [| rc ra rx rb]; simpl;
          try (exists (n + color_eqb Black); simpl; rewrite Hl, Hr, Nat.eqb_refl; reflexivity).
        -- (* r = node ... *) 
           (* no rotation: balance returns original node *)
           exists n0. simpl. rewrite <- Hl.  eauto. admit.
        -- (* other r-shapes covered by same computation *)
           exists n0. simpl. rewrite <- Hl. eauto. admit.
      * (* l = node lc la lx lb *)
        (* many subcases where balance rotates; in all cases the child black_heights
           are built from Hl and Hr and evaluation yields Some _ *)
        destruct la; destruct lb; destruct r; (* push through constructors *)
        try (exists n0; simpl; rewrite Hl, Hr, Nat.eqb_refl; eauto); eauto; admit.
    + (* c = Red *)
      (* balance only rotates when c = Black, so when c = Red balance is identity *)
      exists n0. simpl. rewrite Hl, Hr, Nat.eqb_refl. eauto.
Admitted.


Lemma smaller_preserved_by_insert_right :
  forall v x r,
    smaller v r ->
    (v <? x) = true ->
    smaller v (rb_insert_aux x r).
Proof.
  intros. induction r; simpl in *.
  - constructor; admit.
  - (* pattern: use IH, or use balance_preserves_sorted machinery for shapes *) admit.
Admitted.

Lemma greater_preserved_by_insert_left :
  forall v x l,
    greater v l ->
    (v <? x) = false ->
    (v =? x) = false ->
    greater v (rb_insert_aux x l).
Proof.
  intros. induction l; simpl in *.
  - constructor; admit.
  - admit.
Admitted.


Lemma rb_insert_aux_preserves_sorted :
  forall x t,
    rb_sorted t ->
    rb_sorted (rb_insert_aux x t).
Proof.
  intros x t H. 
  induction t as  [| c l IHl v r IHr]. (*do NOT revert anything here; induction on t and use balance_preserves_sorted for the node-case. *)
  - constructor; eauto.
  - 
    (* inv H. *)
    simpl. destruct (v =? x) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst; assumption.
    + destruct (v <? x) eqn:Hlt.
      * (* go right *)
        apply rb_sorted_node_inv in H as [Hgt_v [Hsm_v [Hrb_l Hrb_r]]].
        specialize (IHr Hrb_r).
        assert (Hsm_v_r' : smaller v (rb_insert_aux x r)).
        { apply smaller_preserved_by_insert_right with (x:=x); eauto. }
        assert (Hnode_sorted : rb_sorted (node c l v (rb_insert_aux x r))).
        { constructor; assumption. }
        eapply (balance_preserves_sorted (node c l v (rb_insert_aux x r)) Hnode_sorted).
      *  (* go left: symmetric *)
        apply rb_sorted_node_inv in H as [Hgt_v [Hsm_v [Hrb_l Hrb_r]]].
        specialize (IHl Hrb_l).
        assert (Hgt_l' : greater v (rb_insert_aux x l)).
        { apply greater_preserved_by_insert_left with (x:=x); try assumption. }
        assert (Hnode_sorted : rb_sorted (node c (rb_insert_aux x l) v r)).
        { constructor; try assumption. }
        eapply (balance_preserves_sorted (node c (rb_insert_aux x l) v r) Hnode_sorted).
Qed.

Inductive red_red_at_root : rb_tree -> Prop :=
| rr_left  : forall a x b y c, red_red_at_root (node Red (node Red a x b) y c)
| rr_right : forall a x b y c, red_red_at_root (node Red a x (node Red b y c)).


Lemma balance_preserves_no_red_red_or_root :
  forall c l v r,
    no_red_red l \/ red_red_at_root l ->
    no_red_red r \/ red_red_at_root r ->
    no_red_red (balance (node c l v r)) \/ red_red_at_root (balance (node c l v r)).
Proof. Admitted.


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

 (* Lemma rb_insert_aux_preserves_no_red_red :
  forall x t,
    no_red_red t ->
    no_red_red (rb_insert_aux x t)
    \/ red_red_at_root (rb_insert_aux x t).
Proof.
  intros x t Hn.
  induction t as [| c l IHl v r IHr]; simpl in *.
  - (* leaf *)
    left. constructor; eauto.
  - (* node *)
    destruct Hn.
    destruct Hn as [Hc |Hl Hr].
    remember (rb_insert_aux x l) as l' eqn:Hl'.
    remember (rb_insert_aux x r) as r' eqn:Hr'.
    destruct (x <? v) eqn:Hlt.
    + (* insert left *)
      specialize (IHl Hl) as [Hl_safe | Hl_root].
      * (* left safe *)
        left. apply balance_preserves_no_red_red_or_root; eauto.
      * (* left root violation *)
        right. apply balance_preserves_no_red_red_or_root; eauto.
    + (* insert right *)
      specialize (IHr Hr) as [Hr_safe | Hr_root].
      * left. apply balance_preserves_no_red_red_or_root; eauto.
      * right. apply balance_preserves_no_red_red_or_root; eauto.
Qed. *)

Lemma rb_insert_aux_preserves_no_red_red :
  forall x t,
    no_red_red t ->
    no_red_red (rb_insert_aux x t)
    \/
    red_red_at_root (rb_insert_aux x t).
Proof.
  intros x t Hn.
  (* revert x Hn. *)
  induction t as [| c l IHl v r IHr]; 
  (* intros x Hn;  *)
  simpl in *.
  
  (* Base case: inserting into leaf *)
  - (* t = leaf *)
    left. constructor; eauto. (* inserting into leaf produces a single red node; no red-red violation *)

  (* Inductive case: t = node c l v r *)
  - 
    inv Hn.
    destruct (v =? x) eqn:Heq.
    + (* v = x: no change *)
      left; constructor; assumption.
    + (* v ≠ x *)
      destruct (v <? x) eqn:Hlt.
      * (* v < x: insert into right subtree *)
        remember (rb_insert_aux x r) as r' eqn:Heqr'.
        pose proof (IHr H4) as Hr_res.
        rewrite  Heqr' in Hr_res.
        destruct Hr_res as [Hr_safe | Hr_root].
        -- (* Right insertion safe *)
          destruct IHr as [Hr1_safe | Hr1_root]; eauto; try(left; apply (balance_preserves_no_red_red (node Black l v r')); eauto; constructor; eauto).
          rewrite Heqr'; assumption.
        -- (* Right insertion causes red-red at root *)
           apply (balance_preserves_no_red_red_or_root Black l v r'); eauto.
      *
        remember (rb_insert_aux x l) as l' eqn:Hl'.
        pose proof (IHl H1) as Hl_res.
        rewrite Hl' in Hl_res.
        destruct Hl_res as [Hl_safe | Hl_root].
        -- destruct IHl as [Hl1_safe | Hl1_root];
           try(left; apply (balance_preserves_no_red_red (node Black l' v r)); constructor; eauto); eauto.
           rewrite Hl'. assumption.
        -- (* Left insertion produced red-red at root *)
           apply (balance_preserves_no_red_red_or_root Black l' v r); eauto.
  + destruct (v =? x) eqn:Heq.
    * (* v = x: no change *)
      left; constructor; assumption.
    * destruct (v <? x) eqn:Hlt.
      remember (rb_insert_aux x r) as r' eqn:Heqr'.
      specialize (IHr H6).
      destruct IHr as [Hr_safe | Hr_root].
        -- (* Right insertion safe: no red-red in r' *)
          pose proof (rb_insert_aux_never_leaf x r) as Hnever_leaf.
          destruct (rb_insert_aux x r) as [|cr lr vr rr] eqn:Hr_eq.
          ++ (* impossible: rb_insert_aux never returns leaf *)
              exfalso. apply Hnever_leaf. eauto.
          ++  destruct cr.
             ** left.
                constructor; try assumption.
                rewrite Heqr'. eauto.
             **  right. rewrite Heqr'. apply rr_right.
      -- right. rewrite Heqr'. inv Hr_root; rewrite <- H; apply rr_right.
      --  specialize (IHl H5).
          destruct IHl as [Hl_safe | Hl_root].
          ++  destruct (rb_insert_aux x l) as [|cl ll lv lr] eqn:Hl_eq. (*Needs to be first otherwise too weak*)  
            **(* impossible: rb_insert_aux never returns leaf *)
            exfalso. apply (rb_insert_aux_never_leaf x l). assumption.
            **  destruct cl.
                --- left. constructor; try assumption. eauto.
                --- right. apply rr_left. 
           ++ (* Left insertion created red-red at root *)
            right. inversion Hl_root as [a x' b y c' | a x' b y c']; subst; apply rr_left. 
Qed.


Lemma rb_insert_preserves_no_red_red :
  forall x t,
    no_red_red t ->
    no_red_red (rb_insert x t).
Proof.
  intros x t Hn.
  unfold rb_insert.
  (* Apply the updated lemma *)
  destruct (rb_insert_aux_preserves_no_red_red x t Hn) as [Hgood | Hrr].
  -
    destruct (rb_insert_aux x t) as [| c l v r] eqn:Haux.
    + (* impossible case *)
      exfalso. apply (rb_insert_aux_never_leaf x t). exact Haux.
    + (* recoloring root to Black preserves no_red_red *)
      constructor; 
      inversion Hgood; assumption.
      
  - 
    destruct (rb_insert_aux x t) as [| c l v r] eqn:Haux.
    + (* impossible case *)
      exfalso. apply (rb_insert_aux_never_leaf x t). exact Haux.
    + (* The root must be Red with Red child; making it Black fixes violation *)
      constructor; eauto; admit.
Admitted.
 
Lemma rb_insert_aux_preserves_bh_exists :
  forall x t,
    (exists k, black_height t = Some k) ->
    (exists k, black_height (rb_insert_aux x t) = Some k).
Proof.
  intros x t [k Hk].
Admitted.

Lemma rb_insert_aux_preserves_invariant :
  forall x t,
    rb_invariant t ->
    rb_sorted (rb_insert_aux x t) /\ 
    (no_red_red (rb_insert_aux x t) \/ red_red_at_root (rb_insert_aux x t)) /\
    exists k, black_height (rb_insert_aux x t) = Some k.
Proof.
  intros x t Hinv.
  destruct Hinv as [Hsorted [Hnored Hbh_ex]].
  split.
  - apply (rb_insert_aux_preserves_sorted x t). exact Hsorted.
  - split.
    + apply (rb_insert_aux_preserves_no_red_red x t). exact Hnored.
    + apply (rb_insert_aux_preserves_bh_exists x t). exact Hbh_ex.
Qed.

Lemma red_red_at_root_children_valid :
  forall t,
    red_red_at_root t ->
    match t with
    | node Red l v r => no_red_red l /\ no_red_red r
    | _ => True
    end.
Proof.
  intros t H.
Admitted.

Theorem rb_insert_correct : forall x t,
  rb_invariant t ->
  rb_invariant (rb_insert x t).
Proof.
  intros x t [Hsorted [Hnored [k Hbh]]].
  unfold rb_insert.
  
  pose proof (rb_insert_aux_preserves_invariant x t) as Haux.
  assert (Hinv_full : rb_invariant t).
  { split; eauto. }
  specialize (Haux Hinv_full).
  destruct Haux as [Hsorted_aux [Hnored_or_root Hbh_aux]].
  
  destruct (rb_insert_aux x t) as [| c l v r] eqn:E.
  - (* impossible *)
    exfalso. apply (rb_insert_aux_never_leaf x t). exact E.
  - (* rb_insert recolors root to Black *)
    split.
    + 
      apply (recolor_preserves_rb_sorted c l v r Hsorted_aux).
    + split.
      * 
        destruct Hnored_or_root as [Hgood | Hroot_viol].
        -- 
           apply (recolor_preserves_no_red_red c l v r Hgood).
        -- constructor. 
           pose proof (red_red_at_root_children_valid (node c l v r) Hroot_viol) as Hvalid_children.
           destruct c.
           ++ inversion Hroot_viol.
           ++ destruct Hvalid_children as [Hnl Hnr]; assumption.
           ++ destruct c.
            --- inversion Hroot_viol.
            --- pose proof (red_red_at_root_children_valid (node Red l v r) Hroot_viol) as Hvalid.
               simpl in Hvalid.
               destruct Hvalid as [_ Hr_valid]. (* Discard left, keep right *)
               assumption.

      * (* black_height: handle the recoloring effect *)
        destruct Hbh_aux as [k' Hbh'].
        destruct c; simpl.
        -- (* c = Black: no change in black height *)
           exists k'. exact Hbh'.
        -- (* c = Red: black height increases by 1 *)
            pose proof (black_height_recolor_root Red l v r k' Hbh') as Hrecolored.
           exists (k' + 1).
           simpl in *.
           exact Hrecolored.   
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