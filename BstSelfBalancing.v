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


(* Definition balance (t: rb_tree) : rb_tree :=
match t with
| node c l v r =>
  match c, v, l, r with
  | Red, v, (node Red ll lv lr), r =>
      node Red (node Black ll lv lr) v (node Black lr v r)
  | Red, v, (node Red ll lv (node Red lrl lrv lrr)), r =>
      node Red (node Black ll lv lrl) lrv (node Black lrr v r)
  | Red, v, l, (node Red (node Red rll rlv rlr) rv rr) =>
      node Red (node Black l v rll) rlv (node Black rlr rv rr)
  | Red, v, l, (node Red rl rv rr) =>
      node Red (node Black l v rl) rv (node Black rl rv rr)
  | _, _, _, _ => t
  end
| _ => t
end. *)

Fixpoint rb_insert (x:nat) (t:rb_tree) : rb_tree :=
match t with
| leaf  => node Red leaf x leaf
| node c l v r => 
  if v =? x then
  t
  else if v <? x then
  node l v (insert x r)
  else
  node (insert x l) v r
end.
