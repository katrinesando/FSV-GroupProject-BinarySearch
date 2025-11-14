Require Import BstProject.BST.
Require Import BstProject.project_lib.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.

(* bst to list *)
Fixpoint bst_to_list (bst: tree) : list nat :=
  match bst with
  | leaf => []
  | node l v r => bst_to_list l ++ [v] ++ bst_to_list r
end.

Fixpoint list_to_bst (lst: list nat) : tree :=
  match lst with
  | [] => leaf
  | head :: tail => insert head (list_to_bst tail)
end.

Example bst_lst : bst_to_list tree1 = [2;5;7;10;12;16;17].
Proof. unfold bst_to_list. reflexivity. Qed.

(* node (node (node leaf 2 leaf) 5 (node leaf 7 leaf))
10 (* root *)
(node (node leaf 12 leaf) 16 (node leaf 17 leaf)). *)

Example lst_bst : list_to_bst [12; 17; 16; 2; 7; 5; 10]=  tree1.
Proof. unfold list_to_bst. reflexivity. Qed.

(*Useful Theorems *)
(* Theorem bst_list_sorted : list -> bst -> list - skulle give sorted list ud
forall t1 t2, 
bst_to_list t1 = bst_to_list t2
*)

(* Size of list equals size of tree *)



(* Exercise 3.10*)
Fixpoint delete (x : nat) (t : tree) : tree 
  (* TODO: delete code *)
. Admitted.

(* TODO: Lemma delete_sorted  *)

(* TODO: Lemma delete_correct  *)