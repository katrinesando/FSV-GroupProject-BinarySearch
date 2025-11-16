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

Definition list_to_bst (lst: list nat) : tree :=
  fold_left(fun acc elem => insert elem acc) lst leaf.

Example bst_lst : bst_to_list tree1 = [2;5;7;10;12;16;17].
Proof. unfold bst_to_list. reflexivity. Qed.

(* node (node (node leaf 2 leaf) 5 (node leaf 7 leaf))
10 (* root *)
(node (node leaf 12 leaf) 16 (node leaf 17 leaf)). *)
(* [12; 17; 16; 2; 7; 5; 10] *)

Example lst_bst : list_to_bst [10;5;7;2;16;17;12] =  tree1.
Proof. unfold list_to_bst. simpl. Admitted.
  (* reflexivity.  *)

(*Useful Theorems *)
(* Theorem bst_list_sorted : list -> bst -> list - skulle give sorted list ud
forall t1 t2, 
bst_to_list t1 = bst_to_list t2
*)

(* Size of list equals size of tree *)

(* Exercise 3.10*)
(* Find smallest value in right subtree -> expects to get right subtree *)
Fixpoint successor (t:tree) : tree :=
  match t with
  | node l v r => 
    match l with
    | leaf => t
    | _ => successor l
    end
  | leaf => t
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
        let succ := successor r in
        match succ with
        | node l' v' r' => node l v' (delete v' r)
        | leaf => leaf (*Impossible -> TODO: make option (None)*)
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

(* TODO: Lemma delete_sorted  *)
Lemma delete_sorted :
  forall t x, sorted t -> sorted (delete x t).
Proof.
   induction t; simpl; intros.
  - constructor; easy.
  - inversion H; subst.
Qed.
  
Lemma delete_correct :
forall t x,
    sorted t ->
    elem_of x t = true -> 
    (elem_of x (delete x t)) = false.
Proof.
  induction t; simpl; intros.
  - admit.
  - inversion H. 
Qed.
  

