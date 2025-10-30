Require Import BstProject.BST.
Require Import BstProject.project_lib.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.

(* Exercise 3.8  *)
Lemma insert_sorted :
  forall t x, sorted t -> sorted (insert x t).
Proof.
  (*TODO: prove insert_sorted*)
 Admitted.
(* Exercise 3.9 *)
Lemma insert_correct :
  forall t x y,
    sorted t ->
    elem_of y (insert x t)
    = orb (elem_of y t) (Nat.eqb x y).
Proof.
  (*TODO: prove insert_correct*)
  Admitted.