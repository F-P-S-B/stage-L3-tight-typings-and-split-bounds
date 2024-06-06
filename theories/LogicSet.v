Require Import Unicode.Utf8_core.

(* Inductive and_set (A B : Set) : Set :=
| and_set_intro : A -> B -> and_set A B
. *)

Inductive ex_set (A : Type) (P : A -> Set) : Type :=
  ex_set_intro : ∀ x : A, P x -> ex_set A  P.


(* Notation "A ∧a B" := (and_set A B) (at level 80, right associativity).
Ltac split_and_set := 
  match goal with 
  | [ |- _ ∧a _] => apply and_set_intro
  | [ H: _ ∧a _ |- _ ] => destruct H 
  end. *)
