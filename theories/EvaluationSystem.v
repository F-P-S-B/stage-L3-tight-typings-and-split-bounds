From Coq Require Import Unicode.Utf8.

Require Import LogicSet.


Definition deterministic {A} (relation : A -> A -> Set) : Set :=
  ∀ (a a₁ a₂ : A), relation a a₁ -> relation a a₂ -> a₁ = a₂. 

Definition rel_normal {A} (relation : A -> A -> Set) (a : A) : Set := 
  (ex_set A (fun (a' : A) => relation a a')) -> False.

(* 
  Definition 2.1 (Evaluation system)
 *)


Section EvalSystem.
Variable T : Set.
Variable relation : T -> T -> Set.
Variable (normal neutral abs : T -> Set).

Definition evaluation_system : Set :=
            (deterministic relation)
        ∧a  (∀ (t : T),
                     (rel_normal relation t -> normal t)
                  ∧a (normal t -> rel_normal relation t))
        ∧a (∀ (t : T), 
                    (neutral t -> ((normal t) ∧a (abs t -> False)))
                  ∧a (((normal t) ∧a (abs t -> False)) -> neutral t))
.

End EvalSystem.

Check evaluation_system.

Inductive reflexive_closure {A} (rel : A -> A -> Set) : A -> A -> Type :=
  | RC_refl : ∀ (a : A), reflexive_closure rel a a
  | RC_self : ∀ (a₁ a₂ : A),
    rel a₁ a₂ -> 
    reflexive_closure rel a₁ a₂
.

Inductive transitive_closure {A} (rel : A -> A -> Set) : A -> A -> Type := 
  | TC_self :  
      ∀ (a₁ a₂ : A),
      rel a₁ a₂ -> 
      transitive_closure rel a₁ a₂
  | TC_trans :
      ∀ (a₁ a₂ a₃ : A), 
      transitive_closure rel a₁ a₂ ->
      transitive_closure rel a₂ a₃ ->
      transitive_closure rel a₁ a₃
.

Inductive n_iteration {A} (rel : A -> A -> Set) : nat -> A -> A -> Type := 
  | NI_O : ∀ (a : A), n_iteration rel O a a 
  | NI_Sn : 
      ∀ (n : nat) (a₁ a₂ a₃ : A), 
      rel a₁ a₂ -> 
      n_iteration rel n a₂ a₃ ->
      n_iteration rel (S n) a₁ a₃
.