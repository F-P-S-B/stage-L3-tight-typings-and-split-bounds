From TLC Require Import LibRelation.
From Coq Require Import Unicode.Utf8_core.

Class Equivalence {A : Type} (relation : A -> A -> Type) : Type :=
  { 
    reflexive : 
      ∀ a, 
      relation a a

  ; symmetric : 
      ∀ a₁ a₂, 
      relation a₁ a₂ -> 
      relation a₂ a₁ 

  ; transitive : 
      ∀ a₁ a₂ a₃, 
      relation a₁ a₂ -> 
      relation a₂ a₃ -> 
      relation a₁ a₃ 
  }.

Class Tightable (A : Type) : Type := 
  { tight : A -> Prop }.

Class Sized (A : Type) : Type := 
  { size : A -> nat }.




