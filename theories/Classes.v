From TLC Require Import LibRelation.
From Coq Require Import Unicode.Utf8_core.

Class Tightable (A : Type) : Type := 
  { tight : A -> Prop }.

Class Sized (A : Type) : Type := 
  { size : A -> nat }.




