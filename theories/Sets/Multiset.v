From Coq Require Import Unicode.Utf8.
From Coq Require Import Classes.Equivalence.
From Coq Require Import List.
From Coq Require Import Lia.
Import ListNotations.


Section Multiset.
  Variable A : Set.
  Variable eqₐ : A -> A -> Prop.
  Infix "=ₐ" := eqₐ (at level 10).
  Hypothesis eqₐ_equiv : Equivalence eqₐ.
  Hypothesis eqₐ_dec : 
    ∀ x y : A, {x =ₐ y} + {¬ (x =ₐ y)}.

  Definition multiset (A : Type) : Type := list A.
  Definition empty : multiset A := [].

  Fixpoint multiplicity (s : multiset  A) (a : A) : nat :=
      match s with 
      | [] => 0 
      | h::t => 
        match eqₐ_dec h a with 
        | left eq => 1 + multiplicity t a 
        | right neq => multiplicity t a
        end
      end.
    
  Definition meq (s₁ s₂ : multiset A) := 
    ∀ (a: A), multiplicity s₁ a = multiplicity s₂ a.
  Infix "=ₘ" := meq (at level 85).

  Lemma meq_refl : ∀ s : multiset A, s =ₘ s.
  Proof with eauto.
    intros s e...
  Qed.

  Theorem meq_equiv : Equivalence meq.
  Proof with eauto.
    Print Equivalence.
    refine (Build_Equivalence meq _ _ _).
    - intro. apply meq_refl.
    - intros s₁ s₂ H_meq e...
    - intros s₁ s₂ s₃ H_meq_1_2 H_meq_2_3 a.
      unfold meq in *.
      specialize H_meq_1_2 with a.
      specialize H_meq_2_3 with a.
      rewrite H_meq_1_2...
  Qed.

  Lemma meq_cons : 
    ∀ (s₁ s₂ : multiset A) (a₁ a₂ : A),
    a₁ =ₐ a₂ -> 
    s₁ =ₘ s₂ ->  
    (a₁ :: s₁) =ₘ (a₂ :: s₂).
  Proof with eauto.
    intros.
    intro a.
    simpl.
    destruct eqₐ_equiv.
    destruct (eqₐ_dec a₁ a); 
    destruct (eqₐ_dec a₂ a);
    match goal with 
    | [ |- S _ = S _] => idtac
    | [ |- _ = S _] => exfalso; eauto
    | [ |- S _ = _] => exfalso; eauto
    | _ => idtac
    end...
  Qed.

  
  Definition union (s₁ s₂ : multiset A) := s₁ ++ s₂.
  Infix "⊎" := union (at level 80).

  (* Set Printing Parentheses. *)
  Check (fun a b c => (a ⊎ b ⊎ c) =ₘ b).

  Fixpoint remove (s : multiset A) (e : A) := 
    match s with 
    | [] => s 
    | h::t => 
      match  eqₐ_dec h e with 
      | left eq => t
      | right neq => h::(remove t e)
      end
    end.

  Fixpoint minus (s₁ s₂ : multiset A) := 
    match s₂ with 
    | [] => s₁ 
    | h::t => minus (remove s₁ h) t
    end.
  
  Lemma union_mult : 
    ∀ (s₁ s₂ : multiset A) (a : A), 
    multiplicity (s₁ ⊎ s₂) a = multiplicity s₁ a + multiplicity s₂ a.
  Proof with eauto.
    intros.
    induction s₁...
    simpl.
    destruct (eqₐ_dec a0 a)... 
    rewrite IHs₁...
  Qed.
  Hint Rewrite union_mult : core.
  
  Lemma munion_empty_left : 
    ∀ s : multiset A, s =ₘ (empty ⊎ s).
  Proof.
    intros. apply meq_refl.
  Qed.

  Lemma munion_empty_right : 
    ∀ s : multiset A, s =ₘ (s ⊎ empty).
  Proof with eauto.
    intro. intro.
    rewrite union_mult...
  Qed.
        

  Lemma munion_comm : 
    ∀ (s₁ s₂ : multiset A), 
      (s₁ ⊎ s₂) =ₘ (s₂ ⊎ s₁).
  Proof with eauto with arith.
    intros. intro.
    repeat rewrite union_mult...
  Qed.
    

  Lemma munion_ass :
    ∀ (s₁ s₂ s₃ : multiset A), 
       ((s₁ ⊎ s₂) ⊎ s₃) =ₘ (s₁ ⊎ (s₂ ⊎ s₃)).
  Proof with eauto with arith.
    intros * a.
    repeat rewrite union_mult...
  Qed.

  Lemma meq_union :
    ∀ s₁ s₂ s₃ s₄ : multiset A, 
    s₁ =ₘ s₂ -> 
    s₃ =ₘ s₄ -> 
    (s₁ ⊎ s₃) =ₘ (s₂ ⊎ s₄).
  Proof with eauto with arith.
    intros * H_eq12 H_eq34 a.
    repeat rewrite union_mult...
  Qed.
End Multiset.
Check meq.

