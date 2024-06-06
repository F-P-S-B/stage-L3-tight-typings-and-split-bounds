From Coq Require Import Unicode.Utf8.
From Coq Require Import List.
Import ListNotations.
Require Import Types.

Inductive and_set (A B : Set) : Set :=
| and_set_intro : A -> B -> and_set A B
.

Module Context (MT : MULTITYPE).
  Definition t := list MT.T.

  Inductive union : t -> t -> t -> Set :=
  | Union_Nil : union [] [] [] 
  | Union_Cons : 
    ∀  Γ₁ Γ₂ Γᵣ mt₁ mt₂, 
    union Γ₁ Γ₂ Γᵣ -> 
    union (mt₁ :: Γ₁) (mt₂ :: Γ₂) ((MT.union  mt₁ mt₂):: Γᵣ)
  .

  Fixpoint equals (Γ₁ Γ₂ : t) : Set :=
    match Γ₁, Γ₂ with 
    | [], [] => True
    | [], _::_ | _::_, [] => False
    | h₁::t₁, h₂::t₂ => and_set (MT.eq h₁ h₂) (equals t₁ t₂)
    end.

  Lemma eq_refl : ∀ Γ, equals Γ Γ.
  Proof with eauto.
    induction Γ; simpl...
    apply and_set_intro...
    apply MT.eq_refl.
  Qed.

  Lemma eq_sym : 
    ∀ (Γ₁ Γ₂ : t),
    eq Γ₁ Γ₂ ->
    eq Γ₂ Γ₁.
  Proof with eauto.
    induction Γ₁; intros...
  Qed.


  Lemma eq_trans : 
    ∀ (Γ₁ Γ₂ Γ₃: t),
    eq Γ₁ Γ₂ ->
    eq Γ₂ Γ₃ ->
    eq Γ₁ Γ₃.
  Proof with eauto.
    induction Γ₁; intros; subst...
  Qed.

  Theorem union_comm : 
    ∀ (Γ₁ Γ₂ Γᵣ₁ Γᵣ₂: t),
    union Γ₁ Γ₂ Γᵣ₁ -> 
    union Γ₂ Γ₁ Γᵣ₂ -> 
    equals Γᵣ₁ Γᵣ₂.
  Proof with eauto.
    intros * H_union_1. generalize dependent Γᵣ₂.
    induction H_union_1; intros * H_union_2; inversion H_union_2; subst; simpl...
    apply and_set_intro...
    apply MT.union_comm.
  Qed.

  Theorem union_assoc : 
    ∀ (Γ₁ Γ₂ Γ₃ Γ₁₂ Γ₁₂_₃ Γ₂₃ Γ₁_₂₃ : t),
    union Γ₁ Γ₂ Γ₁₂ -> 
    union Γ₁₂ Γ₃ Γ₁₂_₃ -> 
    union Γ₂ Γ₃ Γ₂₃ -> 
    union Γ₁ Γ₂₃ Γ₁_₂₃ -> 
    equals Γ₁₂_₃ Γ₁_₂₃.
  Proof with eauto.
  Hint Unfold equals : core.
  intros * H_union_1_2.
  generalize dependent Γ₃.
  generalize dependent Γ₁₂_₃. 
  generalize dependent Γ₂₃.
  generalize dependent Γ₁_₂₃.
  induction H_union_1_2; intros * H_union_12_3 H_union_2_3 H_union_1_23; inversion H_union_12_3; inversion H_union_2_3; inversion H_union_1_23; subst...
  simpl.
  inversion H5; inversion H10; subst.
  apply and_set_intro...
  apply MT.union_assoc.
Qed.

End Context.

Module Ctx := Context Multitype.


Fixpoint is_tight_context(Γ : Ctx.t) : Set :=
  match Γ with 
  | [] => True 
  | h::t => and_set (is_tight_multitype h) (is_tight_context t) 
  end.
