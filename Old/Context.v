(* Require Import Tactics. *)
Require Import Old.Types.
From Coq Require Import Unicode.Utf8_core.

From Coq Require Import List.
Import ListNotations.

Module Context (MT : MULTITYPE).
  Definition t := list MT.T.

  Inductive union : t -> t -> t -> Type :=
  | Union_Nil : union [] [] [] 
  | Union_Cons : 
    ∀  Γ₁ Γ₂ Γᵣ mt₁ mt₂ mtu, 
    union Γ₁ Γ₂ Γᵣ -> 
    MT.eq (MT.union  mt₁ mt₂) mtu ->
    union (mt₁ :: Γ₁) (mt₂ :: Γ₂) (mtu :: Γᵣ)
  .
  Hint Constructors union : core.

  Fixpoint eq (Γ₁ Γ₂ : t) : Prop :=
    match Γ₁, Γ₂ with 
    | [], [] => True
    | [], _::_ | _::_, [] => False
    | h₁::t₁, h₂::t₂ => (MT.eq h₁ h₂) /\ (eq t₁ t₂)
    end.
  Hint Unfold eq : core.


  Lemma eq_empty_l : ∀ Γ, eq [] Γ -> Γ = [].
  Proof with eauto.
    induction Γ; intros...
    inversion H.
  Qed.

  Lemma eq_empty_r : ∀ Γ, eq Γ [] -> Γ = [].
  Proof with eauto.
    induction Γ; intros...
    inversion H.
  Qed.

  Lemma eq_refl : ∀ Γ, eq Γ Γ.
  Proof with eauto.
    induction Γ; simpl...
    split...
    apply MT.eq_refl.
  Qed.
  

  Lemma eq_sym : 
    ∀ (Γ₁ Γ₂ : t),
    eq Γ₁ Γ₂ ->
    eq Γ₂ Γ₁.
  Proof with eauto.
    induction Γ₁ as [| mt₁ Γ₁]; intros [| mt₂ Γ₂ ] H_eq; simpl in *; repeat split_and...
    apply MT.eq_sym...
  Qed.


  Lemma eq_trans : 
    ∀ (Γ₁ Γ₂ Γ₃: t),
    eq Γ₁ Γ₂ ->
    eq Γ₂ Γ₃ ->
    eq Γ₁ Γ₃.
  Proof with eauto.
    induction Γ₁ as [| mt₁ Γ₁]; intros [| mt₂ Γ₂ ] [| mt₃ Γ₃ ] H_eq1 H_eq2; simpl in *; repeat split_and; try contradiction...
    eapply MT.eq_trans...
  Qed.

  Theorem union_comm : 
    ∀ (Γ₁ Γ₂ Γᵣ₁ Γᵣ₂: t),
    union Γ₁ Γ₂ Γᵣ₁ -> 
    union Γ₂ Γ₁ Γᵣ₂ -> 
    eq Γᵣ₁ Γᵣ₂.
  Proof with eauto.
    intros * H_union_1. generalize dependent Γᵣ₂.
    induction H_union_1; intros * H_union_2; inversion H_union_2; subst; simpl...
    split...
    eapply MT.eq_trans...
    apply MT.eq_sym.
    apply MT.eq_trans with (MT.union mt₁ mt₂)...
    apply MT.union_comm.
  Qed.

  Ltac inversion_eq_list := 
    match goal with 
    | [H : _ :: _ = _ :: _ |- _] => inversion H; clear H; subst
    end.

  Theorem union_assoc : 
    ∀ (Γ₁ Γ₂ Γ₃ Γ₁₂ Γ₁₂_₃ Γ₂₃ Γ₁_₂₃ : t),
    union Γ₁ Γ₂ Γ₁₂ -> 
    union Γ₁₂ Γ₃ Γ₁₂_₃ -> 
    union Γ₂ Γ₃ Γ₂₃ -> 
    union Γ₁ Γ₂₃ Γ₁_₂₃ -> 
    eq Γ₁₂_₃ Γ₁_₂₃.
  Proof with eauto using MT.eq_refl, MT.eq_sym, MT.eq_trans, MT.union_assoc, MT.eq_union.
  Hint Unfold eq : core.
  intros * H_union_1_2.
  generalize dependent Γ₃.
  generalize dependent Γ₁₂_₃. 
  generalize dependent Γ₂₃.
  generalize dependent Γ₁_₂₃.
  induction H_union_1_2; intros * H_union_12_3 H_union_2_3 H_union_1_23; inversion H_union_12_3; inversion H_union_2_3; inversion H_union_1_23; subst...
  simpl.
  repeat inversion_eq_list.
  (* inversion H8; inversion H14; subst. *)
  split...
  apply MT.eq_trans with (MT.union mt₁ mtu1)...
  apply MT.eq_trans with (MT.union mtu mt₂0)...
  apply MT.eq_trans with (MT.union mt₁ (MT.union mt₂ mt₂0))...
Qed.



  Lemma eq_union_left : 
    ∀ Γ₁ Γ₁' Γ₂ Γᵣ, 
    eq Γ₁ Γ₁'-> 
    union Γ₁ Γ₂ Γᵣ -> 
    union Γ₁' Γ₂ Γᵣ
    .
  Proof with eauto 6 using MT.eq_union, MT.eq_sym, MT.eq_refl, MT.eq_trans, Union_Cons with permutation_hints.
    induction Γ₁ as [ | mt₁ Γ₁ IHΓ]; intros [| mt₁' Γ₁'] [ | mt₂ Γ₂] [| mtᵣ Γᵣ] H_eq H_u; inversion H_u; try inversion H_eq; subst; simpl...
  Qed.

  Lemma eq_union_right : 
    ∀ Γ₁ Γ₂ Γ₂' Γᵣ, 
    eq Γ₂ Γ₂'-> 
    union Γ₁ Γ₂ Γᵣ -> 
    union Γ₁ Γ₂' Γᵣ
    .
  Proof with eauto 6 using MT.eq_union, MT.eq_sym, MT.eq_refl, MT.eq_trans, Union_Cons with permutation_hints.
    induction Γ₁ as [ | mt₁ Γ₁ IHΓ]; intros [| mt₂ Γ₂] [ | mt₂' Γ₂'] [| mtᵣ Γᵣ] H_eq H_u; inversion H_u; try inversion H_eq; subst; simpl...
  Qed.

  Lemma eq_union : 
    ∀ Γ₁ Γ₁' Γ₂ Γ₂' Γᵣ, 
    eq Γ₁ Γ₁'-> 
    eq Γ₂ Γ₂'-> 
    union Γ₁ Γ₂ Γᵣ -> 
    union Γ₁' Γ₂' Γᵣ.
  Proof.
    eauto using eq_trans, eq_union_left, eq_union_right with permutation_hints.
  Qed.    

End Context.

Module Ctx := Context Multitype.


Fixpoint is_tight_context(Γ : Ctx.t) : Prop :=
  match Γ with 
  | [] => True 
  | h::t => (is_tight_multitype h) /\ (is_tight_context t) 
  end.


Hint Unfold is_tight_type is_tight_multitype is_tight_context  : core.
Notation "a ⊎ b" := (Multitype.union a b) (at level 0).
Notation "a '⊎c' b ≡ c" := (Ctx.union a b c) (at level 0).



Fixpoint In (t : type) (mt : multitype) : Prop :=
  match mt with 
  | {{ nil }} => False
  | {{ h ; mt }} => (permutationₜ t h) \/ (In t mt)
  end.

Lemma mt_eq_in : 
  ∀ (t : type) (mt₁ mt₂ : multitype),
  Multitype.eq mt₁ mt₂ -> 
  In t mt₁ ->
  In t mt₂.
Proof with eauto with permutation_hints.
  intros * H_eq H_in.
  induction H_eq...
  - inversion H_in.
    + left...
    + right...
  - inversion H_in.
    + right. left...
    + inversion H.
      * left...
      * right; right...
Qed.


Ltac permutationₜ_induction perm P0 := 
  induction perm using permutationₜ_mut_ind with (P0:=P0); unfold P0 in *; clear P0.

Ltac permutationₘ_induction perm P := 
  induction perm using permutationₘ_mut_ind with (P:=P); unfold P in *; clear P.

Lemma eq_tight : 
  ∀ t₁ t₂, 
  permutationₜ t₁ t₂ ->
  is_tight_type t₁ -> 
  is_tight_type t₂.
Proof with eauto using mt_eq_in with permutation_hints.
  intros * H_perm.
  pose (P0 (mt₁ mt₂ : multitype) (H_permₘ : permutationₘ mt₁ mt₂) := is_tight_multitype mt₁ -> is_tight_multitype mt₂).
  permutationₜ_induction H_perm P0; try (intro H_tight; split; inversion H_tight as [H_tight_t H_tight_mt]; try inversion H_tight_mt; eauto using mt_eq_in with permutation_hints; fail)...
Qed.

Lemma eq_tight_multitype : 
  ∀ mt₁ mt₂, 
  permutationₘ mt₁ mt₂ ->
  is_tight_multitype mt₁ -> 
  is_tight_multitype mt₂.
Proof with eauto using mt_eq_in with permutation_hints.
  intros * H_perm.
  pose (P (t₁ t₂ : type) (H_permₜ : permutationₜ t₁ t₂) := is_tight_type t₁ -> is_tight_type t₂).
  permutationₘ_induction H_perm P; try (intro H_tight; split; inversion H_tight as [H_tight_t H_tight_mt]; try inversion H_tight_mt; repeat apply and_set_intro; eauto using mt_eq_in with permutation_hints; fail)...
Qed.


Lemma Ctx_eq_tight :
  ∀ (Γ₁ Γ₂ : Ctx.t), Ctx.eq Γ₁ Γ₂ -> is_tight_context Γ₁ -> is_tight_context Γ₂.
Proof with eauto using mt_eq_in, eq_tight, eq_tight_multitype with permutation_hints.
  induction Γ₁; intros; destruct Γ₂; simpl in *; destruct H, H0...
Qed.


Lemma mt_union_tight :
  ∀ (mt₁ mt₂ mt : multitype), 
    Multitype.eq (mt₁ ⊎ mt₂) mt -> 
    is_tight_multitype mt -> 
    is_tight_multitype mt₁ /\ is_tight_multitype mt₂.
Proof with eauto using mt_eq_in, eq_tight, eq_tight_multitype with permutation_hints.
  induction mt₁; intros; simpl.
  - split...
  - change {{` t `; ` mt₁ `}} with (Multitype.union {{t ; nil}} mt₁) in *.
    assert (Multitype.eq (mt₁ ⊎ {{ t ; mt₂}}) mt).
    { 
      change {{` t `; ` mt₂ `}} with (Multitype.union {{t ; nil}} mt₂) in *.
      apply Multitype.eq_trans with ((mt₁ ⊎ {{t ; nil}}) ⊎ mt₂)...
      - apply Multitype.eq_sym. apply Multitype.union_assoc.
      - apply Multitype.eq_trans with (({{` t `; nil}} ⊎ mt₁) ⊎ mt₂)...
        apply Multitype.eq_union_left.
        apply Multitype.union_comm.
    }
    apply IHmt₁ in H1; repeat (split_and; simpl in *)...
Qed.




Lemma Ctx_union_tight : 
  ∀ (Γ₁ Γ₂ Δ : Ctx.t), Γ₁ ⊎c Γ₂ ≡ Δ -> is_tight_context Δ -> is_tight_context Γ₁ /\ is_tight_context Γ₂.
Proof with eauto using mt_union_tight, mt_union_tight, mt_eq_in, eq_tight, eq_tight_multitype with permutation_hints.
  intros Γ₁ Γ₂ Δ.
  generalize dependent Γ₂.
  generalize dependent Γ₁.
  induction Δ as [ | mt Δ IH]; intros * H_union H_tight; inversion H_union as [| Γ₁' Γ₂' H1 mt₁ mt₂ H2 H_union' H_eq H3 H4 H5 ]; subst; simpl in *; repeat split_and; try edestruct IH;
  try destruct (mt_union_tight mt₁ mt₂ mt)...
Qed.