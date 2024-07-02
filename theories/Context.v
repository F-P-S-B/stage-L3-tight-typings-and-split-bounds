
From TLC Require Import LibLN LibTactics LibFset.
From Coq Require Import Unicode.Utf8_core.
From TTSB Require Import Types.

Definition ctx : Type := vars * (var -> multitype).
Definition empty : ctx := (\{}, fun _ => {{nil}}).
Definition add (Γ : ctx) (v : var) (e : multitype) : ctx :=
  If e = MT_Empty 
  then Γ 
  else
    let (s, f) := Γ in 
    (s \u \{v}, fun x => If x = v then e ⊎ (f x) else f x).


Definition union_ctx (Γ₁ Γ₂ : ctx) : ctx :=
  let (s₁, f₁) := Γ₁ in
  let (s₂, f₂) := Γ₂ in
  (s₁ \u s₂, fun x => (f₁ x) ⊎ (f₂ x)).



Notation "a '⊎c' b"  := (union_ctx a b) (at level 0).
Definition eq_ctx (Γ₁ Γ₂ : ctx) : Prop :=
  let (s₁, f₁) := Γ₁ in
  let (s₂, f₂) := Γ₂ in
  s₁ = s₂ /\ 
  ∀ (x : var),  
  Multitype.eq (f₁ x) (f₂ x).


Lemma eq_refl : 
  ∀ Γ, eq_ctx Γ Γ.
Proof.
  Hint Resolve Multitype.eq_refl : core.
  destruct Γ; simpls*.
Qed.

Lemma eq_sym : 
  ∀ Γ₁ Γ₂, eq_ctx Γ₁ Γ₂ -> eq_ctx Γ₂ Γ₁.
Proof.
  Hint Resolve Multitype.eq_sym : core.
  introv H_eq;
  destruct Γ₁ eqn:Heq₁; destruct Γ₂ eqn:Heq₂; splits*;
  inverts* H_eq. 
Qed.

Lemma eq_trans : 
  ∀ Γ₁ Γ₂ Γ₃, eq_ctx Γ₁ Γ₂ -> eq_ctx Γ₂ Γ₃ -> eq_ctx Γ₁ Γ₃.
Proof.
  Hint Resolve Multitype.eq_trans : core.
  intros [s₁ f₁] [s₂ f₂] [s₃ f₃] H_eq1 H_eq2; splits;
  inverts H_eq1; inverts* H_eq2. 
Qed.

Lemma union_empty_l :
  ∀ Γ, eq_ctx (empty ⊎c Γ) Γ.
Proof.
  intros [s f].
  simpls.
  splits*;
  rewrite* LibFset.union_empty_l.
Qed.

Lemma union_empty_r :
  ∀ Γ, eq_ctx (Γ ⊎c empty) Γ.
Proof.
  Hint Resolve Multitype.union_empty_r : core.
  intros [s f].
  simpls;
  splits;
  try rewrite* LibFset.union_empty_r.
  intro x. rewrite* Multitype.union_empty_r.
Qed.



Lemma union_comm :
  ∀ Γ₁ Γ₂, eq_ctx (Γ₁ ⊎c Γ₂) (Γ₂ ⊎c Γ₁).
Proof.
  Hint Resolve Multitype.union_comm : core.
  intros [s₁ f₁] [s₂ f₂]; simpls*; splits*;
  apply* union_comm.
Qed.

Lemma union_assoc :
  ∀ Γ₁ Γ₂ Γ₃, eq_ctx ((Γ₁ ⊎c Γ₂) ⊎c Γ₃) (Γ₁ ⊎c (Γ₂ ⊎c Γ₃)).
Proof.
  Hint Resolve Multitype.union_assoc : core.
  intros [s₁ f₁] [s₂ f₂] [s₃ f₃]; simpls*; splits*.
  rewrite* union_assoc.
Qed.


Definition ok (Γ : ctx) : Prop := 
  let (s, f) := Γ in 
  ∀ x, x \in s <-> f x ≠ {{nil}}.


Lemma ok_empty :
  ok empty.
Proof.
  unfold empty. simpls.
  intros; split; intro H_contra; exfalso.
  applys* in_empty_inv. contradiction.
Qed.
Hint Resolve ok_empty : core.


Lemma ok_add : 
  ∀ (Γ : ctx) (x : var) (M : multitype),
    ok Γ -> 
    ok (add Γ x M).
Proof.
  introv Hok.
  destruct Γ; simpls.
  unfold add.
  case_if*.
  simpls.
  split.
  - intro H_in.
    case_if; substs*.
    + destruct (m x).
      * rewrites* Multitype.union_empty_r.
      * inductions M; autos*.
        intro H_contra. inversion H_contra.
    + specialize Hok with x0 as [H_in_nnil _].
      rewrite in_union in H_in; destruct H_in; autos*.
      rewrite in_singleton in H. autos*.
  - case_if*; intro. substs*.
    + rewrite in_union. right. rewrite* in_singleton.
    + specialize Hok with x0 as [_ H_nnil_in].   
      rewrite in_union. left*.
Qed.

Lemma nnil_union : 
  ∀ mt1 mt2, 
  mt1 ≠ {{ nil }} \/ mt2 ≠ {{ nil }} <->
  mt1 ⊎ mt2 ≠ {{nil}}.
Proof.
  split.
  - introv [Hmt1_nnil | Hmt2_nnil]; inductions mt1; autos*;
    intro H_contra; inversion H_contra.
  - intros H_nnil.
    destruct mt1; simpls*.
    left; intro H_contra; inversion H_contra.
Qed.
Lemma ok_union :
  ∀ (Γ₁ Γ₂ : ctx),
  ok Γ₁ -> ok Γ₂ ->
  ok Γ₁ ⊎c Γ₂.
Proof.
  intros [s₁ f₁] [s₂ f₂] Hok1 Hok2.
  intro x.
  unfold ok in *.
  specialize Hok1 with x as [H_in_nnil₁ H_nnil_in₁].
  specialize Hok2 with x as [H_in_nnil₂ H_nnil_in₂].
  split.
  - intro H_in.
    rewrite in_union in H_in.
    destruct H_in as [H_in | H_in];
    applys* nnil_union.
  - intro. apply nnil_union in H as [H_f₁_x | H_f₂_x];
    rewrite* in_union.
Qed.

Lemma ok_eq : 
  ∀ Γ₁ Γ₂, 
  eq_ctx Γ₁ Γ₂ ->
  ok Γ₁ ->
  ok Γ₂.
Proof.
  intros [s₁ f₁] [s₂ f₂] [H_eq_dom H_eq_f] Hok; simpls*.
  intro x.
  specialize Hok with x as [H_in_nnil H_nnil_in].
  specialize H_eq_f with x; substs; split.
  - intros H_in H_contra.
    rewrite H_contra in *.
    apply Multitype.eq_empty_is_empty in H_eq_f. autos*.
  - intro H_nnil.
    apply H_nnil_in.   
    intro H_contra. rewrite H_contra in *.
    apply Multitype.eq_sym in H_eq_f.
    apply Multitype.eq_empty_is_empty in H_eq_f. autos*.
Qed.

Definition dom (Γ₁ : ctx) : vars := fst Γ₁.

Lemma dom_add : 
  ∀ Γ x mt,
  mt ≠ {{nil}} ->
  dom (add Γ x mt) = \{x} \u (dom Γ).
Proof.
  intros.
  destruct Γ eqn:HeqΓ.
  destruct (add (v, m) x mt) eqn:HeqAdd.
  simpl.
  unfold add in *.
  case_if*.
  inverts HeqAdd.
  rewrite* LibFset.union_comm.
Qed.

Lemma dom_union :
  ∀ Γ₁ Γ₂,
  dom (Γ₁ ⊎c Γ₂) = (dom Γ₁) \u (dom Γ₂).
Proof.
  intros [s₁ f₁] [s₂ f₂].
  simpls*.
Qed.
  


Hint Resolve 
  eq_refl eq_sym eq_trans 
  union_empty_l union_empty_r
  union_comm union_assoc
  ok_empty ok_add nnil_union ok_union ok_eq 
  dom_add dom_union 
: core.
Hint Unfold ok eq_ctx empty union_ctx dom : core.
