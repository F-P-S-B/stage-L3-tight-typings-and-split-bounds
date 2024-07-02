From TLC Require Import LibLN LibTactics LibFset.
From Coq Require Import Unicode.Utf8_core.
From Coq Require Import Lia.
From TTSB Require Import Tactics.
From TTSB Require Import Classes.
From TTSB.Types Require Types.
Import Types.TypesNotations.
Create HintDb context_hints.

Local Notation "'multitype'" := Types.multitype.
Local Notation "'eq_multitype'" := Types.eq_multitype.

Definition ctx : Type := vars * (var -> multitype).
Definition empty : ctx := (\{}, fun _ => {{nil}}).
Definition add (Γ : ctx) (v : var) (e : multitype) : ctx :=
  If e = {{nil}} 
  then Γ 
  else
    let (s, f) := Γ in 
    (s \u \{v}, fun x => If x = v then e ⊎ (f x) else f x).

Lemma add_nil :
  ∀ Γ x, add Γ x {{nil}} = Γ.
Proof.
  unfolds add; case_if; reflexivity.
Qed.

Definition get (Γ : ctx) (x : var) := 
  let (_, f) := Γ in f x.



Lemma get_empty :
  ∀ x, get empty x = {{nil}}.
Proof.
  reflexivity.
Qed.

Lemma get_add_eq : 
  ∀ Γ x A, get (add Γ x A) x = A ⊎ (get Γ x).
Proof.
  unfolds get, add; destruct Γ; intros;
  repeat case_if; substs*.
Qed.

Lemma get_add_neq :
  ∀ Γ x x' A, x ≠ x' -> get (add Γ x A) x' = get Γ x'.
Proof.
  unfolds get, add; destruct Γ; intros;
  repeat case_if; substs*.
Qed.



Definition union (Γ₁ Γ₂ : ctx) : ctx :=
  let (s₁, f₁) := Γ₁ in
  let (s₂, f₂) := Γ₂ in
  (s₁ \u s₂, fun x => (f₁ x) ⊎ (f₂ x)).

Notation "a '⊎c' b"  := (union a b) (at level 0).


Lemma get_union :
  ∀ Γ₁ Γ₂ x, 
  get (Γ₁ ⊎c Γ₂) x = (get Γ₁ x) ⊎ (get Γ₂ x).
Proof.
  intros.
  destruct Γ₁ as [s₁ f₁]. destruct Γ₂ as [s₂ f₂].
  simpls*.
Qed.
Definition equals (Γ₁ Γ₂ : ctx) : Prop :=
  let (s₁, f₁) := Γ₁ in
  let (s₂, f₂) := Γ₂ in
  s₁ = s₂ /\ 
  ∀ (x : var),  
  eq_multitype (f₁ x) (f₂ x).

Instance Equiv_equals_ctx : Equivalence equals.
Proof.
  use_equivalences.
  constructor;
  intros;
  repeat match goal with 
  | [ Γ : ctx |- _] => destruct Γ
  end; simpls; split_and_or_max; substs*.
Qed.


Ltac use_equivalences ::= 
  Types.use_equivalences_type;
  destruct Equiv_equals_ctx 
    as [eq_ctx_refl eq_ctx_sym eq_ctx_trans].


Lemma equals_empty_is_empty :
  ∀ Γ, equals Γ empty <-> Γ = empty.
Proof.
  destruct Γ; split; intros; inverts* H.
  - fequals*. applys fun_ext_dep.
    intro x.
    specialize H1 with x.
    applys* Types.eq_empty_is_empty.
  - use_equivalences. autos*.
Qed. 

Lemma equals_add :
  ∀ Γ₁ Γ₂ x M₁ M₂, 
  Types.eq_multitype M₁ M₂ ->
  equals Γ₁ Γ₂ -> 
  equals (add Γ₁ x M₁) (add Γ₂ x M₂).
Proof.
  intros [s1 f1] [s2 f2] * HeqM HeqΓ.
  unfold add; repeat case_if; substs*;
  try solve[use_equivalences; hint Types.eq_empty_is_empty; false*].
  simpls; reduce_max; substs*.
  hint Types.union_perm.
  intros.
  case_if*.
Qed.

Lemma add_comm :
  ∀ Γ₁ Γ₂ x₁ x₂ M₁ M₂, 
  equals Γ₁ Γ₂ -> 
  equals (add (add Γ₁ x₁ M₁) x₂ M₂) (add (add Γ₂ x₂ M₂) x₁ M₁).
Proof.
  intros [s₁ f₁] [s₂ f₂] * Heq.
  simpls.
  unfolds add, equals;
  repeat case_if; reduce_max; substs*;
  try solve [intro y; hint Types.union_perm; use_equivalences; case_if*]. 
  - rewrite union_comm, union_assoc, (union_comm \{ x₂} s₂). auto.
  - intro. repeat case_if; 
    try solve[ hint Types.union_perm; use_equivalences; autos* ].
    use_equivalences.
    hint Types.union_assoc, Types.union_perm, Types.union_comm; autos*.
Qed.  


Lemma union_empty_l :
  ∀ Γ, (empty ⊎c Γ) = Γ.
Proof.
  use_equivalences;
  intros [s f].
  simpls.
  simpl_unions.
  fequals.
Qed.

Lemma union_empty_r :
  ∀ Γ, (Γ ⊎c empty) = Γ.
Proof.
  
  use_equivalences;
  intros [s f].
  simpls.
  simpl_unions.
  fequals.
  apply fun_ext_dep; intro.
  rewrite* Types.union_empty_r.
Qed.

Lemma union_comm :
  ∀ Γ₁ Γ₂, equals (Γ₁ ⊎c Γ₂) (Γ₂ ⊎c Γ₁).
Proof.
  hint Types.union_comm.
  intros [s₁ f₁] [s₂ f₂]; simpls*; splits*;
  apply* LibFset.union_comm.
Qed.

Lemma union_assoc :
  ∀ Γ₁ Γ₂ Γ₃, equals ((Γ₁ ⊎c Γ₂) ⊎c Γ₃) (Γ₁ ⊎c (Γ₂ ⊎c Γ₃)).
Proof.
  hint Types.union_assoc.
  intros [s₁ f₁] [s₂ f₂] [s₃ f₃]; simpls*; splits*.
  rewrite* LibFset.union_assoc.
Qed.

Definition ok (Γ : ctx) : Prop := 
  let (s, f) := Γ in 
  ∀ x, x \in s <-> f x ≠ {{nil}}.


Lemma ok_empty :
  ok empty.
Proof.
  unfolds empty. simpls.
  intros; splits; intro H_contra; false.
  applys* in_empty_inv.
Qed.
Hint Resolve ok_empty : context_hints.


Lemma ok_add : 
  ∀ (Γ : ctx) (x : var) (M : multitype),
    ok Γ -> 
    ok (add Γ x M).
Proof.
  intros [s f] y M Hok.
  unfolds ok, add; repeat case_if; intro x; specialize Hok with x; split_and_or_max; intros; repeat case_if*; autos*.
  - applys* Types.nnil_union.
  - apply Hok0; reduce_max; autos*.
  - reduce_max; right; reduce_max; autos.
  - simpl_unions; autos*.
Qed. 


Lemma ok_union :
  ∀ (Γ₁ Γ₂ : ctx),
  ok Γ₁ -> ok Γ₂ ->
  ok Γ₁ ⊎c Γ₂.
Proof.
  hint Types.nnil_union.
  unfolds ok, union.
  intros [s₁ f₁] [s₂ f₂] Hok1 Hok2 x.
  specialize Hok1 with x;
  specialize Hok2 with x;
  split_and_or_max; intros; repeat simpl_unions.
  - applys* Types.nnil_union.
  - destruct (f₁ x); destruct (f₂ x); autos*;
    left; applys Hok4; absurd.
Qed.

Lemma ok_eq : 
  ∀ Γ₁ Γ₂, 
  equals Γ₁ Γ₂ ->
  ok Γ₁ ->
  ok Γ₂.
Proof.
  hint Types.eq_empty_is_empty.
  use_equivalences.
  intros [s₁ f₁] [s₂ f₂] [H_eq_dom H_eq_f] Hok; simpls*.
  intro x.
  specialize Hok with x as [H_in_nnil H_nnil_in].
  specialize H_eq_f with x; substs; split_and_or_max.
  - intros Hin H_contra.
    applys* H_in_nnil.
    rewrites* H_contra in H_eq_f.
  - intros H_f2x_nnil.
    apply H_nnil_in.
    destruct (f₁ x); destruct* (f₂ x).
    absurd.
Qed.

Lemma add_eq: 
  ∀ x M Γ₁ Γ₂,
  ok Γ₁ -> ok Γ₂ ->
  equals (add Γ₁ x M) (add Γ₂ x M) -> 
  equals Γ₁ Γ₂.
Proof.
  intros x M [s₁ f₁] [s₂ f₂] Hok1 Hok2 Heq; unfolds equals, add; case_if; simpls; split_and_or_max; autos.
  - lets Heq2 : Heq1 x; case_if.
    destruct (f₁ x) eqn:Heqf₁x;
    destruct (f₂ x) eqn:Heqf₂x;
    try rewrite Types.union_empty_r in Heq2;
    try solve[
      apply Types.eq_size in Heq2; rewrite Types.size_union in Heq2; 
      simpls; lia
    ].
    + admit.
    + admit.
  - lets Heq2 : Heq1 x; case_if.
    destruct (f₁ x) eqn:Heqf₁x;
    destruct (f₂ x) eqn:Heqf₂x;
    try rewrite Types.union_empty_r in Heq2; 
    try solve[
      apply Types.eq_size in Heq2; rewrite Types.size_union in Heq2; 
      simpls; lia
    ].
    + intro y.
      asserts H_EM : ({x = y} + {¬ x = y}).
      { apply classicT. }
      destruct H_EM.
      * substs; use_equivalences; rewrite Heqf₁x, Heqf₂x; autos*.
      * substs; specialize Heq1 with y; case_if*.
    + intro y.
      asserts H_EM : ({x = y} + {¬ x = y}).
      { apply classicT. }
      destruct H_EM.
      * substs; use_equivalences; rewrite Heqf₁x, Heqf₂x; autos*. admit.
      * substs; specialize Heq1 with y; case_if*.
Admitted.


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

Lemma dom_equal :
  ∀ Γ₁ Γ₂,
  equals Γ₁ Γ₂ ->
  dom Γ₁ = dom Γ₂.
Proof.
  intros [s₁ f₁] [s₂ f₂].
  simpls*.
Qed.

Hint Resolve 
  eq_refl eq_sym eq_trans 
  union_comm union_assoc
  ok_empty ok_add ok_union ok_eq 
  dom_add dom_union 
: context_hints.
Hint Rewrite union_empty_l union_empty_r : core.
Hint Unfold ok equals empty union dom : context_hints.


#[global] Instance Tightable_context : Tightable ctx := {| 
  tight := fun (Γ : ctx) =>
    let (_, f) := Γ in 
    ∀ x, tight (f x)
|}.

Lemma union_tight_ctx :
  ∀ Γ₁ Γ₂ Δ, 
  tight Δ ->
  equals (union Γ₁ Γ₂) Δ  ->
  tight Γ₁ /\ tight Γ₂.
Proof.
  intros.
  destruct Γ₁, Γ₂, Δ.
  simpls; split_and_or_max;
  intro x; specialize H with x; specialize H2 with x;
  apply Types.mt_union_tight in H2 as [Htm Htm0]; autos*.
Qed.

Ltac tight_union_ctx Δ :=
  match goal with 
  | [H : equals (union ?Γ₁ ?Γ₂) Δ |- _] => 
    let H_tight_Γ₁ := fresh "H_tight_Γ₁" in 
    let H_tight_Γ₂ := fresh "H_tight_Γ₂" in 
      apply union_tight_ctx in H as  [H_tight_Γ₁ H_tight_Γ₂]; eauto 
  end.

Lemma ok_get_equals :
  ∀ Γ₁ Γ₂, 
  ok Γ₁ -> ok Γ₂ -> 
  equals Γ₁ Γ₂ <-> ∀ x, eq_multitype (get Γ₁ x) (get Γ₂ x).
Proof.
  split.
  {
    intros Heq x.
    destruct Γ₁, Γ₂; simpls*.
  }
  {
    asserts Heqnnil : (
      ∀ mt1 mt2,
        mt1 ≠ {{nil}} ->
        eq_multitype mt1 mt2 ->
        mt2 ≠ {{nil}}
    ).
    {
      intros; destruct* mt1.
      intro; substs. apply Types.eq_empty_is_empty in H2; autos*.
    }
    intros.
    destruct Γ₁, Γ₂; split; simpls*.
    apply fset_extens;
    intros x Hin;
    repeat match goal with 
    | [H : ∀ _, _ |- _] => specialize H with x
    end; split_and_or_max;
    match goal with 
    | [H : ?x \in ?v , H' : ?x \in ?v -> _ |- _] => apply H' in H
    end;
    match goal with 
    | [H : ?mx ≠ {{nil}}, H' : eq_multitype ?mx ?mx2 |- _] => 
        apply Heqnnil with (mt2 := mx2) in H
    | [H : ?mx ≠ {{nil}}, H' : eq_multitype ?mx2 ?mx |- _] => 
        use_equivalences; apply Heqnnil with (mt2 := mx2) in H
    end; autos*.
  }
Qed.

