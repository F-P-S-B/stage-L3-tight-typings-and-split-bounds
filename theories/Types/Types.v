From Coq Require Import Unicode.Utf8_core.
From Coq Require Import Lia.
From Coq Require Import RelationClasses.
From TLC Require Import LibLN LibTactics LibFset LibList LibRelation.
From TTSB Require Import Tactics.
From TTSB Require Import Classes.
Create HintDb type_hints.


Ltac auto_tilde :=
  try (solve[ auto with type_hints
            | intuition auto with type_hints ]).

Ltac auto_star ::= 
  try (solve [ reflexivity
             | symmetry; eauto with type_hints 
             | etransitivity; eauto with type_hints 
             | eauto with type_hints 
             | jauto 
             | intuition eauto with type_hints]).


Parameter AtomicType : Set.
Parameter X : fset AtomicType.
Parameter eqₐ : AtomicType -> AtomicType -> Prop.
Parameter eqₐ_dec : 
  ∀ (t₁ t₂ : AtomicType),
  {eqₐ t₁ t₂} + {¬ eqₐ t₁ t₂}.
Parameter eqₐ_equiv : 
  equiv eqₐ.
Infix "≡ₐ" := eqₐ (at level 0).

Hint Constructors equiv : type_hints.
Hint Resolve eqₐ_equiv eqₐ_dec : type_hints.


Inductive tight_constant := 
| TC_Neutral : tight_constant
| TC_Abs : tight_constant
.
Inductive type :=
| Ty_Tight (t : tight_constant) : type
| Ty_Atomic (t : AtomicType) : (t \in X) -> type
| Ty_Fun : multitype -> type -> type 
with multitype :=
| MT_Empty : multitype
| MT_Cons (t : type) (mt : multitype) : multitype
.
Scheme type_mut_ind := Induction for type Sort Type
with multitype_mut_ind := Induction for multitype Sort Type.

Hint Constructors tight_constant type multitype : type_hints.

Fixpoint union (mt₁ mt₂ : multitype) : multitype :=
  match mt₁ with 
  | MT_Empty => mt₂
  | MT_Cons t mt₁' => MT_Cons t (union mt₁' mt₂) 
  end.

Hint Unfold union : type_hints.

#[global] Instance Tight_type : Tightable type := {
  tight := 
    fun t => 
    match t with
    | Ty_Tight _ => True 
    | Ty_Atomic _ _ => False
    | Ty_Fun _ _ => False
    end
}.

Fixpoint tight_aux (mt : multitype) : Prop := 
  match mt with 
  | MT_Empty => True
  | MT_Cons t mt' => (tight t) /\ (tight_aux mt')
  end.
#[global] Instance Tight_multitype : Tightable multitype := {
  tight := tight_aux
}.


Inductive eq_type : type -> type -> Prop :=
| Eq_Tight : 
    ∀ (t : tight_constant), 
    eq_type (Ty_Tight t) (Ty_Tight t)
| Eq_Atomic :
    ∀ (t₁ t₂ : AtomicType) 
      (prf₁ : t₁ \in X) (prf₂ : t₂ \in X),
    eqₐ t₁ t₂ -> 
    eq_type (Ty_Atomic t₁ prf₁) (Ty_Atomic t₂ prf₂)
| Eq_Fun : 
    ∀ (mt₁ mt₂ : multitype) (t₁ t₂ : type),
    eq_multitype mt₁ mt₂ -> 
    eq_type t₁ t₂ -> 
    eq_type (Ty_Fun mt₁ t₁) (Ty_Fun mt₂ t₂)
with eq_multitype : multitype -> multitype -> Prop :=
| Eq_MT_Empty : eq_multitype (MT_Empty) (MT_Empty)
| Eq_MT_Cons : 
    ∀ (mt₁ mt₂ : multitype) (t₁ t₂ : type),
    eq_type t₁ t₂ -> 
    eq_multitype mt₁ mt₂ -> 
    eq_multitype (MT_Cons t₁ mt₁) (MT_Cons t₂ mt₂)
| Eq_MT_Swap : 
    ∀ (t₁ t₂ : type) (mt : multitype),
      eq_multitype 
        (MT_Cons t₁ (MT_Cons t₂ mt))
        (MT_Cons t₂ (MT_Cons t₁ mt))
| Eq_MT_Trans :
    ∀ (mt₁ mt₂ mt₃ : multitype),
    eq_multitype mt₁ mt₂ ->
    eq_multitype mt₂ mt₃ ->
    eq_multitype mt₁ mt₃
.
Check eq_multitype_ind.
Hint Constructors eq_type eq_multitype : type_hints.
Scheme eq_type_mut_ind := Induction for eq_type Sort Prop
with eq_multitype_mut_ind := Induction for eq_multitype Sort Prop.

Ltac eq_type_induction eq P0 := 
  induction eq using eq_type_mut_ind with (P0:=P0); unfold P0 in *; clear P0.

Ltac eq_multitype_induction eq P := 
  induction eq using eq_multitype_mut_ind with (P:=P); unfold P in *; clear P.

Module TypesNotations.
Notation "a ⊎ b" := (union a b) (at level 0).

Declare Custom Entry multitype. 

Notation "{{ mt }}" := mt (mt custom multitype at level 99).
Notation "( mt )" := mt (in custom multitype, mt at level 99).
Notation "'nil'" := MT_Empty (in custom multitype at level 0).
Notation "t" := t (in custom multitype at level 0, t constr at level 0).
Notation "` t `" := t (in custom multitype at level 0, t constr at level 0).
Notation " t ; mt" := (MT_Cons t mt) (in custom multitype at level 90, mt custom multitype at level 99, left associativity).

Notation "mt |-> t" := (Ty_Fun mt t) (at level 99, right associativity).
Notation "{{ mt }} |-> t" := (Ty_Fun mt t) (in custom multitype at level 80, right associativity).

End TypesNotations.

Import TypesNotations.

Check eq_type_mut_ind.
#[global] Instance Refl_eq_type : Reflexive eq_type.
Proof.
  intro t; destruct eqₐ_equiv;
  pose (P0 mt := eq_multitype mt mt).
  induction t
    using type_mut_ind 
    with (P0 := P0); unfolds P0; clear P0; autos*.
Qed.

#[global] Instance Symm_eq_type : Symmetric eq_type.
Proof.
  intros t₁ t₂ Heq; destruct eqₐ_equiv.
    pose (
      P0 (mt₁ mt₂ : multitype ) (Heq : eq_multitype mt₁ mt₂) := 
      eq_multitype mt₂ mt₁ 
    );
    eq_type_induction Heq P0; autos*.
Qed.

#[global] Instance Trans_eq_type : Transitive eq_type.
Proof.
  intros t₁ t₂ t₃ Heq; destruct eqₐ_equiv;
  pose (
  P0 (mt₁ mt₂ : multitype) (Heq : eq_multitype mt₁ mt₂) :=
    ∀ (mt₃ : multitype), eq_multitype mt₂ mt₃ -> eq_multitype mt₁ mt₃
  ).
  gen t₃.
  eq_type_induction Heq P0; 
  intros t₃ Heq2; inverts* Heq2.
Qed.

(* #[global] Instance Equiv_eq_type : Equivalence eq_type.
Proof.
  constructor.
  - reflexivity.
  - intros. symmetry. auto.
  - intros. etransitivity; eauto.
Qed. *)


#[global] Instance Refl_eq_multitype : Reflexive eq_multitype.
Proof.
  substs.
  intro t. 
  induction t; simpls*.
  apply* Eq_MT_Cons.
Qed.

#[global] Instance Symm_eq_multitype : Symmetric eq_multitype.
Proof.
  intros t₁ t₂ Heq; inductions Heq; autos*.
  apply* Eq_MT_Cons.
Qed.

#[global] Instance Trans_eq_multitype : Transitive eq_multitype.
Proof.
  intros t₁ t₂ t₃ Heq1 Heq2.
  autos*.
Qed.

Generalizable Variables A rel.

Lemma eq_empty_is_empty :
  ∀ mt, eq_multitype mt MT_Empty -> mt = MT_Empty.
Proof.
  introv Heq.
  inductions Heq; autos.
Qed.

Lemma union_empty_r : 
  ∀ (mt : multitype),
    (union mt MT_Empty) = mt.
Proof.
  induction mt; simpls*.
  rewrites* IHmt.
Qed.


Lemma nnil_union : 
  ∀ mt1 mt2, 
  mt1 ≠ {{ nil }} \/ mt2 ≠ {{ nil }} <->
  mt1 ⊎ mt2 ≠ {{nil}}.
Proof.
  split.
  - introv [Hmt1_nnil | Hmt2_nnil]; inductions mt1; autos*;
    absurd.
  - introv H_nnil;
    destruct mt1; simpls*.
    left; absurd.
Qed.

Lemma nil_eq_union :
  ∀ mt1 mt2, 
  mt1 = {{ nil }} /\ mt2 = {{ nil }} <->
  mt1 ⊎ mt2 = {{nil}}.
Proof.
  split.
  - introv [Hmt1_nil Hmt2_nil]; inductions mt1; 
    repeat match goal with 
    | [H : _ = {{nil}} |- _] => rewrite H 
    | [H : {{nil}} = _ |- _] => rewrite <- H
    end; simpls*.
  - introv H_nil;
    destruct mt1; simpls*.
    inversion H_nil.
Qed.

Lemma union_perm_tail : 
  ∀ (mt₁ mt₂ mt₂': multitype), 
  eq_multitype mt₂ mt₂' -> 
  eq_multitype (union mt₁ mt₂) (union mt₁ mt₂').
Proof.
  introv Heq.
  inductions mt₁; simpls*.
  apply* Eq_MT_Cons.
Qed.


Lemma union_perm_head : 
  ∀ (mt₁ mt₁' mt₂ : multitype),
  eq_multitype mt₁ mt₁' -> 
  eq_multitype (union mt₁ mt₂) (union mt₁' mt₂).
Proof with eauto with permutation_hints.
  introv Heq.
  inductions Heq; simpls*.
Qed.

Lemma union_perm : 
  ∀ (mt₁ mt₁' mt₂ mt₂' : multitype),
  eq_multitype mt₁ mt₁' ->
  eq_multitype mt₂ mt₂' ->
  eq_multitype (union mt₁ mt₂) (union mt₁' mt₂').
Proof.
  intros.
  unfolds trans.
  transitivity (mt₁' ⊎ mt₂).
  - applys* union_perm_head.
  - applys* union_perm_tail.
Qed.



Lemma union_insert : 
  ∀ (mt₁ mt₁' mt₂ mt₂' : multitype) (t t' : type),
  eq_multitype mt₁ mt₁' -> 
  eq_multitype mt₂ mt₂' -> 
  eq_type t t' -> 
  eq_multitype
    (union mt₁ (MT_Cons t mt₂))
    (union mt₁' (MT_Cons t' mt₂'))
  .
Proof.
  introv Heq1 Heq2 Heqt.
  induction Heq1; applys* union_perm.
Qed.

Lemma union_cons : 
  ∀ (mt : multitype) (t : type),
  eq_multitype (MT_Cons t mt) (union mt (MT_Cons t MT_Empty)).
Proof.
  intros.
  inductions mt; simpls*.
  - transitivity {{` t `; ` t0 `; ` mt `}}.
    + autos*.
    + apply Eq_MT_Cons.
      * reflexivity.
      * autos*.
Qed.


Theorem union_assoc : 
  ∀ (mt₁ mt₂ mt₃ : multitype),
  eq_multitype 
    (union (union mt₁ mt₂) mt₃)
    (union mt₁ (union mt₂ mt₃)).
Proof.
  intros.
  inductions mt₁; simpls*.
  apply* Eq_MT_Cons.
Qed.

Theorem union_comm : 
  ∀ mt₁ mt₂, eq_multitype (union mt₁ mt₂) (union mt₂ mt₁).
Proof.
  hint union_empty_r, union_assoc, union_cons, union_perm_head.
  induction mt₁ as [|h₁ mt₁']; intro mt₂.
  - rewrites* union_empty_r.
  - autos*.
Qed.


Lemma eq_union_left : 
  ∀ mt₁ mt₁' mt₂, 
  eq_multitype mt₁ mt₁'-> 
  eq_multitype (union mt₁ mt₂) (union mt₁' mt₂).
Proof with eauto with permutation_hints.
  introv Heq.
  inductions Heq; autos*;
  try reflexivity.
  simpls.
  apply Eq_MT_Swap.
Qed.



Lemma eq_union_right: 
  ∀ mt₁ mt₂ mt₂', 
  eq_multitype mt₂ mt₂'-> 
  eq_multitype (union mt₁ mt₂) (union mt₁ mt₂').
Proof.
  introv Heq.
  hint eq_union_left, union_comm.
  transitivity (mt₂ ⊎ mt₁); autos*.
Qed.

Lemma eq_union : 
  ∀ t₁ t₁' t₂ t₂', 
  eq_multitype t₁ t₁' -> 
  eq_multitype t₂ t₂' -> 
  eq_multitype (union t₁ t₂) (union t₁' t₂').
Proof.
  introv Heq1 Heq2.
  hint eq_union_left, eq_union_right, union_comm.
  autos*.
Qed.

Fixpoint size_aux (mt : multitype) : nat := match mt with 
    | MT_Empty => 0 
    | MT_Cons _ mt' => 1 + size_aux mt'
end.

#[global] Instance Sized_multitype : Sized multitype := { 
  size := size_aux
}.

Lemma eq_size : 
  ∀ M₁ M₂,
  eq_multitype M₁ M₂ -> 
  size M₁ = size M₂.
Proof.
  intros.
  induction* H; simpls.
  fequals.
Qed.

Lemma size_union :
  ∀ M₁ M₂,
  size (M₁ ⊎ M₂) = size M₁ + size M₂.
Proof.
  induction M₁; simpls; introv; try rewrite IHM₁; reflexivity.
Qed. 

Fixpoint In (t : type) (mt : multitype) : Prop := 
  match mt with 
  | {{ nil }} => False
  | {{ h ; mt }} => (eq_type t h) \/ (In t mt)
  end.

Lemma eq_in :
  ∀ (t : type) (mt₁ mt₂ : multitype),
  eq_multitype mt₁ mt₂ -> 
  In t mt₁ ->
  In t mt₂.
Proof.
  intros * Heq Hin.
  induction Heq; autos*;
  inverts Hin; simpls*.
  left.
  transitivity t₁; assumption.
Qed.



Lemma eq_tight : 
  ∀ t₁ t₂, 
  eq_type t₁ t₂ ->
  tight t₁ -> 
  tight t₂.
Proof with eauto using eq_in with permutation_hints.
  intros * Heq.
  pose (P0 (mt₁ mt₂ : multitype) (Heqₘ : eq_multitype mt₁ mt₂) := tight mt₁ -> tight mt₂).
  eq_type_induction Heq P0; intros;
  repeat match goal with 
  | [H : tight {{ _ ; _}} |- _] => destruct H
  | [ _: _ |- tight {{ _ ; _}}] => split
  end; simpls; split_and_or_max; autos*.
Qed.

Lemma eq_tight_multitype : 
  ∀ mt₁ mt₂, 
  eq_multitype mt₁ mt₂ ->
  tight mt₁ -> 
  tight mt₂.
Proof.
  intros * Heq.
  pose (P (t₁ t₂ : type) (Heqₜ : eq_type t₁ t₂) := tight t₁ -> tight t₂).
  eq_multitype_induction Heq P; autos*; intros Htight;
  simpls; split_and_or; autos*.
Qed.


Lemma mt_union_tight :
  ∀ (mt₁ mt₂ mt : multitype), 
    eq_multitype (union mt₁ mt₂) mt -> 
    tight mt -> 
    tight mt₁ /\ tight mt₂.
Proof.
  hint eq_tight_multitype.
  inductions mt₁; intros; split_and_or; try solve[ simpls* ].
  - apply eq_tight_multitype with (mt₁ := mt); 
    try symmetry;
    simpls*.
  - change {{` t `; ` mt₁ `}} with (union {{t ; nil}} mt₁) in *.
    asserts Heq : (eq_multitype (union mt₁ {{ t ; mt₂}}) mt).
    { 
      change {{` t `; ` mt₂ `}} with (union {{t ; nil}} mt₂) in *.
      transitivity ((mt₁ ⊎ {{t ; nil}}) ⊎ mt₂)...
      - symmetry. apply union_assoc.
      - transitivity (({{` t `; nil}} ⊎ mt₁) ⊎ mt₂); autos.
        apply eq_union_left;
        apply union_comm.
    }
    apply IHmt₁ in Heq; repeat (split_and_or; simpls); autos.
  - apply eq_tight_multitype 
    with (mt₂ := union {{` t `; ` mt₁ `}} mt₂) in H0; 
    simpls*; split_and_or_max.
    edestruct IHmt₁; autos*.
Qed.


Lemma mt_tight_union :
  ∀ mt₁ mt₂,
  tight mt₁ ->
  tight mt₂ ->
  tight (mt₁ ⊎ mt₂).
Proof.
  induction mt₁; introv Htight1 Htight2; simpls*.
Qed.