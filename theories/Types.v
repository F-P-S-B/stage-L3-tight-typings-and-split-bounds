
From Coq Require Import Unicode.Utf8_core.
From Coq Require Import Lia.
From Coq Require Import Lists.ListSet.
From Coq Require Vector.
Import Vector.VectorNotations.
From Coq Require Import Classes.Equivalence.
From Coq Require Import List.
Import ListNotations.
Require Import LogicSet.

Parameter AtomicType : Set.
Parameter X : set AtomicType.
Parameter eqₐ : AtomicType -> AtomicType -> Prop.
Parameter eqₐ_dec : 
  ∀ (t₁ t₂ : AtomicType),
  {eqₐ t₁ t₂} + {¬ eqₐ t₁ t₂}.
Parameter eqₐ_Eq : 
  Equivalence eqₐ.
Infix "≡ₐ" := eqₐ (at level 0).

Inductive tight_constant := 
| TC_Neutral : tight_constant
| TC_Abs : tight_constant
.
Inductive type :=
| Ty_Tight (t : tight_constant) : type
| Ty_Atomic (t : AtomicType) : (set_In t X) -> type
| Ty_Fun : multitype -> type -> type 
| Ty_Mult : multitype -> type
with multitype :=
| MT_Empty : multitype
| MT_Cons (t : type) (mt : multitype) : multitype
.

Scheme type_mut_ind := Induction for type Sort Type
with multitype_mut_ind := Induction for multitype Sort Type.








Fixpoint MT_Union (mt₁ mt₂ : multitype) : multitype :=
  match mt₁ with 
  | MT_Empty => mt₂ 
  | MT_Cons t mt₁ => MT_Cons t (MT_Union mt₁ mt₂)
  end 
.

Fixpoint is_tight_type (t : type) : Set :=
  match t with
  | Ty_Tight _ => True 
  | Ty_Atomic _ _ => False
  | Ty_Fun _ _ => False
  | Ty_Mult mt => is_tight_multitype mt
  end
with is_tight_multitype (mt : multitype) : Set :=
  match mt with 
  | MT_Empty => True
  | MT_Cons t mt' => and_set (is_tight_type t) (is_tight_multitype mt')
  end.

Create HintDb permutation_hints.

  Inductive permutationₜ : type -> type -> Set :=
  | P_Tight : 
      ∀ (t : tight_constant), 
      permutationₜ (Ty_Tight t) (Ty_Tight t)
  | P_Atomic :
      ∀ (t₁ t₂ : AtomicType) 
        (prf₁ : set_In t₁ X) (prf₂ : set_In t₂ X),
      eqₐ t₁ t₂ -> 
      permutationₜ (Ty_Atomic t₁ prf₁) (Ty_Atomic t₂ prf₂)
  | P_Fun : 
      ∀ (mt₁ mt₂ : multitype) (t₁ t₂ : type),
      permutationₘ mt₁ mt₂ -> 
      permutationₜ t₁ t₂ -> 
      permutationₜ (Ty_Fun mt₁ t₁) (Ty_Fun mt₂ t₂)
  | P_Mult : 
      ∀ (mt₁ mt₂ : multitype), 
      permutationₘ mt₁ mt₂ -> 
      permutationₜ (Ty_Mult mt₁) (Ty_Mult mt₂)
  with permutationₘ : multitype -> multitype -> Set :=
  | P_MT_Empty : permutationₘ (MT_Empty) (MT_Empty)
  | P_MT_Cons : 
      ∀ (mt₁ mt₂ : multitype) (t₁ t₂ : type),
      permutationₜ t₁ t₂ -> 
      permutationₘ mt₁ mt₂ -> 
      permutationₘ (MT_Cons t₁ mt₁) (MT_Cons t₂ mt₂)
  | P_MT_Swap : 
      ∀ (t₁ t₂ : type) (mt : multitype),
        permutationₘ 
          (MT_Cons t₁ (MT_Cons t₂ mt))
          (MT_Cons t₂ (MT_Cons t₁ mt))
  | P_MT_Trans :
      ∀ (mt₁ mt₂ mt₃ : multitype),
      permutationₘ mt₁ mt₂ ->
      permutationₘ mt₂ mt₃ ->
      permutationₘ mt₁ mt₃
  .
  Hint Constructors permutationₜ : permutation_hints.
  Hint Constructors permutationₘ : permutation_hints.
  Scheme permutationₜ_mut_ind := Induction for permutationₜ Sort Type
  with permutationₘ_mut_ind := Induction for permutationₘ Sort Type.

  Check permutationₜ_mut_ind.
  Theorem permₜ_refl : ∀ (t : type), permutationₜ t t.
  Proof with eauto with permutation_hints.
    destruct eqₐ_Eq.
    unshelve induction t 
      using type_mut_ind 
      with (P0 := fun mt => permutationₘ mt mt)...
  Qed.

  Theorem permₘ_refl : ∀ (mt : multitype), permutationₘ mt mt.
  Proof with eauto with permutation_hints.
    destruct eqₐ_Eq.
    einduction mt 
      using multitype_mut_ind with (P := fun t => permutationₜ t t)...
  Qed.

  Theorem permₜ_sym : 
    ∀ (t₁ t₂ : type), 
    permutationₜ t₁ t₂ ->
    permutationₜ t₂ t₁.
  Proof with eauto with permutation_hints.
    intros * H_perm.
    destruct eqₐ_Eq.
    pose (
      P0 (mt₁ mt₂ : multitype ) (H_perm : permutationₘ mt₁ mt₂) := 
      permutationₘ mt₂ mt₁ 
    ).
    induction H_perm 
      using permutationₜ_mut_ind 
      with (P0 := P0); unfold P0...
  Qed.
  Theorem permₘ_sym : 
    ∀ (mt₁ mt₂ : multitype), 
    permutationₘ mt₁ mt₂ ->
    permutationₘ mt₂ mt₁.
  Proof with eauto with permutation_hints.
    intros * H_perm.
    destruct eqₐ_Eq.
    pose (
      P (t₁ t₂ : type ) (H_perm : permutationₜ t₁ t₂) := permutationₜ t₂ t₁ 
    ).
    induction H_perm 
      using permutationₘ_mut_ind 
      with (P := P); unfold P...
  Qed.

  Theorem permₜ_trans : 
    ∀ (t₁ t₂ t₃ : type), 
    permutationₜ t₁ t₂ -> 
    permutationₜ t₂ t₃ -> 
    permutationₜ t₁ t₃.
  Proof with eauto with permutation_hints.
    destruct eqₐ_Eq.
    intros * H_perm1.
    generalize dependent t₃.
    pose (
      P0 (mt₁ mt₂ : multitype) (H_perm : permutationₘ mt₁ mt₂) :=
        ∀ (mt₃ : multitype), permutationₘ mt₂ mt₃ -> permutationₘ mt₁ mt₃
    ).
    induction H_perm1 
      using permutationₜ_mut_ind 
      with (P0 := P0); unfold P0; try (
        intros t₃ H_perm2;
        inversion H_perm2;
        eauto with permutation_hints;
        fail
      )...
  Qed.

  Theorem permₘ_trans : 
    ∀ (mt₁ mt₂ mt₃ : multitype), 
    permutationₘ mt₁ mt₂ -> 
    permutationₘ mt₂ mt₃ -> 
    permutationₘ mt₁ mt₃.
  Proof with eauto with permutation_hints.
    destruct eqₐ_Eq.
    intros * H_perm1.
    generalize dependent mt₃.
    pose (
      P (t₁ t₂ : type) (H_perm : permutationₜ t₁ t₂) :=
        ∀ (t₃ : type), permutationₜ t₂ t₃ -> permutationₜ t₁ t₃
    ).
    induction H_perm1 
      using permutationₘ_mut_ind
      with (P := P); unfold P; try (
        intros t₃ H_perm2; 
        inversion H_perm2; eauto with permutation_hints; fail
      )...
  Qed.

  Hint Resolve permₜ_refl permₜ_sym permₜ_trans: permutation_hints.
  Hint Resolve permₘ_refl permₘ_sym permₘ_trans: permutation_hints.

Module Type MULTITYPE.
  Parameter T : Set.
  Parameter eq : T -> T -> Set. 
  Parameter union : T -> T -> T.

  Axiom eq_refl : ∀ (t : T), eq t t.
  Axiom eq_sym : ∀ (t₁ t₂ : T), eq t₁ t₂ -> eq t₂ t₁.
  Axiom eq_trans : ∀ (t₁ t₂ t₃ : T), eq t₁ t₂ -> eq t₂ t₃ -> eq t₁ t₃.
  Axiom union_comm : ∀ mt₁ mt₂, eq (union mt₁ mt₂) (union mt₂ mt₁).
  Axiom union_assoc : 
    ∀ mt₁ mt₂ mt₃, 
    eq 
      (union (union mt₁ mt₂) mt₃) 
      (union mt₁ (union mt₂ mt₃)). 
  
  Axiom eq_union : 
    ∀ t₁ t₁' t₂ t₂', 
    eq t₁ t₁' -> 
    eq t₂ t₂' -> 
    eq (union t₁ t₂) (union t₁' t₂').
  


End MULTITYPE.


Module Multitype <: MULTITYPE.
  Definition T := multitype.
  Definition eq := permutationₘ.
  Definition union := MT_Union.

   
  Theorem eq_refl : ∀ (t : T), eq t t. 
  Proof. 
    unfold eq.
    eauto with permutation_hints.
  Qed.

  Theorem eq_sym : ∀ (t₁ t₂ : T), eq t₁ t₂ -> eq t₂ t₁.
  Proof. 
    unfold eq.
    eauto with permutation_hints.
  Qed.

  Theorem eq_trans : ∀ (t₁ t₂ t₃ : T), eq t₁ t₂ -> eq t₂ t₃ -> eq t₁ t₃.
  Proof. 
    unfold eq.
    eauto with permutation_hints.
  Qed.

  
  Lemma union_empty_r : 
    ∀ (mt : multitype),
      (union mt MT_Empty) = mt.
  Proof with eauto with permutation_hints.
    unfold eq.
    induction mt; simpl...
    rewrite IHmt...
  Qed.

  Lemma union_perm_tail : 
    ∀ (mt₁ mt₂ mt₂': multitype), 
    eq mt₂ mt₂' -> 
    eq (union mt₁ mt₂) (union mt₁ mt₂').
  Proof with eauto with permutation_hints.
    unfold eq.
    induction mt₁...
  Qed.

  Lemma union_perm_head : 
    ∀ (mt₁ mt₁' mt₂ : multitype),
    eq mt₁ mt₁' -> 
    eq (union mt₁ mt₂) (union mt₁' mt₂).
  Proof with eauto with permutation_hints.
    unfold eq.
    intros * H_perm.
    induction H_perm...
  Qed.


  Lemma union_perm_app : 
    ∀ (mt₁ mt₁' mt₂ mt₂' : multitype),
    eq mt₁ mt₁' ->
    eq mt₂ mt₂' ->
    eq (union mt₁ mt₂) (union mt₁' mt₂').
  Proof with unfold eq; eauto with permutation_hints.
    intros.
    eapply permₘ_trans.
    - apply union_perm_head...
    - apply union_perm_tail...
  Qed. 

  Lemma union_insert : 
    ∀ (mt₁ mt₁' mt₂ mt₂' : multitype) (t t' : type),
    eq mt₁ mt₁' -> 
    eq mt₂ mt₂' -> 
    permutationₜ t t' -> 
    eq 
      (union mt₁ (MT_Cons t mt₂))
      (union mt₁' (MT_Cons t' mt₂'))
    .
  Proof with unfold eq; eauto 3 with permutation_hints.
    unfold eq.
    intros * H_eq_1 H_eq_2 H_perm.
    induction H_eq_1; apply union_perm_app...
  Qed.

  Lemma union_cons : 
    ∀ (mt : multitype) (t : type),
    eq (MT_Cons t mt) (union mt (MT_Cons t MT_Empty)).
  Proof with unfold eq; eauto with permutation_hints.
    intros.
    induction mt...
  Qed.


  Theorem union_assoc : 
    ∀ (mt₁ mt₂ mt₃ : multitype),
    eq 
      (union (union mt₁ mt₂) mt₃)
      (union mt₁ (union mt₂ mt₃)).
  Proof with eauto with permutation_hints.
    unfold eq.
    intros.
    induction mt₁...
  Qed.


  Theorem union_comm : ∀ mt₁ mt₂, eq (union mt₁ mt₂) (union mt₂ mt₁).
  Proof with 
    eauto
    using 
      eq_sym, eq_trans, eq_refl,
      union_empty_r, union_assoc, union_cons,
      union_perm_head
    with permutation_hints.
    unfold eq.
    induction mt₁ as [|h₁ mt₁']; simpl; intro mt₂...
    - apply eq_sym. rewrite union_empty_r...
    - eapply eq_trans with (MT_Cons h₁ (union mt₂ mt₁'))...
      + apply P_MT_Cons...
      + apply eq_trans with (union (union mt₂ (MT_Cons h₁ MT_Empty)) mt₁')...
  Qed.

  Lemma eq_union_left : 
    ∀ t₁ t₁' t₂, 
    eq t₁ t₁'-> 
    eq (union t₁ t₂) (union t₁' t₂).
  Proof with eauto with permutation_hints.
    Hint Unfold eq : core.
    intros.
    induction H...
  Qed.

  Lemma eq_union_right : 
    ∀ t₁ t₂ t₂', 
    eq t₂ t₂'-> 
    eq (union t₁ t₂) (union t₁ t₂').
  Proof with eauto using eq_union_left, union_comm with permutation_hints.
    unfold eq.
    intros * H_eq.
    apply eq_trans with (union t₂ t₁)...
    apply eq_trans with (union t₂' t₁)...
  Qed.

  Lemma eq_union : 
    ∀ t₁ t₁' t₂ t₂', 
    eq t₁ t₁' -> 
    eq t₂ t₂' -> 
    eq (union t₁ t₂) (union t₁' t₂').
  Proof with eauto using eq_union_left, eq_union_right with permutation_hints.
    Hint Unfold eq : core.
    intros * H_eq_1 H_eq_2.
    apply eq_trans with (union t₁ t₂')...
  Qed.
  
End Multitype.




Module Context (MT : MULTITYPE).
  Definition t := list MT.T.

  Inductive union : t -> t -> t -> Set :=
  | Union_Nil : union [] [] [] 
  | Union_Cons : 
    ∀  Γ₁ Γ₂ Γᵣ mt₁ mt₂ mtu, 
    union Γ₁ Γ₂ Γᵣ -> 
    MT.eq (MT.union  mt₁ mt₂) mtu ->
    union (mt₁ :: Γ₁) (mt₂ :: Γ₂) (mtu :: Γᵣ)
  .
  Hint Constructors union : core.

  Fixpoint eq (Γ₁ Γ₂ : t) : Set :=
    match Γ₁, Γ₂ with 
    | [], [] => True
    | [], _::_ | _::_, [] => False
    | h₁::t₁, h₂::t₂ => and_set (MT.eq h₁ h₂) (eq t₁ t₂)
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
    apply and_set_intro...
    apply MT.eq_refl.
  Qed.

  Lemma eq_sym : 
    ∀ (Γ₁ Γ₂ : t),
    eq Γ₁ Γ₂ ->
    eq Γ₂ Γ₁.
  Proof with eauto.
    induction Γ₁ as [| mt₁ Γ₁]; intros [| mt₂ Γ₂ ] H_eq; simpl in *; repeat split_and_set...
    apply MT.eq_sym...
  Qed.


  Lemma eq_trans : 
    ∀ (Γ₁ Γ₂ Γ₃: t),
    eq Γ₁ Γ₂ ->
    eq Γ₂ Γ₃ ->
    eq Γ₁ Γ₃.
  Proof with eauto.
    induction Γ₁ as [| mt₁ Γ₁]; intros [| mt₂ Γ₂ ] [| mt₃ Γ₃ ] H_eq1 H_eq2; simpl in *; repeat split_and_set; try contradiction...
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
    apply and_set_intro...
    eapply MT.eq_trans...
    apply MT.eq_sym.
    apply MT.eq_trans with (MT.union mt₁ mt₂)...
    apply MT.union_comm.
  Qed.

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
  inversion H8; inversion H14; subst.
  apply and_set_intro...
  clear H1 H7 H8 H13 H14 H_union_1_23 H_union_12_3 H_union_2_3.
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
    induction Γ₁ as [ | mt₁ Γ₁ IHΓ]; intros [| mt₁' Γ₁'] [ | mt₂ Γ₂] [| mtᵣ Γᵣ] H_eq H_u; inversion H_u; try inversion H_eq; subst; simpl; try split_and_set...
  Qed.

  Lemma eq_union_right : 
    ∀ Γ₁ Γ₂ Γ₂' Γᵣ, 
    eq Γ₂ Γ₂'-> 
    union Γ₁ Γ₂ Γᵣ -> 
    union Γ₁ Γ₂' Γᵣ
    .
  Proof with eauto 6 using MT.eq_union, MT.eq_sym, MT.eq_refl, MT.eq_trans, Union_Cons with permutation_hints.
    induction Γ₁ as [ | mt₁ Γ₁ IHΓ]; intros [| mt₂ Γ₂] [ | mt₂' Γ₂'] [| mtᵣ Γᵣ] H_eq H_u; inversion H_u; try inversion H_eq; subst; simpl; try split_and_set...
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


Fixpoint is_tight_context(Γ : Ctx.t) : Set :=
  match Γ with 
  | [] => True 
  | h::t => and_set (is_tight_multitype h) (is_tight_context t) 
  end.


(* Module Context (MT : MULTITYPE).
  Definition t (n : nat) := Vector.t MT.T n.
  Definition union {n : nat} (c₁ c₂ : t n) := 
    Vector.map2 (fun mt₁ mt₂ => MT.union mt₁ mt₂) c₁ c₂.
  
  Definition eq {n : nat} (c₁ c₂ : t n) : Set :=
      Vector.fold_right2 
        (fun h₁ h₂ acc => and_set (MT.eq h₁ h₂) acc) 
        True
        n 
        c₁ 
        c₂
  .

  Lemma eq_refl : 
    ∀ (n : nat) (c : t n),
    eq c c.
  Proof with auto.
    induction n.
    - eapply Vector.case0. cbv...
    - intro c. eapply (Vector.caseS' c). 
      intros. unfold eq. split...
      + apply MT.eq_refl.
      + apply IHn.
  Qed.

  Lemma eq_sym : 
    ∀ (n : nat) (c₁ c₂ : t n),
    eq c₁ c₂ ->
    eq c₂ c₁.
  Proof with auto.
    intro n.
    eapply (
      Vector.rect2
        (fun n c₁ c₂ => eq c₁ c₂ -> eq c₂ c₁)
    ).
    - cbv...
    - intros n' t₁ t₂ IH h₁ h₂ H_eq.
      destruct H_eq as [H_eq_h H_eq_t].
      split...
      apply MT.eq_sym...
  Qed.

  Lemma eq_trans : 
    ∀ (n : nat) (c₁ c₂ c₃: t n),
    eq c₁ c₂ ->
    eq c₂ c₃ ->
    eq c₁ c₃.
  Proof with auto.
    unfold Transitive in *.
    intro n.
    eapply (
      Vector.rect2
        (fun n c₁ c₂ => ∀ c₃, eq c₁ c₂ -> eq c₂ c₃ -> eq c₁ c₃)
    ).
    - cbv...
    - intros n' t₁ t₂ IH h₁ h₂ c₃.
      apply (Vector.caseS' c₃).
      intros h₃ t₃ H_eq_1_2 H_eq_2_3.
      destruct H_eq_1_2 as [H_eq_h_1_2 H_eq_t_1_2].
      destruct H_eq_2_3 as [H_eq_h_2_3 H_eq_t_2_3].
      split...
      apply MT.eq_trans with h₂...
  Qed.

  
  Theorem union_comm : 
    ∀ (n : nat) (c₁ c₂ : t n),
    eq 
      (union c₁ c₂) 
      (union c₂ c₁).
  Proof with auto.
    intro n.
    eapply (
      Vector.rect2
        (fun n c₁ c₂ => eq (union c₁ c₂) (union c₂ c₁))
    ); simpl...
    intros n' t₁ t₂ H_eq h₁ h₂. split...
    apply MT.union_comm.
  Qed.

  Theorem union_assoc : 
    ∀ (n : nat) (c₁ c₂ c₃ : t n),
    eq 
      (union c₁ (union c₂ c₃))
      (union (union c₁ c₂) c₃).
  Proof with auto.
    intro n.
    eapply (
      Vector.rect2
        (fun n c₁ c₂ => ∀ c₃, eq (union c₁ (union c₂ c₃)) (union (union c₁ c₂) c₃))
    ).
    - apply Vector.case0.
      simpl...
    - intros n' t₁ t₂ IH h₁ h₂ c₃. apply (Vector.caseS' c₃).
      intros h₃ t₃. simpl. split... apply MT.eq_sym. apply MT.union_assoc.
  Qed.

End Context. *)
Hint Unfold is_tight_type is_tight_multitype is_tight_context  : core.
Notation "a ⊎ b" := (Multitype.union a b) (at level 0).
Notation "a '⊎c' b ≡ c" := (Ctx.union a b c) (at level 0).

Declare Custom Entry multitype. 

Notation "{{ mt }}" := mt (mt custom multitype at level 99).
Notation "( mt )" := mt (in custom multitype, mt at level 99).
Notation "'nil'" := MT_Empty (in custom multitype at level 0).
Notation "t" := t (in custom multitype at level 0, t constr at level 0).
Notation "` t `" := t (in custom multitype at level 0, t constr at level 0).
Notation " t ; mt" := (MT_Cons t mt) (in custom multitype at level 90, mt custom multitype at level 99, left associativity).

Notation "mt |-> t" := (Ty_Fun mt t) (at level 99, right associativity).
Notation "{{ mt }} |-> t" := (Ty_Fun mt t) (in custom multitype at level 80, right associativity).

Inductive or_set (A B : Set) : Set :=
| or_set_intro_l : A -> or_set A B 
| or_set_intro_r : B -> or_set A B 
.


Fixpoint In (t : type) (mt : multitype) : Set :=
  match mt with 
  | {{ nil }} => False
  | {{ h ; mt }} => or_set (permutationₜ t h) (In t mt)
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
  permutationₜ_induction H_perm P0; try (intro H_tight; split; inversion H_tight as [H_tight_t H_tight_mt]; repeat apply and_set_intro; try inversion H_tight_mt; eauto using mt_eq_in with permutation_hints; fail)...
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
  induction Γ₁; intros; destruct Γ₂; simpl in *; destruct H, H0; try apply and_set_intro...
Qed.


Lemma mt_union_tight :
  ∀ (mt₁ mt₂ mt : multitype), 
    Multitype.eq (mt₁ ⊎ mt₂) mt -> 
    is_tight_multitype mt -> 
    is_tight_multitype mt₁ ∧a is_tight_multitype mt₂.
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
    apply IHmt₁ in H1; repeat (split_and_set; simpl in *)...
Qed.




Lemma Ctx_union_tight : 
  ∀ (Γ₁ Γ₂ Δ : Ctx.t), Γ₁ ⊎c Γ₂ ≡ Δ -> is_tight_context Δ -> is_tight_context Γ₁ ∧a is_tight_context Γ₂.
Proof with eauto using mt_union_tight, mt_union_tight, mt_eq_in, eq_tight, eq_tight_multitype with permutation_hints.
  intros Γ₁ Γ₂ Δ.
  generalize dependent Γ₂.
  generalize dependent Γ₁.
  induction Δ as [ | mt Δ IH]; intros * H_union H_tight; inversion H_union as [| Γ₁' Γ₂' H1 mt₁ mt₂ H2 H_union' H_eq H3 H4 H5 ]; subst; simpl in *; repeat split_and_set; try edestruct IH;
  try destruct (mt_union_tight mt₁ mt₂ mt)...
Qed.