
From Coq Require Import Unicode.Utf8_core.
From Coq Require Import Lia.
From Coq Require Import Lists.ListSet.
From Coq Require Import Classes.Equivalence.
From Coq Require Import List.
Import ListNotations.
From TLC Require Import LibLN LibTactics LibFset.


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

Fixpoint is_tight_type (t : type) : Prop :=
  match t with
  | Ty_Tight _ => True 
  | Ty_Atomic _ _ => False
  | Ty_Fun _ _ => False
  | Ty_Mult mt => is_tight_multitype mt
  end
with is_tight_multitype (mt : multitype) : Prop :=
  match mt with 
  | MT_Empty => True
  | MT_Cons t mt' => (is_tight_type t) /\ (is_tight_multitype mt')
  end.

Create HintDb permutation_hints.

  Inductive permutationₜ : type -> type -> Prop :=
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
  with permutationₘ : multitype -> multitype -> Prop :=
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
  Scheme permutationₜ_mut_ind := Induction for permutationₜ Sort Prop
  with permutationₘ_mut_ind := Induction for permutationₘ Sort Prop.

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
  Parameter eq : T -> T -> Prop. 
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

  Lemma eq_empty_is_empty :
    ∀ mt, eq mt MT_Empty -> mt = MT_Empty.
  Proof.
    introv H_eq.
    inductions H_eq; autos.
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

  Fixpoint size (mt : multitype) :=
  match mt with 
  | MT_Empty => 0 
  | MT_Cons _ mt' => 1 + size mt'
  end.
  
End Multitype.




Declare Custom Entry multitype. 

Notation "{{ mt }}" := mt (mt custom multitype at level 99).
Notation "( mt )" := mt (in custom multitype, mt at level 99).
Notation "'nil'" := MT_Empty (in custom multitype at level 0).
Notation "t" := t (in custom multitype at level 0, t constr at level 0).
Notation "` t `" := t (in custom multitype at level 0, t constr at level 0).
Notation " t ; mt" := (MT_Cons t mt) (in custom multitype at level 90, mt custom multitype at level 99, left associativity).

Notation "mt |-> t" := (Ty_Fun mt t) (at level 99, right associativity).
Notation "{{ mt }} |-> t" := (Ty_Fun mt t) (in custom multitype at level 80, right associativity).
Notation "a ⊎ b" := (Multitype.union a b) (at level 0).


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
  intros. 
  repeat match goal with 
  | [H : is_tight_multitype {{ _ ; _}} |- _] => destruct H
  | [ _: _ |- is_tight_multitype {{ _ ; _}}] => split
  end...
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
  intros.
  repeat match goal with 
  | [H : is_tight_multitype {{ _ ; _}} |- _] => destruct H
  | [ _: _ |- is_tight_multitype {{ _ ; _}}] => split
  end...
Qed.
Ltac split_and := 
  match goal with 
  | [ |- _ /\ _ ] => split
  | [H : _ /\ _ |- _] => destruct H
  end.

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


Inductive Add (t : type) : multitype -> multitype -> Prop :=
  | Add_head mt : ∀ t' mt', Multitype.eq mt mt' -> permutationₜ t t' -> Add t mt {{ t'; mt' }}
  | Add_cons t' mt1 mt2 :
      ∀ t'',
      permutationₜ t' t'' ->
      Add t mt1 mt2 -> 
      Add t {{ t';mt1 }} {{t'' ; mt2}}.

Lemma Add_app t mt1 mt2 : Add t (mt1 ⊎ mt2) (mt1 ⊎ {{t ; mt2}}).
Proof.
  Hint Constructors Add  : core. 
  Hint Resolve permₜ_refl Multitype.eq_refl : core.
  inductions mt1; simpls; autos.
Qed.


Lemma Add_split t mt mt' :
    Add t mt mt' -> exists mt1 mt2, Multitype.eq mt (mt1 ⊎ mt2) /\ Multitype.eq mt' (mt1 ⊎ {{t ; mt2}}).
Proof.
  Hint Constructors Add  : core. 
  Hint Resolve 
    P_MT_Cons permₜ_refl permₜ_sym 
    Multitype.eq_refl Multitype.eq_refl permₘ_refl permₘ_sym  : core.
  Hint Unfold union : core.
  intros.
  inductions H.
  - exists {{nil}}. exists* mt; split*; simpls.
    applys* P_MT_Cons.
  - destruct IHAdd as [mt3 [mt4 [H_eq1 H_eq2]]]; substs.
    exists {{ t' ; mt3 }}. exists* mt4; split*; simpls;
    applys* P_MT_Cons.
Qed.

Lemma Add_in t mt mt' : Add t mt mt' ->
   ∀ x, In x mt' <-> In x {{t ; mt}}.
Proof.
  Hint Resolve Add_split Add_app Add_head Add_cons permₜ_trans permₜ_sym : core.
  intros H_Add x.
  split; intros H_in;
  inductions H_Add; autos*;
  destruct* H_in; simpls*.
  - right. inductions H; autos*. 
    + inverts* H2.
      * left*.
      * right*.
    + inverts* H1.
      * right. left*.
      * inverts H.
        -- left*.  
        -- right. right*.  
  - apply IHH_Add in H0; autos*.
  - right*. inductions H; autos*. 
    + inverts* H2.
      * left*.
      * right*.
    + inverts* H1.
      * right. left*.
      * inverts H.
        -- left*.  
        -- right. right*.
Qed.


(* Lemma Add_length a l l' : Add a l l' -> length l' = S (length l). *)


Lemma Add_inv t mt : In t mt -> exists mt', Add t mt' mt.
Proof.
  intro H_in.
  inductions mt; inverts H_in.
  - exists* mt.
  - apply IHmt in H as [mt' HAdd]. autos*.
Qed.
  (* Lemma incl_Add_inv a l u v :
    ~In a l -> incl (a::l) v -> Add a u v -> incl l u. *)


Lemma eq_Add t mt mt' : Add t mt mt' -> Multitype.eq {{t ; mt}} mt'.
Proof.
  Hint Resolve Multitype.eq_refl P_MT_Swap P_MT_Trans P_MT_Cons permₜ_refl : core.
  induction 1; simpls*.
  - applys* P_MT_Cons.
  - apply P_MT_Trans with {{` t' `; ` t `; ` mt1 `}}; autos*.
Qed.


Theorem eq_ind_bis :
 ∀ P : multitype -> multitype -> Prop,
   P {{nil}} {{nil}} ->
   (∀ t t' mt mt', permutationₜ t t' -> Multitype.eq mt mt' -> P mt mt' -> P {{t ; mt}} {{t' ; mt'}}) ->
   (∀ t1 t1' t2 t2' mt mt', permutationₜ t1 t1' -> permutationₜ t2 t2' -> Multitype.eq mt mt' -> P mt mt' -> P {{t2 ; t1 ; mt}} {{t1' ; t2' ; mt'}}) ->
   (∀ mt mt' mt'', Multitype.eq mt mt' -> P mt mt' -> Multitype.eq mt' mt'' -> P mt' mt'' -> P mt mt'') ->
   ∀ mt mt', Multitype.eq mt mt' -> P mt mt'.
Proof.
  Hint Resolve permₜ_refl : core.
  intros P Hnil Hskip Hswap Htrans mt mt' Heq.
  inductions Heq; autos.
  -  applys* Hswap.
    induction mt; autos*.
  - autos*.
Qed.   


Ltac InvAdd := repeat (match goal with
 | H: Add ?x _ {{_ ; _}} |- _ => inversion H; clear H; subst
 end).
Ltac finish_basic_perms H :=
  try constructor; try rewrite P_MT_Swap; try constructor; trivial;
  (rewrite <- H; now apply eq_Add) ||
  (rewrite H; symmetry; now apply eq_Add).



Goal ∀ t mt1 mt2 mtf, Multitype.eq mt1 mt2 -> Add t mt1 mtf -> Add t mt2 mtf.
Proof.
  Hint Resolve 
    Multitype.eq_refl 
    P_MT_Swap P_MT_Trans P_MT_Cons permₜ_refl 
    eq_Add Add_in Add_split Add_app Add_head Add_cons : core.
  introv Heq HAdd.
  inductions Heq.
  - inverts* HAdd.
  - inverts* HAdd.
    applys Add_head; autos*.
    + apply Multitype.eq_trans with {{` t₁ `; ` mt₁ `}}; autos*.
      applys* P_MT_Cons.
    + applys* Add_cons.
      admit.
  - inverts HAdd.
    + applys* Add_head.
      apply Multitype.eq_trans with {{` t₁ `; ` t₂ `; ` mt `}}; autos*.
Admitted.



Theorem eq_Add_inv t mt1 mt2 :
  Multitype.eq mt1 mt2 -> ∀ mt1' mt2', Add t mt1' mt1 -> Add t mt2' mt2 ->
   Multitype.eq mt1' mt2'.
Proof.
  Hint Resolve 
    Multitype.eq_refl 
    P_MT_Swap P_MT_Trans P_MT_Cons permₜ_refl 
    eq_Add Add_in Add_split Add_app Add_head Add_cons : core.
  
 (* revert mt1 mt2. refine (eq_ind_bis _ _ _ _ _).
  - (* nil *)
   inversion_clear 1.
 - (* skip *)
   intros x l1 l2 PE IH. intros. InvAdd; try finish_basic_perms PE.
   constructor. now apply IH.
 - (* swap *)
   intros x y l1 l2 PE IH. intros. InvAdd; try finish_basic_perms PE.
   rewrite perm_swap; do 2 constructor. now apply IH.
 - (* trans *)
   intros l1 l l2 PE IH PE' IH' l1' l2' AD1 AD2.
   assert (Ha : In a l). { rewrite <- PE. rewrite (Add_in AD1). simpl; auto. }
   destruct (Add_inv _ _ Ha) as (l',AD).
   transitivity l'; auto. *)
Admitted.


 
 
(* Qed. *)


(* 

  

End Add.



Theorem Multitype.eq_cons_inv l l' a :
 Multitype.eq (a::l) (a::l') -> Multitype.eq l l'.
Proof.
  intro. eapply Multitype.eq_Add_inv; eauto using Add_head.
Qed.

 *)
Goal 
  ∀ A mt1 mt2,
  Multitype.eq {{A; mt1}} {{A; mt2}} ->
  Multitype.eq {{mt1}} {{mt2}}.
Proof.
  Hint Resolve Multitype.eq_refl : core.
  introv Heq.
  inductions Heq; autos*.
  Admitted.