(*
  Tight Typings and Split Bounds,
    BENIAMINO ACCATTOLI
    STÉPHANE GRAHAM-LENGRAND
    DELIA KESNER
  https://arxiv.org/pdf/1807.02358.pdf
*)
Set Default Goal Selector "!".
From Coq Require Import String.
From Coq Require Import PeanoNat.
From Coq Require Import Arith.
From Coq Require Import Unicode.Utf8.
From Coq Require Import Lia.
From Coq Require Import Lists.ListSet.
From Coq Require Import List.
From Coq Require Import Classes.Equivalence.
Require Import EvaluationSystem.
Require Import Tactics.
Require Import Syntax.
Require Import Types.Types.
Import ListNotations.



Inductive neutral : term -> Prop :=
| Neutral_Var : ∀ (n : nat), neutral <{#n}>
| Neutral_App : ∀ (t₁ t₂ : term), neutral t₁ -> neutral <{t₁ t₂}>
.
Inductive normal : term -> Prop := 
| Normal_Neutral : ∀ (t : term), neutral t -> normal t 
| Normal_Abs : ∀ (t : term), normal t -> normal <{λ t}> 
.
Hint Constructors neutral : core.
Hint Constructors normal : core.

Ltac neutral_to_normal t := 
  match goal with 
  | [H : neutral t |- _] => let H_normal := fresh "H_normal" in apply Normal_Neutral in H 
  end.  

Inductive abs : term -> Prop := 
| Abs : ∀ (t : term), abs <{ λ t }>
.
Hint Constructors abs : core.

Ltac contra_neutral_abs := 
  match goal with 
  | [H : ¬ abs (Trm_Abs _) |- _] => exfalso; apply H; apply Abs
  | [H : neutral (Trm_Abs _) |- _] => inversion H 
  | _ => idtac
  end.


Reserved Notation "a --> b" (at level 0).
Inductive step : term -> term -> Prop :=
| ST_Beta : 
    ∀ (u q : term), 
    <{ (λ u) q }> --> (lower 0 <{u[0 <- q]}>)
| ST_Abs : 
    ∀ (t p : term),
    t --> p -> 
    <{λ t}> --> <{λ p}>
| ST_App : 
    ∀ (t p u : term), 
    (abs t -> False) -> 
    t --> p ->
    <{t u}> --> <{p u}>
where 
  "a --> b" := (step a b)
.
Hint Constructors step : core.

Theorem deterministic_step : deterministic step.
Proof with (myauto contra_neutral_abs).
  unfold deterministic.
  intros * H.
  generalize dependent a₂.
  induction H; intros;
  match goal with 
  | [H : step _ _ |- _] => 
      inversion H; subst; 
      try f_equal; try contra_neutral_abs
  end; myauto idtac.
Qed.
Hint Resolve deterministic_step : core.


Definition multistep : term -> term -> Set := reflexive_closure (transitive_closure step).
Notation "a -->* b" := (multistep a b) (at level 0).

Fixpoint size (t : term) : nat := 
  match t with
  | <{ #_ }> => 0 
  | <{λ t}> 
  | <{ t _ }> => 1 + size t
  end.

Hint Unfold size  : HeadEvaluation.



Goal <{(λ λ #1 #2) (λ #0)}> --> <{λ (λ #0) #1}>.
apply ST_Beta.
Qed.



Lemma neutral_is_normal_not_abs : 
  ∀ (t : term), 
  normal t -> (¬ abs t) -> 
  neutral t.
Proof with myauto contra_neutral_abs.
  intros * H_normal_t H_not_abs_t.
  inversion H_normal_t; subst...
Qed.
Hint Resolve neutral_is_normal_not_abs : core.

Theorem head_red_eval_system :
  evaluation_system term step normal neutral abs.
Proof with myauto contra_neutral_abs.
  repeat split...
  - intro H_rel_normal.
    unfold rel_normal in *.
    induction t...
    + induction t1...
      * apply Normal_Neutral. apply Neutral_App. 
        apply neutral_is_normal_not_abs...
        apply IHt1.
        intros [a' H_st].
        apply H_rel_normal.
        exists <{a' t2}>...
        apply ST_App...
    + apply Normal_Abs. apply IHt. intros [a' Hst]...
  - intro.
    induction H as [t H_neutral | t H_norm IH].
    + induction H_neutral; intros [a Hst]; inversion Hst; subst...
    + intros [a H_st].
      inversion H_st; subst... 
  - inversion H; subst...
  - intros [H_normal_t H_not_abs_t]...  
Qed.



Section HeadTypingSystem.

        (* TODO:
          Rajouter multi-ensemble vide 
          ou 
          remplacer singleton par vide + T_Many: un multitype et un type *)
        

    Reserved Notation "Γ '|(' b ',' r ')-' t '∈' T" (at level 70).
    Reserved Notation "Γ '|(' b ',' r ')-' t '∈ₘ' T" (at level 70).

    Inductive has_type : Ctx.t -> nat -> nat -> term -> type -> Type :=
    | T_Ax0 :
        ∀ {A : type},
        [ {{ A ; nil }} ] |(0, 0)- <{ #0 }> ∈ A
    | T_Ax0_Empty : 
        ∀ {A: type} {h : multitype} {Γ : Ctx.t},
        h::Γ |(0, 0)- <{#0}> ∈ A ->
        h::{{nil}}::Γ |(0, 0)- <{#0}> ∈ A
    | T_AxS : 
        ∀ {A: type} {Γ : Ctx.t} {x : nat},
        Γ |(0, 0)- <{#x}> ∈ A ->
        {{nil}}::Γ |(0, 0)- <{#`S x`}> ∈ A
    (* | T_Many_Inv :
        ∀ {Γ: Ctx.t} {t : term} {A : type} {b r : nat},
         
        Γ |(b, r)- t ∈ₘ {{A ; nil}} -> 
        Γ |(b, r)- t ∈ A *)
    | T_Fun_b :
        ∀ {t : term} {mt : multitype} {A : type} {Γ : Ctx.t} {b r : nat},
        mt :: Γ |(b, r)- t ∈ A -> 
        Γ |(S b, r)- <{ λ t }> ∈ Ty_Fun mt A
    | T_Fun_r : 
        ∀ {t : term} {T A : type} {Γ : Ctx.t} {b r : nat},
        is_tight_type A ->
        is_tight_type T ->
        (MT_Cons T MT_Empty) :: Γ |(b, r)- t ∈ A -> 
        Γ |(b, S r)-  <{ λ t }> ∈ Ty_Tight TC_Abs 
    | T_App_b :
        ∀ {Γ₁ Γ₂ Δ : Ctx.t} {M : multitype} {A : type}
          {b₁ b₂ r₁ r₂ : nat} {t₁ t₂ : term}, 
        Γ₁ ⊎c Γ₂ ≡ Δ ->
        Γ₁ |(b₁, r₁)- t₁ ∈ Ty_Fun M A ->
        Γ₂ |(b₂, r₂)- t₂ ∈ₘ M ->  
        Δ |(b₁ + b₂, r₁ + r₂)- <{ t₁ t₂ }> ∈ A
    | T_App_hd_r :
        ∀ {Γ : Ctx.t} {t₁ t₂ : term} {b r : nat},
        Γ |(b, r)- t₁ ∈ Ty_Tight TC_Neutral -> 
        Γ |(b, S r)- <{ t₁ t₂ }> ∈ Ty_Tight TC_Neutral
    where 
      "Γ '|(' b ',' r ')-' t '∈' T" := (has_type Γ b r t T)
    with has_many_types : Ctx.t -> nat -> nat -> term -> multitype -> Type :=
    (* | ManyT_Empty : 
      ∀ t, 
      [] |(0, 0)- t ∈ₘ {{nil}} *)
    | ManyT_Singleton :
      ∀ {Γ : Ctx.t} {t : term} {A : type} {b r : nat},
        Γ |(b, r)- t ∈ A ->
        Γ |(b, r)- t ∈ₘ {{ A ; nil }} 
    | ManyT_Union :
        ∀ {Γ₁ Γ₂ Δ: Ctx.t} {t : term} {mt₁ mt₂ : multitype} {b₁ b₂ r₁ r₂ : nat},
        Γ₁ ⊎c Γ₂ ≡ Δ ->
        Γ₁ |(b₁, r₁)- t ∈ₘ mt₁ ->
        Γ₂ |(b₂, r₂)- t ∈ₘ mt₂ ->
        Δ |(b₁ + b₂, r₁ + r₂)- t ∈ₘ (mt₁ ⊎ mt₂)
    | ManyT_Inv :
      ∀ {Γ₁ Γ₂ Δ : Ctx.t} {t : term} {A : type} {mt₁ mt₂ mtᵤ : multitype} {b₁ b₂ r₁ r₂ : nat},
        Γ₁ ⊎c Γ₂ ≡ Δ ->
        Multitype.eq (mt₁ ⊎ mt₂) mtᵤ ->
        Δ  |(b₁ + b₂, r₁ + r₂)- t ∈ₘ mtᵤ ->
        Γ₁ |(b₁, r₁)- t ∈ₘ mt₁ ->
        Γ₂ |(b₂, r₂)- t ∈ₘ mt₂

    where 
      "Γ '|(' b ',' r ')-' t '∈ₘ' T" := (has_many_types Γ b r t T)
    .

    Hint Constructors has_type has_many_types : core.
    Scheme has_type_mut_ind := Induction for has_type Sort Type
    with has_many_types_mut_ind := Induction for has_many_types Sort Type.
    Scheme has_type_mut_rec := Induction for has_type Sort Set
    with has_many_types_mut_rec := Induction for has_many_types Sort Set.

  


  Fixpoint size_typing_derivation {b r : nat} {Γ : Ctx.t} {t : term} {T : type} (der : Γ |( b , r )- t ∈ T) : nat :=
    match der with 
      | T_Ax0  => 0
      | T_Ax0_Empty _ => 0
      | T_AxS _  => 0
      (* | T_Many_Inv der => size_many_typing_derivation der *)
      | T_Fun_b der' => S (size_typing_derivation der')
      | T_Fun_r _ _ der' => S (size_typing_derivation der')
      | T_App_b _ der₁ der₂ => 
          S ((size_typing_derivation der₁) + (size_many_typing_derivation der₂))
      | T_App_hd_r der' => S (size_typing_derivation der')
      end
  with 
    size_many_typing_derivation {b r : nat} {Γ : Ctx.t} {t : term} {M : multitype} (der : Γ |( b , r )- t ∈ₘ M) : nat :=
    match der with 
    (* | ManyT_Empty _ => 0 *)
    | ManyT_Singleton der => size_typing_derivation der
    | ManyT_Union _ der₁ der₂ => size_many_typing_derivation der₁ + size_many_typing_derivation der₂
    | ManyT_Inv _ _ der _ => size_many_typing_derivation der
    end
  .

  Definition is_tight_derivation 
    {b r : nat} {Γ : Ctx.t} {t : term} {T : type} 
    (der : Γ |( b , r )- t ∈ T) : Prop 
  := 
    (is_tight_type T) /\  (is_tight_context Γ).
    
    Check has_type_mut_ind.

Ltac derivation_induction der P0 := 
  induction der using has_type_mut_ind with (P0:=P0); unfold P0 in *; clear P0.



Definition Id := <{ λ #0 }>.
Definition example_term := <{ (λ ((λ #0 #1) #0)) `Id` }>.
Example example_1_is_Id : example_term -->* Id.
Proof.
  unfold example_term.
  apply RC_self.
  eapply TC_trans.
  - eapply TC_self. apply ST_Beta.
  - simpl. eapply TC_trans; simpl; eapply TC_self.
    + eapply ST_Beta. 
    + eapply ST_Beta.
Qed. 

Definition abs_abs := {{ ` Ty_Tight TC_Abs ` ; nil }} |-> Ty_Tight TC_Abs.

Example first_derivation : [] |(3, 1)- example_term ∈ (Ty_Tight TC_Abs).
Proof with eauto using Ctx.Union_Nil, Ctx.Union_Cons, Multitype.eq_refl.
  unfold example_term.
  apply @T_App_b with 
    (b₁ := 2)
    (b₂ := 1)
    (r₁ := 0)
    (r₂ := 1)
    (Γ₁ := []) 
    (Γ₂ :=[]) 
    (
    M := {{ 
        ` Ty_Tight TC_Abs ` ; 
        ` abs_abs ` ; 
          nil 
        }}
    )...
  - apply T_Fun_b.
    apply @T_App_b with 
      (Γ₁ := [{{ ` Ty_Tight TC_Abs ` ; nil }}]) 
      (Γ₂ := [{{ ` abs_abs ` ; nil }}]) 
      (b₁ := 1) 
      (b₂ := 0) 
      (r₁ := 0) 
      (r₂ := 0)
       (M := {{ abs_abs ; nil}})...
    apply T_Fun_b.
    unfold abs_abs.
    apply @T_App_b with 
    (Γ₁ := [ {{ ` abs_abs ` ; nil }} ; {{nil}}])
    (Γ₂ := [ {{nil}}; {{ ` Ty_Tight TC_Abs ` ; nil }} ])
    (b₁ := 0) (b₂ := 0) (r₁ := 0) (r₂ := 0) (M := {{ ` Ty_Tight TC_Abs ` ; nil }}); unfold abs_abs...
  - unfold Id.
    change 1 with (1 + 0) at 2.
    change 1 with (0 + 1) at 1.
    eapply @ManyT_Union with (mt₁ := {{`Ty_Tight TC_Abs`; nil}}) (mt₂ := {{ `abs_abs` ; nil }}); unfold abs_abs...
    apply ManyT_Singleton...
    eapply @T_Fun_r 
      with (T := Ty_Tight TC_Abs) (A := Ty_Tight TC_Abs)...
Qed.



Definition last_rule_is_appb 
    {b r : nat} {Γ : Ctx.t} {t : term} {T : type} 
    (der : Γ |( b , r )- t ∈ T) : Prop := 
  match der with 
  | T_Ax0 => False
  | T_Ax0_Empty _ => False
  | T_AxS _ => False
  | T_Fun_b _ => False
  | T_Fun_r _ _ _ => False
  | T_App_b _ _ _ => True
  | T_App_hd_r _ => False
  end.


Lemma tight_spreading_var :  
  ∀ {Γ : Ctx.t} {b r : nat} {x : nat} {A : type}
    (φ : Γ |( b, r )- Trm_Bound_Var x ∈ A), 
  is_tight_context Γ -> 
  is_tight_type A /\ ¬ last_rule_is_appb φ.
Proof with eauto.
  intros * H_tight.
  split.
  + generalize dependent Γ.
    generalize dependent b. 
    generalize dependent r. 
    generalize dependent A. 
    induction x; intros * φ H_tight.
    - remember (Trm_Bound_Var 0) as t.
      induction φ; subst; simpl in *; repeat split_and;
      try (inversion Heqt; fail)...
    - remember (Trm_Bound_Var (S x)) as t. 
      induction φ; subst; simpl in *; repeat split_and;
      inversion Heqt; subst...
  + intros * H_contra.
    remember (Trm_Bound_Var x) as t.
    destruct φ eqn:H_eq...
    inversion Heqt. 
Qed.

Ltac tight_union Δ :=
  match goal with 
  | [H : ?Γ₁ ⊎c ?Γ₂ ≡ Δ |- _] => 
    let H_tight_Γ₁ := fresh "H_tight_Γ₁" in 
    let H_tight_Γ₂ := fresh "H_tight_Γ₂" in 
      apply Ctx_union_tight in H as  [H_tight_Γ₁ H_tight_Γ₂]; eauto 
  end.



Lemma tigh_spreading_on_neutral_terms : 
  ∀ {t : term}, neutral t ->
  ∀ {Γ : Ctx.t} {b r : nat} {A : type}
    (φ : Γ |(b, r)- t ∈ A), 
  is_tight_context Γ ->
  is_tight_type A /\ ¬ last_rule_is_appb φ.
Proof with eauto.
  intros t H_neutral.
  induction H_neutral as [ x | p u H_neutral_p IH]; intros Γ b r A φ H_tight.
  - eapply tight_spreading_var...
  - inversion φ; subst...
    + tight_union Γ.
      apply IH in H5; simpl in H5; try contradiction...
    + split...
      remember <{ ` p ` ` u ` }> as t.
      remember (Ty_Tight TC_Neutral) as T.
      destruct φ eqn:Heq; simpl; inversion Heqt; subst...
      tight_union Δ.
      apply IH with (φ := h) in H_tight_Γ₁ as [H_contra _]; simpl in *; contradiction.
Qed.


Lemma normal_size_derivation : 
  ∀ {t : term} {Γ : Ctx.t} {b r : nat} {A : type} 
    (φ : Γ |(b, r)- t ∈ A), 
  normal t -> 
  size t <= size_typing_derivation φ.
Proof with try lia.
  intros * H_normal_t.
  induction φ; inversion H_normal_t; subst; contra_neutral_abs; simpl; try apply IHφ in H0; 
  try (
    inversion H; subst;
    neutral_to_normal t₁;
    apply IHφ in H1; lia
  )...
Qed.

Ltac use_type_spreading Γ :=
  match goal with 
  | [ H : Γ |(_, _)- _ ∈ {{ {{_}} |-> _}} |- _] => 
      apply tigh_spreading_on_neutral_terms in H; eauto; subst; inversion H
  end. 

Theorem normal_tight_der_size_b_r :
  ∀ {t : term} {Γ : Ctx.t} {b r : nat} {A : type} 
    (φ : Γ |(b, r)- t ∈ A), 
  normal t -> 
  is_tight_derivation φ -> 
  b = 0 /\ r = size t.
Proof with try lia; eauto using Ctx_union_tight.
  induction t; intros * H_normal_t H_tight_der; destruct H_tight_der as [H_tight_A H_tight_Γ]; inversion φ; subst; simpl; try (inversion H_tight_A; fail)...
  - assert (is_tight_context Γ₁ /\ is_tight_context Γ₂) 
      as [H_tight_Γ₁ H_tight_Γ₂]...
    inversion H_normal_t. inversion H; subst.
    use_type_spreading Γ₁.
  - inversion H_normal_t; inversion H; subst.
    apply Normal_Neutral in H2.
    eapply IHt1 with (φ := H5) in H2; try split...
  - inversion H_normal_t; contra_neutral_abs; subst; 
    destruct (IHt _ _ _ _ H5); try split...
Qed.  

Theorem normal_neutral_type_is_neutral : 
  ∀ {t : term} {Γ : Ctx.t} {b r : nat} 
    (φ : Γ |(b, r)- t ∈ Ty_Tight TC_Neutral), 
  normal t -> 
  neutral t.
Proof with eauto.
  induction t; intros * φ H_normal_t; inversion H_normal_t; inversion φ...
Qed.

End HeadTypingSystem.


