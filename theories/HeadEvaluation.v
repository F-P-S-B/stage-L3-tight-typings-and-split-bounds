(*
  Tight Typings and Split Bounds,
    BENIAMINO ACCATTOLI
    STÉPHANE GRAHAM-LENGRAND
    DELIA KESNER
  https://arxiv.org/pdf/1807.02358.pdf
*)
Set Default Goal Selector "!".
Require Import String.
Require Import PeanoNat.
Require Import Arith.
From Coq Require Import Unicode.Utf8.
Require Import EvaluationSystem.
Require Import Tactics.
Require Import LogicSet.
Module Syntax.



Inductive term :Set :=
  | Trm_Bound_Var : nat -> term
  | Trm_App : term -> term -> term
  | Trm_Abs : term -> term 
.

Declare Custom Entry term.
Notation "<{ e }>" := e (e custom term at level 99).
Notation "( x )" := x (in custom term, x at level 99).
Notation "x" := x (in custom term at level 0, x constr at level 0).
Notation "'#' n" := (Trm_Bound_Var n) (in custom term at level 0).
Notation "x y" := (Trm_App x y) (in custom term at level 2, left associativity).
Notation "'λ' t" := (Trm_Abs t) (
  in custom term at level 90, 
  t custom term at level 99,
  left associativity
).
Notation "'`' e '`'" := e (in custom term at level 0, e constr).
Search (∀ _, 0 < S _).

Check <{ (λ #0 #1)(λ #1 #0) }>.


Check le_gt_dec.
Fixpoint shift (n : nat) (k : nat) (t : term) : term := 
  match t with 
  | <{ #p }> => 
    match le_gt_dec p k with 
    | left p_le_k => t
    | right p_gt_k => <{ #`p + n - 1 ` }>
    end
  | <{ u v }> => <{`shift n k u` `shift n k v`}> 
  | <{ λ u }> => <{ λ `shift n (k + 1) u` }>
  end.

Check lt_eq_lt_dec. 
Reserved Notation "M '[' n '<-' N ']'" (
  in custom term at level 0,
  n constr
).
Fixpoint subst (t : term) (n : nat) (s : term) : term := 
  match t with 
  | <{ #m }> => 
    match Nat.eq_dec n m with 
    | left eq => shift n 0 s
    | right neq => t
    end
  | <{ u v }> => <{(u[n <- s]) (v[n <- s])}>
  | <{ λ u }> => <{λ u[n+1 <- s]}>
  end
  where
  "M '[' n '<-' N ']'" := (subst M n N) (in custom term).

Fixpoint lower (n : nat) (t : term) : term := 
  match t with 
  | <{#m}> =>
    match le_gt_dec m n with 
    | left m_le_n => t
    | right m_gt_n => <{#`m-1`}>
    end
  | <{λ t}> => <{ λ `lower (n+1) t` }>
  | <{t u}> => <{ `lower n t` `lower n u`}>
  end.

Compute <{ (λ #2 #0 #1)[0 <- #4] }>.


Notation "t '[' s ']'" := (subst s t) (in custom term at level 1, s at level 99, no associativity).

Check <{ λ λ ((λ #2 #1 #0) (λ #0))  }>.

Compute <{(λ λ ((#2 #1 #0) [0 <- λ #0]))}>.
Eval compute in <{(λ λ ((#2 #1 #0)[1 <- λ #0]))}>.
Eval compute in <{(λ λ ((#2 #1 #0)))[0 <- λ #0]}>.

End Syntax.
Import Syntax.



Inductive neutral : term -> Set :=
| Neutral_Var : ∀ (n : nat), neutral <{#n}>
| Neutral_App : ∀ (t₁ t₂ : term), neutral t₁ -> neutral <{t₁ t₂}>
.
Inductive normal : term -> Set := 
| Normal_Neutral : ∀ (t : term), neutral t -> normal t 
| Normal_Abs : ∀ (t : term), normal t -> normal <{λ t}> 
.
Hint Constructors neutral : core.
Hint Constructors normal : core.

Inductive abs : term -> Set := 
| Abs : ∀ (t : term), abs <{ λ t }>
.
Hint Constructors abs : core.

Ltac contra_neutral_abs := 
  match goal with 
  | [H : abs (Trm_Abs _) -> False |- _] => exfalso; apply H; apply Abs
  | [H : neutral (Trm_Abs _) |- _] => inversion H 
  | _ => idtac
  end.


Reserved Notation "a --> b" (at level 0).
Inductive step : term -> term -> Set :=
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



Lemma neutral_is_normal_not_abs : ∀ t, normal t ∧a (abs t -> False) -> neutral t.
Proof with myauto contra_neutral_abs.
  intros * [H_normal_t H_not_abs_t].
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
        apply neutral_is_normal_not_abs. split...
        apply IHt1.
        intros [a' H_st].
        apply H_rel_normal.
        exists <{a' t2}>...
        apply ST_App...
      * exfalso. apply H_rel_normal. eexists... 
    + apply Normal_Abs. apply IHt. intros [a' Hst]...
      apply H_rel_normal. eexists...
  - intro.
    induction H as [t H_neutral | t H_norm IH].
    + induction H_neutral; intros [a Hst]; inversion Hst; subst...
      apply IHH_neutral. eexists...
    + intros [a H_st].
      inversion H_st; subst... 
      apply IH. eexists...
  - intro. inversion H; subst; inversion H0. 
Qed.

From Coq Require Import Lia.
From Coq Require Import Lists.ListSet.
From Coq Require Import List.
Import ListNotations.
From Coq Require Import Classes.Equivalence.

Require Import Types.


Section HeadTypingSystem.

        (* TODO:
          Rajouter multi-ensemble vide 
          ou 
          remplacer singleton par vide + T_Many: un multitype et un type *)
        

    Reserved Notation "Γ '|(' b ',' r ')-' t '∈' T" (at level 70).
    Reserved Notation "Γ '|(' b ',' r ')-' t '∈ₘ' T" (at level 70).

    Inductive has_type : Ctx.t -> nat -> nat -> term -> type -> Set :=
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
    | T_Many_Inv :
        ∀ {Γ: Ctx.t} {t : term} {A : type} {M : multitype} {b₁ b₂ r₁ r₂ : nat},
         
        Γ |(b₁ + b₂, r₁ + r₂)- t ∈ₘ {{A ; nil}} -> 
        Γ |(b₁, r₁)- t ∈ A
    | T_Fun_b :
        ∀ {t : term} {mt : multitype} {A : type} {Γ : Ctx.t} {b r : nat},
        mt :: Γ |(b, r)- t ∈ A -> 
        Γ |(S b, r)- <{ λ t }> ∈ Ty_Fun mt A
    | T_Fun_r : 
        ∀ {t : term} {T A : type} {Γ : Ctx.t} {b r : nat},
        is_tight_type A ->
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
    with has_many_types : Ctx.t -> nat -> nat -> term -> multitype -> Set :=
    | ManyT_Singleton :
      ∀ {Γ : Ctx.t} {t : term} {A : type} {b r : nat},
        Γ |(b, r)- t ∈ A ->
        Γ |(b, r)- t ∈ₘ {{ A ; nil }} 
    | ManyT_Cons :
        ∀ {Γ₁ Γ₂ Δ: Ctx.t} {t : term} {A : type} {mt : multitype} {b₁ b₂ r₁ r₂ : nat},
        Γ₁ ⊎c Γ₂ ≡ Δ ->
        Γ₁ |(b₁, r₁)- t ∈  A ->
        Γ₂ |(b₂, r₂)- t ∈ₘ mt ->
        Δ |(b₁ + b₂, r₁ + r₂)- t ∈ₘ {{ A ; mt }}
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
      | T_Many_Inv der => size_many_typing_derivation der
      | T_Fun_b der' => S (size_typing_derivation der')
      | T_Fun_r _ der' => S (size_typing_derivation der')
      | T_App_b _ der₁ der₂ => 
          S ((size_typing_derivation der₁) + (size_many_typing_derivation der₂))
      | T_App_hd_r der' => S (size_typing_derivation der')
      end
  with 
    size_many_typing_derivation {b r : nat} {Γ : Ctx.t} {t : term} {M : multitype} (der : Γ |( b , r )- t ∈ₘ M) : nat :=
    match der with 
    | ManyT_Singleton der => size_typing_derivation der
    | ManyT_Cons _ der₁ der₂ => size_typing_derivation der₁ + size_many_typing_derivation der₂
    | ManyT_Inv _ _ der _ => size_many_typing_derivation der
    end
  .

  Definition is_tight_derivation 
    {n b r : nat} {Γ : Ctx.t} {t : term} {T : type} 
    (der : Γ |( b , r )- t ∈ T) : Set 
  := 
    and_set (is_tight_type T)  (is_tight_context Γ).
    
    Check has_type_mut_ind.

Ltac derivation_induction der P0 := 
  induction der using has_type_mut_ind with (P0:=P0); unfold P0 in *; clear P0.

Locate "{ _ } + { _ }".

Lemma permₘ_empty : ∀ mt, permutationₘ {{nil}} mt -> mt = {{nil}}.
Proof with eauto with permutation_hints.
  intros.
  remember {{nil}} as mt'.
  induction H; subst; try inversion Heqmt'...
  rewrite <- IHpermutationₘ1...
Qed.

Locate "∃".
Check ex.




Definition Id := <{ λ #0 }>.
Definition example_term := <{ (λ ((λ #0 #1) #0)) `Id` }>.
Goal example_term -->* Id.
Proof.
  unfold example_term.
  apply RC_self.
  eapply TC_trans.
  - eapply TC_self. apply ST_Beta.
  - simpl. eapply TC_trans.
    + eapply TC_self. eapply ST_Beta. 
    + simpl. eapply TC_self. eapply ST_Beta.
Qed. 

Definition abs_abs := {{ ` Ty_Tight TC_Abs ` ; nil }} |-> Ty_Tight TC_Abs.

Example first_derivation : [] |(3, 1)- example_term ∈ (Ty_Tight TC_Abs).
Proof with eauto.
  unfold example_term.
  change 3 with (2 + 1).
  change 1 with (0 + 1) at 3.
  apply @T_App_b with 
    (Γ₁ := []) 
    (Γ₂ :=[]) 
    (
    M := {{ 
        ` Ty_Tight TC_Abs ` ; 
        ` abs_abs ` ; 
          nil 
        }}
    ). 
  - apply Ctx.Union_Nil.
  - apply T_Fun_b.
    apply @T_App_b with 
      (Γ₁ := [{{ ` Ty_Tight TC_Abs ` ; nil }}]) 
      (Γ₂ := [{{ ` abs_abs ` ; nil }}]) 
      (b₁ := 1) 
      (b₂ := 0) 
      (r₁ := 0) 
      (r₂ := 0)
       (M := {{ abs_abs ; nil}})...
    + apply Ctx.Union_Cons.
      * apply Ctx.Union_Nil.
      * simpl.
        apply Multitype.eq_refl.
    + apply T_Fun_b.
      unfold abs_abs.
      apply @T_App_b with 
      (Γ₁ := [ {{ ` abs_abs ` ; nil }} ; {{nil}}])
      (Γ₂ := [ {{nil}}; {{ ` Ty_Tight TC_Abs ` ; nil }} ])
      (b₁ := 0) (b₂ := 0) (r₁ := 0) (r₂ := 0) (M := {{ ` Ty_Tight TC_Abs ` ; nil }}); unfold abs_abs...
      repeat apply Ctx.Union_Cons; simpl; try apply Multitype.eq_refl.
      apply Ctx.Union_Nil.
  - unfold Id.
    change 1 with (1 + 0) at 2.
    change 1 with (0 + 1) at 1.
    eapply ManyT_Cons; unfold abs_abs...
    + apply Ctx.Union_Nil.
    + eapply @T_Fun_r with (T := Ty_Tight TC_Abs) (A := Ty_Tight TC_Abs)...
Qed.


Lemma tigh_spreading_on_neutral_terms : 
  ∀ (t : term), neutral t ->
  ∀ (Γ : Ctx.t) (b r : nat)  (A : type)
  (φ : Γ |(b, r)- t ∈ A), (is_tight_context Γ) -> (is_tight_type A).
Proof with eauto.
  intros t H_neutral.
  induction H_neutral as [ x | p u H_neutral_p IH]; intros Γ b r A φ H_tight.
  - admit. 
  - inversion φ; subst...
    + admit.
    + apply Ctx_union_tight in H1 as [H_tight_Γ₁ H_tight_Γ₂]...
      apply IH in H5; simpl in H5; try contradiction...

Qed.

End HeadTypingSystem.