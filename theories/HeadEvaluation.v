From Coq Require Import Peano Nat Arith ZArith Lia Unicode.Utf8_core.
From TLC Require Import LibLN LibTactics LibFset.
From TTSB Require Import Tactics Classes.
From TTSB.Types Require Import Types Context.
From TTSB Require Import Syntax.
Import TypesNotations. 


Ltac auto_tilde :=
  try (solve[ auto with head_eval_hints
            | intuition auto with head_eval_hints
            | solve_set_equality ]).

Ltac auto_star ::= 
  try (solve [ eauto with head_eval_hints 
             | jauto 
             | intuition eauto with head_eval_hints
             | solve_set_equality ]).


Inductive neutral : term -> Prop :=
  | Neutral_BVar : ∀ (n : nat), neutral (TmBVar n)
  | Neutral_FVar : ∀ (x : var), neutral (TmFVar x)
  | Neutral_App : ∀ (t₁ t₂ : term), 
      neutral t₁ -> 
      neutral (TmApp t₁ t₂)  
.
Hint Constructors neutral : head_eval_hints.

Inductive normal : term -> Prop :=
  | Normal_Neutral : 
      ∀ (t : term), neutral t -> normal t
  | Normal_Abs :
      ∀ (t : term),
      (∀ (x : var), (x \notin fv t) -> normal (t ^ x)) -> 
      normal (TmAbs t)
.
Hint Constructors normal : head_eval_hints.

Inductive abs : term -> Prop :=
(* Voir si besoin LC *)
  | Abs : ∀ (t : term), abs (TmAbs t)
.
Hint Constructors abs : head_eval_hints.


Reserved Notation "t1 '-->' t2" (at level 50).
Inductive step : term -> term -> Prop :=
| ST_Beta : 
    ∀ (u q : term), 
    (TmApp (TmAbs u) q) --> (u ^^ q)
| ST_Abs : 
    ∀ (t p : term),
    t --> p ->
    TmAbs t --> TmAbs p
| ST_App : 
    ∀ (t p u : term), 
    (¬ abs t) -> 
    t --> p ->
    TmApp t u --> TmApp p u
where 
  "a --> b" := (step a b)
.
Hint Constructors step : head_eval_hints.

Ltac gather_vars := 
  let A := gather_vars_with (fun x : vars => x) in 
  let B := gather_vars_with (fun x : var => \{x}) in 
  let C := gather_vars_with (fun x : ctx => dom x) in 
  let D := gather_vars_with (fun x : term => fv x) in 
  constr:(A \u B \u C \u D).

Ltac pick_fresh x :=
  let L := gather_vars in pick_fresh_gen L x.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) := 
  apply_fresh_base T gather_vars x.


Definition deterministic {A : Type} (rel : A -> A -> Prop) :=
  ∀ a a₁ a₂, rel a a₁ -> rel a a₂ -> a₁ = a₂.  

Definition rel_normal {A : Type} (rel : A -> A -> Prop) (a : A) :=
  ¬ (∃ a', rel a a').

Theorem deterministic_step : deterministic step.
Proof.
  unfold deterministic.
  introv Hstep1 Hstep2.
  gen a₂.
  induction Hstep1; intros; inverts* Hstep2; 
  try solve [
    fequals*
  | false*
  ].
Qed.
Hint Resolve deterministic_step : head_eval_hints.


Reserved Notation "a -->* b" (at level 50).
Inductive multistep : term -> term -> Set := 
| MS_Self : ∀ t, t -->* t 
| MS_Trans : ∀ t₁ t₂ t₃, t₁ --> t₂ -> t₂ -->* t₃ -> t₁ -->* t₃
where "a -->* b" := (multistep a b)
.


Lemma neutral_is_normal_not_abs : 
  ∀ (t : term), 
  normal t -> (¬ abs t) -> 
  neutral t.
Proof.
  introv H_normal_t H_not_abs_t.
  inverts* H_normal_t.
  false*.
Qed.
Hint Resolve neutral_is_normal_not_abs : head_eval_hints.

Hint Extern 1 => match goal with 
  | [H : neutral (TmAbs _) |- _] => inverts* H
  | [H : abs (TmApp _ _) |- _] => inverts* H
  | [H : abs (TmBVar _) |- _] => inverts* H
  | [H : abs (TmFVar _) |- _] => inverts* H
  | [H : TmFVar _ --> _ |- _] => inverts* H
  | [H : TmBVar _ --> _ |- _] => inverts* H
end : head_eval_hints.

Lemma step_open : 
  ∀ t t' x, 
  t --> t' ->
  ∃ t'', t ^ x --> t''.
Proof.
  unfold "^".
  generalize 0.
  intros n t; inductions t gen n; introv Hstep; inverts* Hstep; simpls*;
  match goal with 
  | [ H : ?t --> _, IH : context[?t --> _]  |- _ ] => 
    eapply IH in H as [t'' Hst]
  end; eexists; unfold "^"; simpls*.
  applys* ST_App.
  destruct* t1; simpls; try case_if*.
  absurd.
Qed.

Lemma open_irrelevant :
  ∀ t t' x, 
  (t ^ x) --> (t') -> 
  ∃ t'', t --> t''.
Proof.
  unfold "^".
  generalize 0.
  intros n t.
  inductions t gen n; introv Hstep; simpls*; 
  repeat case_if; inverts Hstep.
  - edestruct IHt; autos*.
  - destruct* t1; simpls; try case_if*; inverts H0.
  - destruct* t1; simpls; repeat case_if*; substs*.
    edestruct IHt1; autos*.
Qed. 

Hint Resolve open_irrelevant : head_eval_hints.


Lemma rel_normal_is_normal : 
  ∀ t, lc t -> rel_normal step t -> normal t.
Proof.
  introv H_lc. 
  unfold rel_normal in *.
  inductions H_lc; intro H_rel_normal; autos*.
  + apply Normal_Abs.
    intros x Hnotin.
    applys* H0.
    intros [t' Hstep].
    lets t'' Hst : (open_irrelevant t t' x Hstep).
    autos*.
  + destruct* t1.
    * false*.
    * do 2 constructor.
      applys* neutral_is_normal_not_abs.
      applys* IHH_lc1.
      introv [a' Hstep].
      autos*.
Qed.

Hint Resolve rel_normal_is_normal : head_eval_hints.
Theorem head_red_eval_system :
        (deterministic step)
        /\  (∀ (t : term), lc t -> (rel_normal step t <-> normal t))
        /\ (∀ (t : term), lc t -> (neutral t <-> ((normal t) /\ (¬ abs t)))).
Proof.
  repeat split*.
  - introv Hnormal [t' Hstep].
    gen H t'.
    inductions Hnormal.
    + intro Hlc. inductions H; intros; inverts* Hstep.
      inverts* Hlc.
    + intros Hlc t' Hstep.
      inverts* Hstep.
      inverts* Hlc.
      pick_fresh x.
      apply step_open with t p x in H2 as [t''].
      applys* (H0 x).
  - induction* t.
Qed.

(* TODO: Passer en paramètres les variables interdites *)

Reserved Notation "[| V |] Γ '|(' b ',' r ')-' t '∈' T" (at level 70).
Reserved Notation "[| V |] Γ '|(' b ',' r ')-' t '∈ₘ' T" (at level 70).
Inductive has_type : vars -> ctx -> nat -> nat -> term -> type -> Type :=
| T_Ax :
    ∀ {V : vars} {x : var} {A : type} {Δ : ctx},
    equals Δ (add empty x {{ A ; nil }}) ->
    [|V|] Δ |(0, 0)- TmFVar x ∈ A
| T_Fun_b :
    ∀ 
      {V : vars} {Γ : ctx} 
      {t : term} 
      {M : multitype} {A : type} 
      {x : var} 
      {b r : nat},
    x \notin (V \u fv t \u dom Γ) ->
    ok Γ ->
    [|V \u \{x}|] add Γ x M |(b, r)- t ^ x ∈ A ->
    [|V|] Γ |(S b, r)- TmAbs t ∈ (M |-> A) 
| T_App_b :
    ∀ 
      {V₁ V₂ : vars}
      {Γ₁ Γ₂ Δ : ctx} {t p : term} 
      {M : multitype} {A : type}
      {b r b' r' : nat},
    ok Γ₁ -> ok Γ₂ ->
    equals (union Γ₁ Γ₂) Δ -> 
    [|V₁|] Γ₁ |(b, r)- t ∈ (M |-> A) ->
    [|V₂|] Γ₂ |(b', r')- p ∈ₘ M ->
    [|V₁ \u V₂|] Δ |(b + b', r + r')- (TmApp t p) ∈ A
| T_Fun_r :
    ∀ {V : vars}
      {Γ : ctx} {t : term} {x : var}
      {b r : nat} {A : type} {M : multitype},
    ok Γ ->
    x \notin (V \u fv t \u dom Γ) ->
    tight A -> 
    tight M -> 
    [|V \u \{x}|] add Γ x M |(b, r)- t ^ x ∈ A -> 
    [|V|] Γ |(b, S r)- TmAbs t ∈ Ty_Tight TC_Abs

| T_App_hd_r :
  ∀ {V : vars} {Γ : ctx} {t p : term} {b r : nat},
  [|V|] Γ |(b, r)- t ∈ Ty_Tight TC_Neutral -> 
  [|V|] Γ |(b, S r)- TmApp t p ∈ Ty_Tight TC_Neutral
where 
  "[| V |] Γ '|(' b ',' r ')-' t '∈' T" := (has_type V Γ b r t T)
with  has_many_types : vars -> ctx -> nat -> nat -> term -> multitype -> Type :=
  | ManyT_Empty :
      ∀ {V : vars} {t : term},
        [|V|] empty |(0, 0)- t ∈ₘ {{ nil }}
  | ManyT_Union :
        ∀ {V₁ V₂ : vars}
          {Γ₁ Γ₂ Δ: ctx} 
          {t : term} 
          {A : type} {mt : multitype} 
          {b₁ b₂ r₁ r₂ : nat},
        ok Γ₁ -> ok Γ₂ ->
        equals (union Γ₁ Γ₂) Δ ->
        [|V₁|] Γ₁ |(b₁, r₁)- t ∈ₘ mt ->
        [|V₂|] Γ₂ |(b₂, r₂)- t ∈ A ->
        [|V₁ \u V₂|] Δ |(b₁ + b₂, r₁ + r₂)- t ∈ₘ {{A; mt}}
  
where
  "[| V |] Γ '|(' b ',' r ')-' t '∈ₘ' T" := (has_many_types V Γ b r t T)
.
Hint Constructors has_many_types has_type : head_eval_hints.

Scheme has_type_mut_ind := Induction for has_type Sort Type
with has_many_types_mut_ind := Induction for has_many_types Sort Type.



Fixpoint size_typing_derivation {V : vars} {b r : nat} {Γ : ctx} {t : term} {T : type} (der : [|V|] Γ |( b , r )- t ∈ T) : nat :=
    match der with 
      | T_Ax _ => 0
      (* | T_Many_Inv der => size_many_typing_derivation der *)
      | T_Fun_b _ _ der' => S (size_typing_derivation der')
      | T_Fun_r _ _ _ _ der' => S (size_typing_derivation der')
      | T_App_b _ _ _ der₁ der₂ => 
          S ((size_typing_derivation der₁) + (size_many_typing_derivation der₂))
      | T_App_hd_r der' => S (size_typing_derivation der')
      (* | T_Many_Inv _ _ _ mder _ => 
        size_many_typing_derivation mder *)
      end
  with
    size_many_typing_derivation {V : vars} {b r : nat} {Γ : ctx} {t : term} {M : multitype} (der : [|V|] Γ |( b , r )- t ∈ₘ M) : nat :=
    match der with 
    | ManyT_Empty => 0
    | ManyT_Union _ _ _ der₁ der₂ => size_many_typing_derivation der₁ + size_typing_derivation der₂
    (* | ManyT_Inv _ _ _  mder der => size_many_typing_derivation mder +  size_typing_derivation der *)
    end
.

#[global] Instance Size_der : 
  ∀ {V : vars} {b r : nat} {Γ : ctx} {t : term} {T : type}, 
  Sized ([|V|] Γ |( b , r )- t ∈ T) :=
  fun {V : vars} {b r : nat} {Γ : ctx} {t : term} {T : type} =>
  {| size := size_typing_derivation |}
  .
#[global] Instance Size_mder : 
  ∀ {V : vars} {b r : nat} {Γ : ctx} {t : term} {M : multitype}, 
  Sized ([|V|] Γ |( b , r )- t ∈ₘ M) :=
  fun {V : vars} {b r : nat} {Γ : ctx} {t : term} {M : multitype} =>
  {| size := size_many_typing_derivation |}
  .

#[global] Instance Tightable_der : 
  ∀ {V : vars} {b r : nat} {Γ : ctx} {t : term} {T : type}, 
  Tightable ([|V|] Γ |( b , r )- t ∈ T) :=
    fun {V : vars} {b r : nat} {Γ : ctx} {t : term} {T : type} => 
    {| tight := fun _ => tight T /\ tight Γ |}.


(* Lemma ManyT_Inv :
      ∀ {V₁ V₂ : vars} {Γ₁ Γ₂ Δ : ctx} {t : term} {A : type} {mt : multitype} 
        {b₁ b₂ r₁ r₂ : nat},
        ok Γ₁ -> ok Γ₂ ->
        equals (union Γ₁ Γ₂) Δ ->
        [|V₁|] Δ  |(b₂, r₂)- t ∈ₘ {{A; mt}} ->
        [|V₂|] Γ₁ |(b₁, r₁)- t ∈ A ->
        ∃ Γ b r (φ : [|V₁ \u V₂|] Γ |(b, r)- t ∈ₘ mt), True.
        
Proof.
  introv Hok1 Hok2 Heq φ1 φ2.
  inverts* φ1.
  exists Γ₂.
  
Qed. *)

Lemma bvar_not_typable : 
  ∀ V Γ b r n A mt,
  [|V|] Γ |(b, r)- TmBVar n ∈ₘ {{A; mt}} -> False.
Proof.
  introv φ.
  inverts φ.
  inverts X0.
Qed.


Lemma typed_empty :
  ∀ V Γ b r t
  (φ : [|V|] Γ |(b, r)- t ∈ₘ {{nil}}),
  Γ = empty /\ b = 0 /\ r = 0 /\ size φ = 0.
Proof.
  introv.
  inversion φ; substs*; autos.
  inductions φ; autos.
Qed.


Lemma size_typed_var :
  ∀ V Γ b r x A
  (φ : [|V|] Γ |(b, r)- TmFVar x ∈ A),
  size φ = 0.
Proof.
  introv.
  inversion φ; substs*; autos.
  inductions φ; autos.
Qed.






Lemma typed_ok : ∀ V Γ b r t A, 
[|V|] Γ |(b, r)- t ∈ A -> ok Γ.
Proof.
  introv φ.
  induction φ; autos*; eauto with context_hints.
  eapply ok_eq.
  - use_equivalences. clear eq_ctx_refl; autos*.
  - apply ok_add, ok_empty. 
Qed.

Lemma multityped_ok : ∀ V Γ b r t M, 
[|V|] Γ |(b, r)- t ∈ₘ M -> ok Γ.
Proof.
  introv φ.
  induction φ; autos*; eauto with context_hints.
Qed.


Definition Id := TmAbs (TmBVar 0).
Definition example_term := 
  TmApp 
    (TmAbs (
      TmApp 
        (TmAbs (TmApp (TmBVar 0) (TmBVar 1))) 
        (TmBVar 0)
    )) 
    Id.

Example example_1_is_Id : example_term -->* Id.
Proof.
  unfold example_term.
  eapply MS_Trans; unfold "^^"; simpls; repeat case_if; autos*.
  eapply MS_Trans; unfold "^^"; simpls; repeat case_if; autos*.
  eapply MS_Trans; unfold "^^"; simpls; repeat case_if; unfold Id; autos*.
  unfold "^^". simpls; repeat case_if; unfold Id; autos*.
  apply MS_Self.
Qed.

Ltac replace_empty_union :=
  replace (\{}) with (@FsetImpl.union var \{} \{}); try solve[ simpl_unions; reflexivity].


Definition abs_abs := {{ ` Ty_Tight TC_Abs ` ; nil }} |-> Ty_Tight TC_Abs.
Example first_derivation : [|\{}|] empty |(3, 1)- example_term ∈ (Ty_Tight TC_Abs).
Proof with auto with context_hints.
  unfold example_term.
  replace_empty_union.
  apply @T_App_b with 
    (b := 2)
    (b' := 1)
    (r := 0)
    (r' := 1)
    (Γ₁ := empty) 
    (Γ₂ := empty) 
    (
    M := {{ 
        ` Ty_Tight TC_Abs ` ; 
        ` abs_abs ` ; 
          nil 
        }}
    )...
  { use_equivalences. rewrite* union_empty_l. }
  - pick_fresh x.
    replace_empty_union.
    
    apply @T_Fun_b with (x := x); simpls~.
    { intro. split; intros; false*; simpl_unions. }
    apply @T_App_b with 
      (Γ₁ := add empty x {{ ` Ty_Tight TC_Abs ` ; nil }}) 
      (Γ₂ := add empty x {{ ` abs_abs ` ; nil }}) 
      (b := 1) 
      (b' := 0) 
      (r := 0) 
      (r' := 0)
      (M := {{ abs_abs ; nil}}); repeat case_if; autos~...
    {
      use_equivalences.
      hint union_same.
      unfold equals, union, add, empty. repeat case_if. split_and_or_max; repeat simpl_unions; repeat intro; repeat case_if; autos*.
    }
    + pick_fresh x2.
      eapply @T_Fun_b with (x:=x2); simpls*...
      replace 0 with (0 + 0); autos*.
      { rewrite dom_add; simpls... absurd. }
      replace_empty_union.
      eapply @T_App_b with 
      (Γ₁ := add empty x2 {{ ` abs_abs ` ; nil }}  )
      (Γ₂ := add empty x  {{ ` Ty_Tight TC_Abs ` ; nil }})
      (b := 0) (b' := 0) (r := 0) (r' := 0) (M := {{ ` Ty_Tight TC_Abs ` ; nil }}); unfold abs_abs; repeat case_if;
      try (change 0 with (0 + 0); autos* )...
      { 
        hint LibFset.union_comm.
        use_equivalences; unfold equals, union, add, empty; repeat case_if; split_and_or_max; repeat simpl_unions; intros; repeat case_if; autos*.
      }
      { constructor. use_equivalences; autos. }
      replace \{ x2} with (\{} \u \{x2}); try solve [simpl_unions; autos].
      apply @ManyT_Union with (Γ₁ := empty) (Γ₂ := add empty x {{` (Ty_Tight TC_Abs) `; nil}}); autos*...
      { use_equivalences; rewrite* union_empty_l. }
      { constructor; use_equivalences; auto. }
    + replace 0 with (0 + 0); autos*. 
      replace \{ x} with (\{} \u \{x}); try solve [simpl_unions; autos].
      replace_empty_union.
      apply @ManyT_Union with (Γ₁ := empty) (Γ₂ := add empty x {{` abs_abs `; nil}}); autos*...
      { use_equivalences; rewrite* union_empty_l. }
      { constructor; use_equivalences; auto. }

  - unfold Id.
    change 1 with (1 + 0) at 1.
    change 1 with (0 + 1) at 2.
    replace_empty_union.
    apply @ManyT_Union with (A := Ty_Tight TC_Abs) (mt := {{ `abs_abs` ; nil }}) (Γ₁ := empty) (Γ₂ := empty); unfold abs_abs; pick_fresh x; autos...
      { use_equivalences; rewrite* union_empty_l. }
    + replace_empty_union.
      apply @ManyT_Union with 
      (Γ₁ := empty) (Γ₂ := empty) (b₁ := 0) (r₁ := 0); autos*...
      { use_equivalences; rewrite* union_empty_l. }
      eapply @T_Fun_b with (x := x); autos*... 
      unfold "^"; simpls. case_if*.
      constructor; use_equivalences; auto.

    + replace_empty_union.
      apply @T_Fun_r 
      with (M := {{`Ty_Tight TC_Abs`; nil}}) (A := Ty_Tight TC_Abs) (x := x); unfold "^"; simpls; repeat case_if; autos*...
      { constructor; use_equivalences; auto. }
Qed.

Ltac derivation_induction der P0 := 
  induction der using has_type_mut_ind with (P0:=P0); unfold P0 in *; clear P0.


Goal ∀ {V : vars} {Γ: ctx} {t : term} {A : type} {b r : nat} (φ : [|V|] Γ |(b, r)- t ∈ A),
b + r <= size_typing_derivation φ.
Proof.
  intros.
  pose (P0 (V : vars) (Γ: ctx) (b r : nat) (t : term) (M : multitype) (φ : [|V|] Γ |(b, r)- t ∈ₘ M) := b + r <= size_many_typing_derivation φ).
  derivation_induction φ P0; simpl; lia.
Qed.

Definition last_rule_is_appb 
    {V : vars} {b r : nat} {Γ : ctx} {t : term} {T : type} 
    (der : [|V|] Γ |( b , r )- t ∈ T) : Prop := 
  match der with 
  | T_Ax _ => False
  | T_Fun_b _ _ _ => False
  | T_Fun_r _ _ _ _ _ => False
  | T_App_b _ _ _ _ _ => True
  | T_App_hd_r _ => False
  (* | T_Many_Inv _  _ _ _ _ => False *)
  end.


Lemma tight_spreading_var :  
  ∀ {V : vars} {Γ : ctx} {b r : nat} {x : var} {A : type}
    (φ : [|V|] Γ |( b, r )- TmFVar x ∈ A), 
  tight Γ -> 
  tight A /\ ¬ last_rule_is_appb φ.
Proof with eauto.
  intros * H_tight.
  split.
  + inversion φ; subst.
    unfold tight, add, empty in H_tight; repeat case_if*.
    simpls.
    destruct Γ.
    specialize H_tight with x; repeat case_if*;
    simpls*.
    unfolds empty, add.
    case_if.
    reduce_max.
    specialize H1 with x.
    case_if.
    apply eq_tight_multitype in H1; simpls*.
  + intros * H_contra.
    remember (TmFVar x) as t.
    destruct φ eqn:H_eq...
    inversion Heqt. 
Qed.

Lemma tigh_spreading_on_neutral_terms : 
  ∀ {t : term}, neutral t ->
  ∀ {V : vars} {Γ : ctx} {b r : nat} {A : type}
    (φ : [|V|] Γ |(b, r)- t ∈ A), 
  tight Γ ->
  tight A /\ ¬ last_rule_is_appb φ.
Proof.
  intros t H_neutral.
  induction H_neutral as [ n | x | p u H_neutral_p IH]; introv H_tight.
  - inversion φ. 
  - applys* (tight_spreading_var 
              (V := V) (Γ := Γ) 
              (b := b) (r := r) 
              (x := x) (A := A)).
  - inversion φ; substs*.
    + tight_union_ctx Γ.
      apply IH in X; simpls*.
    + splits; simpls*...
      remember (TmApp p u) as t.
      remember (Ty_Tight TC_Neutral) as T.
      destruct φ eqn:Heq; simpl; inversion Heqt; subst...
      tight_union_ctx Δ.
      apply IH with (φ := h) in H_tight_Γ₁ as [H_contra _]; simpls*; contradiction. absurd.
Qed.

Fixpoint size_aux_term t :=
  match t with 
  | TmBVar _ | TmFVar _ => 0
  | TmAbs t' => S (size_aux_term t')
  | TmApp t₁ t₂ => S (size_aux_term t₁)
  end.

#[global] Instance Sized_term : Sized term := {| size := size_aux_term |}.


Ltac neutral_to_normal t := 
  match goal with 
  | [H : neutral t |- _] => let H_normal := fresh "H_normal" in apply Normal_Neutral in H 
  end.   

Lemma size_open :
  ∀ t x, 
  size t = size (t ^ x).
Proof.
  intro t.
  unfold "^".
  generalize 0.
  inductions t; intros; simpls; repeat case_if; autos*.
Qed.

Lemma normal_size_derivation : 
  ∀ {t : term} {V : vars} {Γ : ctx} {b r : nat} {A : type} 
    (φ : [|V|] Γ |(b, r)- t ∈ A), 
  normal t -> 
  size t <= size_typing_derivation φ.
Proof with simpls*; try lia.
  intros * H_normal_t.
  induction φ; inversion H_normal_t; subst; simpl; try apply IHφ in H0...
  - inverts* H_normal_t; substs*. rewrite size_open with ( x:= x). 
    specialize H1 with x. apply IHφ in H1...
  - inverts* H; neutral_to_normal t; apply IHφ in H1...
  - inverts* H_normal_t; substs*. rewrite size_open with ( x:= x).
    specialize H1 with x. apply IHφ in H1...
  - inverts* H; neutral_to_normal t; apply IHφ in H1...
Qed.

Ltac use_type_spreading Γ :=
  match goal with 
  | [ H : [|_|] Γ |(_, _)- _ ∈ {{ {{_}} |-> _}} |- _] => 
      apply tigh_spreading_on_neutral_terms in H; eauto; subst; inversion H
  end. 

Section term_size_ind.
  Inductive le_type : nat -> nat -> Type :=
  | O_le_n : ∀ n, le_type 0 n
  | Sn_le_Sm : ∀ n m, le_type n m -> le_type (S n) (S m)
  .

  Lemma le_refl :
    ∀ a, le_type a a.
  Proof.
    hint O_le_n, Sn_le_Sm.
    intro.
    induction* a.
  Qed.

  Lemma le_trans : 
    ∀ a b c, le_type a b -> le_type b c -> le_type a c.
  Proof with autos*.
    hint O_le_n, Sn_le_Sm.
    intro a.
    inductions a;
    introv Hlt_a_b Hlt_b_c;
    inverts Hlt_a_b;
    inverts* Hlt_b_c.
  Qed.

  Lemma le_S : 
    ∀ a, le_type a (S a).
  Proof.
    hint O_le_n, Sn_le_Sm.
    intro.
    induction* a.
  Qed.
  (* Inductive or_type A B : Type :=
  | ort_intro_l : A -> or_type A B
  | ort_intro_r : B -> or_type A B
  . *)

  Definition lt_type n m := le_type (S n) m.

  Variable P : term -> Type.

  Definition max (a b : nat) :=
    if leb a b then b else a.

  Lemma max_comm : 
    ∀ a b, max a b = max b a.
  Proof.
    intros.
    induction a; unfold max; destruct b; simpls*.
    destruct (a <=? b) eqn:Heqaleb; destruct (b <=? a) eqn:Hblea;
    autos.
    - apply leb_complete in Heqaleb, Hblea. lia.
    - apply leb_complete_conv in Heqaleb, Hblea. lia.
  Qed.

  Lemma le_max_self :
    ∀ a b, le_type a (max a b).
  Proof.
    hint le_refl, O_le_n, Sn_le_Sm.
    induction a; intros; unfolds max; destruct b; simpls*; case_if; substs*.
    specialize IHa with b. rewrite* C in IHa.
  Qed.

  Fixpoint size_for_ind (t : term) :=
    match t with 
    | TmBVar _ => 0
    | TmFVar _ => 0
    | TmAbs t => S (size_for_ind t)
    | TmApp t1 t2 => 1 + max (size_for_ind t1) (size_for_ind t2)
    end.

  Lemma size_for_ind_open : 
    ∀ t x, 
    size_for_ind t = size_for_ind (t ^ x).
  Proof.
    unfold "^"; generalize 0.
    intros n t; gen n.
    induction* t; intros; repeat (case_if || simpls || substs); autos.
  Qed.

  Hypothesis H : forall t, (forall t', lt_type (size_for_ind t') (size_for_ind t) -> P t') -> P t.


  Theorem term_size_ind : forall xs, P xs.
  Proof.
    asserts H_ind : (
      ∀ t t', 
          (le_type (size_for_ind t') (size_for_ind t)) -> P t'
    ).
    
      
    {
      hint le_trans.
      intro t; inductions t; intros t' Hlen; apply H; intros l0 H0; simpls;
      inverts Hlen;
      match goal with 
      | [ H : _ = size_for_ind _ |- _] => 
          rewrite <- H in *; clear H
      end; inverts* H0.
      unfolds max; case_if.
      - apply IHt2.
        apply le_trans with n.
        + assumption.
        + assumption.
      - apply IHt1.
        apply le_trans with n.
        + assumption.
        + assumption.
    }
    intros t.
    apply H_ind with (t := t).
    apply le_refl.
  Qed.
End term_size_ind.

Theorem normal_tight_der_size_b_r :
  ∀ {t : term} {V : vars} {Γ : ctx} {b r : nat} {A : type} 
    (φ : [|V|] Γ |(b, r)- t ∈ A), 
  normal t -> 
  tight φ -> 
  b = 0 /\ r = size t.
Proof with try lia; eauto using union_tight_ctx.
  asserts size_eq : (size = size_aux_term)...
  induction t using term_size_ind.
  gen H.
  induction t; intros H_ind_size * H_normal_t H_tight_der; destruct H_tight_der as [H_tight_A H_tight_Γ]; inversion φ; subst; simpl; try (inversion H_tight_A; fail)...
  - inversion H_normal_t; subst; try inversion H.
    asserts H_size : (lt_type (size_for_ind (t ^ x)) (size_for_ind (TmAbs t))). 
    { unfold lt_type. hint le_refl. rewrite* <- size_for_ind_open. }
    specialize H3 with x.
    asserts Hfree : (x \notin fv t). { reduce_max. auto. }
    destruct* (H_ind_size _ H_size _ _ _ _ _ X (H3 Hfree)).
    { split*. destruct Γ. unfold add. simpls*. case_if. simpls*. intro. specialize H_tight_Γ with x0. case_if*. apply* mt_tight_union. }
    split*.
    change size_aux_term with size.
    rewrite* (size_open t x).
  - asserts H_tight_Γ₁ H_tight_Γ₂ : (tight Γ₁ /\ tight Γ₂)...
    inversion H_normal_t. inversion H; subst.
    use_type_spreading Γ₁.
  - inversion H_normal_t; inversion H; subst.
    assert (b = 0 ∧ r0 = size t1).
    {
      eapply H_ind_size with (φ := X); autos*.
      - unfold lt_type. hint le_refl. simpls*.
        constructor.
        apply le_max_self.
      - unfold tight. split...
    }
    change size_aux_term with size.
    lia.
Qed.  


Theorem normal_neutral_type_is_neutral : 
  ∀ {t : term} {V : vars} {Γ : ctx} {b r : nat} 
    (φ : [|V|] Γ |(b, r)- t ∈ Ty_Tight TC_Neutral), 
  normal t -> 
  neutral t.
Proof with eauto.
  induction t; intros * φ H_normal_t; inversion H_normal_t; inversion φ...
Qed.


Lemma free_subst_neq : 
  ∀ t p x y,
  y ≠ x ->
  y \in fv t ->
  y \in fv ([x ~> p]t).
Proof.
  intro t.
  induction* t; introv Hneq Hin; simpls; repeat case_if; reduce_max; substs*.
  simpls. reduce_max. reflexivity.
Qed.
 
Lemma var_subst :
  ∀ t p x, 
  fv ([x ~> p] t) \c fv p \u fv t.
Proof.
  intro.
  induction* t; introv; simpls; repeat case_if; reduce_max; substs*; simpls; reduce_max; autos*.
  - apply subset_empty_l.
  - apply subset_union_weak_l.
  - apply subset_union_weak_r.
  - intros y Hin. reduce_max.
    + unfold subset in IHt1. specialize IHt1 with p x y.
      apply IHt1 in Hin; reduce_max; autos.
    + unfold subset in IHt2. specialize IHt2 with p x y.
      apply IHt2 in Hin; reduce_max; autos.
Qed.

Lemma fv_open : 
  ∀ t p n, fv ({ n ~> p} t) \c fv t \u fv p.
Proof.
  intros t p.
  induction t; intro k; intros y Hin; simpls; reduce_max;
  unfold subset in *; simpls; autos*.
  - case_if; simpls; reduce_max; autos.
  - apply IHt in Hin; reduce_max; autos.
  - apply IHt1 in Hin; reduce_max; autos.
  - apply IHt2 in Hin; reduce_max; autos.
Qed.

Lemma fv_substs :
  ∀ t p y, 
  fv ([y ~> p] t) \c (fv t \- \{y}) \u fv p.
Proof.
  intros t p y x Hin.
  inductions t; simpls; reduce_max; repeat case_if; simpls; reduce_max; substs*.
  - apply IHt in Hin; reduce_max; autos*.
  - apply IHt1 in Hin; reduce_max; autos*.
  - apply IHt2 in Hin; reduce_max; autos*.
Qed.

Inductive or_type A B : Type :=
| ort_intro_l : A -> or_type A B
| ort_intro_r : B -> or_type A B
.

Lemma open_notin_eq : 
  ∀ x t₁ t₂,
  x \notin fv t₁ ->
  x \notin fv t₂ ->
  t₁ ^ x = t₂ ^ x -> 
  t₁ = t₂.
Proof.
  unfold "^"; generalize 0;
  introv Hnin1 Hnin2 Heq.
  gen n.
  inductions t₁; destruct t₂; intros; repeat (simpls || case_if); substs*; 
  try solve [inversion Heq; substs; reduce_max; false].
  - inversion Heq. fequals. apply* IHt₁.
  - inversion Heq. fequals.
    + apply* IHt₁1.
    + apply* IHt₁2.
Qed.

Fixpoint is_free_BVar (n : nat) (t : term) :=
  match t with
  | TmBVar k => n = k
  | TmFVar _ => False 
  | TmAbs t' => is_free_BVar (S n) t'
  | TmApp t1 t2 => is_free_BVar n t1 \/ is_free_BVar n t2 
  end.

Lemma free_bvar_neq : 
  ∀ t n k x, 
  k ≠ n ->
  is_free_BVar (n) t -> 
  is_free_BVar (n) ({k ~> TmFVar x} t).
Proof.
  intros t.
  induction t; introv Hneq Hfree; repeat (simpls || case_if); autos*.
Qed.
Lemma lc_no_free_bvar :
  ∀ t,
  lc t -> 
  ∀ n, ¬ is_free_BVar n t.
Proof.
  intro t.
  induction t using term_size_ind; destruct t; intros Hlc k Hfree; simpls*.
  - inversion Hlc.
  - inverts Hlc.
    pick_fresh x.
    apply H with (t' := t ^ x) (n := S k).
    + rewrite <- size_for_ind_open; simpls; constructor; apply le_refl.
    + apply* H1.
    + unfold "^". apply* free_bvar_neq.
  - reduce_max; inverts Hlc.
    + eapply H with (t' := t1) (n:=k); try assumption.
      constructor. apply le_max_self.
    + eapply H with (t' := t2) (n:=k); try assumption.
      constructor. rewrite max_comm. apply le_max_self.
Qed.

Lemma free_Bvar_open :
  ∀ t p n, 
  ¬ is_free_BVar n t ->
  {n ~> p} t = t.
Proof.
  induction t; introv Hnfree; repeat (simpls || case_if); autos*.
  - fequals*.
  - fequals*.
Qed.

Lemma lc_open_substs : 
  ∀ t p x y, lc p -> x ≠ y -> ([y ~> p]t) ^ x = [y ~> p](t ^ x).
Proof.
  unfold "^"; generalize 0.
  introv Hlc Hneq. gen n.
  inductions t; intros; repeat (case_if || reduce_max || simpls || substs); autos*.
  - apply free_Bvar_open.
    apply* lc_no_free_bvar.
  - fequals.
    apply* IHt.
  - fequals. 
    + rewrite* IHt1.
    + rewrite* IHt2.
Qed.

Lemma num_eq_typed :
  ∀ Γ V b b' r r' p A (φ : [|V|] Γ |(b, r)- p ∈ A),
  b = b' ->
  r = r' ->
  ∃ φ' : [|V|] Γ |(b', r')- p ∈ A, size φ = size φ'.
Proof.
  introv Heqb Heqr.
  gen b' r'.
  inductions φ; intros; substs; exists*.
Qed.

Lemma num_eq_multityped :
  ∀ Γ V b b' r r' p M (φ : [|V|] Γ |(b, r)- p ∈ₘ M),
  b = b' ->
  r = r' ->
  ∃ φ' : [|V|] Γ |(b', r')- p ∈ₘ M, size φ = size φ'.
Proof.
  introv Heqb Heqr.
  gen b' r'.
  inductions φ; intros; substs; exists*.
Qed.

Lemma vars_eq_typed : 
  ∀ Γ V V' b r p A (φ : [|V|] Γ |(b, r)- p ∈ A),
  V = V' ->
  ∃ φ' : [|V'|] Γ |(b, r)- p ∈ A, size φ = size φ'.
Proof.
  introv Heq.
  gen V'.
  inductions φ; intros.
  - unshelve exists.
    + apply T_Ax. assumption.
    + simpls~.  
  - destruct (IHφ (V' \u \{x})) as [φ' Hsizeφ']; substs*.
  - destruct (IHφ V₁) as [φ' Hsizeφ']; substs*.
  - destruct (IHφ (V' \u \{x})) as [φ' Hsizeφ']; substs*.
  - destruct (IHφ V) as [φ' Hsizeφ']; substs*.
Qed.
  
Lemma vars_eq_multityped : 
  ∀ Γ V V' b r p M (φ : [|V|] Γ |(b, r)- p ∈ₘ M),
  V = V' ->
  ∃ φ' : [|V'|] Γ |(b, r)- p ∈ₘ M, size φ = size φ'.
Proof.
  introv Heq.
  gen V'.
  inductions φ; intros.
  - unshelve exists; autos*. 
  - destruct (IHφ V₁) as [φ' Hsizeφ']; substs*.
Qed.  

Lemma ctx_eq_typed :
  ∀ Γ Δ V b r p A (φ : [|V|] Γ |(b, r)- p ∈ A),
  equals Γ Δ ->
  ∃ φ' : [|V|] Δ |(b, r)- p ∈ A, size φ = size φ'.
Proof.
  introv Heq.
  gen Δ.
  inductions φ; intros.
  - asserts: (equals Δ0 (add empty x {{` A `; nil}})).
    { use_equivalences; autos*. }
    unshelve exists.
    + apply T_Ax; assumption.
    + simpls*. 
  - destruct IHφ with (Δ := add Δ x M).
    { hint equals_add; use_equivalences; autos*. }
    asserts: (x \notin V \u fv t \u dom Δ).
    { rewrite <- dom_equal with (Γ₁ := Γ); reduce_max; use_equivalences; autos*. }
    asserts: (ok Δ).
    { hint ok_eq; autos*. }
    unshelve exists.
    + apply @T_Fun_b with (x := x); assumption.
    + simpls*.
  - asserts : (equals (Γ₁) ⊎c (Γ₂) Δ0).
    { use_equivalences; autos*. }
    destruct IHφ with (Δ := Γ₁).
    { use_equivalences; autos*. }
    unshelve exists.
    + apply @T_App_b with (M := M) (Γ₁ := Γ₁) (Γ₂ := Γ₂); assumption.
    + simpls*.
  - asserts: (ok Δ). { hint ok_eq; autos*. }
    asserts: (x \notin V \u fv t \u dom Δ). { 
      rewrite <- dom_equal with (Γ₁ := Γ); reduce_max; autos. 
    }
    destruct IHφ with (Δ := add Δ x M).
    { use_equivalences; apply* equals_add.  }
    unshelve exists.
    + apply @T_Fun_r with (x := x) (M := M) (A := A); assumption.
    + simpls*.
  - destruct IHφ with (Δ := Δ). { use_equivalences; autos*. }
    unshelve exists.
    + apply* @T_App_hd_r.
    + simpls*.  
Qed.

Lemma ctx_eq_multityped :
  ∀ Γ Δ V b r p M (φ : [|V|] Γ |(b, r)- p ∈ₘ M),
  equals Γ Δ ->
  ∃ φ' : [|V|] Δ |(b, r)- p ∈ₘ M, size φ' = size φ.
Proof.
  introv Heq.
  gen Δ.
  inductions φ; intros.
  - use_equivalences. apply eq_ctx_sym in Heq. rewrite equals_empty_is_empty in Heq; substs*.
  - asserts : (equals (Γ₁) ⊎c (Γ₂) Δ0).
    { use_equivalences; autos*. }
    unshelve exists.
    + apply @ManyT_Union with (Γ₁ := Γ₁) (Γ₂ := Γ₂); assumption.
    + simpls*. 
Qed.


Lemma type_eq_typed : ∀ V Γ b r p t1 t2 (φ : [|V|] Γ |(b, r)- p ∈ t1 ),
  eq_type t1 t2 -> 
  ∃ (φ' : [|V|] Γ |(b, r)- p ∈ t2), size φ = size φ'.
Proof.
  introv Heq.
  gen t2.
  inductions φ; introv Heq.
  - asserts HeqΔ : (equals Δ (add empty x {{t2 ; nil}})). {
        use_equivalences; hint equals_add, Eq_MT_Cons; autos*.
      }
    unshelve exists.
    + apply T_Ax; assumption.
    + simpls*.
  - inverts Heq.
    destruct* (IHφ t₂) as [φIH].
    asserts Heq: (equals (add Γ x M) (add Γ x mt₂)).
    { use_equivalences; apply* equals_add. }
    lets φf Hsizeφf : (ctx_eq_typed _ (add Γ x mt₂) _ _ _ _ _ φIH Heq). 
    unshelve exists.
    + apply @T_Fun_b with (x := x); try assumption.
    + simpls. fequals. 
  - destruct (IHφ ({{ {{M}} |-> t2}})).
    { constructor; use_equivalences; autos*. }
    unshelve exists.
    + apply @T_App_b with (M := M) (Γ₁ := Γ₁) (Γ₂ := Γ₂); assumption.
    + simpls*.  
  - inverts Heq.
    destruct (IHφ A).
    { use_equivalences; autos*. }
    unshelve exists.
    + apply @T_Fun_r with (M := M) (A := A) (x := x); assumption.
    + simpls*.
  - inverts Heq.
    destruct (IHφ (Ty_Tight TC_Neutral)).
    { use_equivalences; autos. }
    unshelve exists.
    + apply @T_App_hd_r; assumption.
    + simpls*.
Qed.

Lemma multitype_eq_typed :
  ∀ V Γ b r t mt1 mt2 (φ : [|V|] Γ |(b, r)- t ∈ₘ mt1), 
  eq_multitype mt1 mt2 -> 
  ∃ (φ' : [|V|] Γ |(b, r)- t ∈ₘ mt2), size φ = size φ'.
Proof.
  introv Heqmt.
  gen V Γ b r t φ.
  inductions Heqmt; introv.
  - inversion φ;
    destruct φ eqn:Heq.
    + unshelve exists.
      * apply ManyT_Empty.
      * reflexivity.
    + substs*.
  
  - remember ({{` t₁ `; ` mt₁ `}}) as t_temp. 
    destruct φ eqn:Heq; inverts Heqt_temp.
    destruct IHHeqmt with (φ := h).
    lets φf Hsizeφf : (type_eq_typed _ _ _ _ _ _ _ h0 H).
    unshelve exists.
    + apply @ManyT_Union with (Γ₁ := Γ₁) (Γ₂ := Γ₂); assumption.
    + simpls*.
  - remember ({{` t₁ `; ` t₂ `; ` mt `}}) as t_temp. 
    destruct φ eqn:Heqφ; inverts Heqt_temp.
    remember {{` t₂ `; ` mt `}} as t_temp.
    destruct h eqn:Heqh; inverts Heqt_temp.
    asserts φf Hsizeφf: (∃ φ' : [|(V₁ \u V₂) \u V₂0|] Δ |( b₁ + b₂ + b₂0, r₁ + r₂ + r₂0  )- t ∈ₘ {{` t₂ `; ` t₁ `; ` mt `}}, size φ' = size φ). { 
      asserts: (ok (Γ₁) ⊎c (Γ₂)). { hint ok_union; autos. }
      asserts: (equals (union (Γ₁) ⊎c (Γ₂) Γ₂0) Δ). {
        use_equivalences.
          hint union_perm.
          apply eq_ctx_trans with ((Δ0) ⊎c (Γ₂)). 
          2: { autos*. }
          apply eq_ctx_trans with ((Γ₁ ⊎c Γ₂0) ⊎c Γ₂).
          2 : { 
            apply ok_get_equals; try solve[hint ok_union, ok_eq; autos*].
            intro x.
            repeat rewrite get_union.
            apply union_perm_head.
            rewrite <- get_union.
            gen x.
            hint ok_union, ok_eq;
            rewrite* <- ok_get_equals.
          }
          hint union_assoc.
          apply eq_ctx_trans with (Γ₁ ⊎c (Γ₂ ⊎c Γ₂0)); autos.
          apply eq_ctx_trans with (Γ₁ ⊎c (Γ₂0 ⊎c Γ₂)); autos. 
          apply ok_get_equals; try solve[hint ok_union, ok_eq; autos*].
          intro x.
          repeat rewrite get_union.
          hint union_perm_tail, Types.union_comm.
          autos*.
      }
      asserts: (equals (Γ₁) ⊎c (Γ₂) (Γ₁) ⊎c (Γ₂)). { use_equivalences; autos. }
      unshelve exists.
      - apply @ManyT_Union with (Γ₁ := Γ₁ ⊎c Γ₂) (Γ₂ := Γ₂0); try assumption.
        apply @ManyT_Union with (Γ₁ := Γ₁) (Γ₂ := Γ₂); try assumption.
      - substs. simpls. lia.
    }
    asserts φf' Hsizeφf' : (∃ φf' : [|(V₁ \u V₂0) \u V₂|] Δ |( b₁ + b₂ + b₂0, r₁ + r₂ + r₂0 )- t ∈ₘ {{` t₂ `; ` t₁ `; ` mt `}}, size φf = size φf').
    { apply vars_eq_multityped with (φ := φf). solve_set_equality. }
    rewrite Heqφ in Hsizeφf.
    rewrite Hsizeφf in Hsizeφf'.
    rewrite Hsizeφf'.
    apply num_eq_multityped; lia.
  - destruct IHHeqmt1 with (φ := φ) as [φ' ->].
    apply IHHeqmt2.
Qed.


(* Lemma substitution_typing :
  ∀ (V₁ V₂ : vars)
    (Γ₁ Γ₂ Γ₂' Δ : ctx) (y : var) (M : multitype) 
    (t p : term) (A : type)
    (b b' r r' : nat)
    
    (φₜ : [|V₁ \u \{y}|] Γ₂' |(b, r)- t ∈ A)
    (φₚ : [|V₁ |] Γ₁ |(b', r')- p ∈ₘ M),
    ok Γ₁ -> ok Γ₂ -> lc p ->
    (V₂ \u dom Γ₁ \u dom Γ₂ \u fv p) \c V₁ ->
    (* (V₂ \u dom Γ₁ \u dom Γ₂ \u fv t \u fv p) \c V₁ -> *)
    y \notin V₁ ->
    equals (add Γ₂ y M) Γ₂' -> 
    equals Γ₂ ⊎c Γ₁ Δ ->
    ∃ (φ : [|V₁ \u \{y}|] Δ |(b + b', r + r')- [y ~> p] t ∈ A), 
    (* True *)
    size φ = size φₜ + size φₚ - size M
    .
Proof.
  (* introv φₜ.
  remember (V₁ \u \{ y}) as V.
  gen b' r' Γ₁ Γ₂ Δ M p V₁ V₂ y.
  induction φₜ eqn:Heqφₜ; simpls. introv Heq φₚ HokΓ₁ HokΓ₂ Hlcp Hsub Hnotin HeqΓ₂ HeqΔ;
  rewrite Heq in *; clear Heq.
  (* inductions φₜ; simpls; introv φₚ HokΓ₁ HokΓ₂ Hlcp Hsub Hfree HeqΓ₂ HeqΔ. *)
  - case_if.
    + asserts [HM_Anil | HM_nil] : ((eq_multitype M {{A ; nil}}) \/ (M = {{nil}})).
      { substs.
        asserts Heq_get : 
          (∀ z, eq_multitype (get (add Γ₂ x M) z) (get (add empty x {{` A `; nil}}) z)).
        { 
          asserts Heq_get1 : 
            (∀ z : var, eq_multitype (get (add Γ₂ x M) z) (get Δ z));
          asserts Heq_get2 : 
            (∀ z : var, eq_multitype (get Δ z) (get (add empty x {{` A `; nil}}) z));
            try solve[apply ok_get_equals; hint ok_union, ok_add, ok_eq; autos; apply* ok_eq].
          use_equivalences; autos*. 
        }
        specialize Heq_get with x.
        repeat rewrite get_add_eq in Heq_get. rewrite get_empty in Heq_get; simpls.
        destruct M; simpls*.
        destruct (Types.union M (get Γ₂ x)) eqn:HeqU; simpls*.
        + destruct* M; solve[inversion HeqU]. 
        + apply eq_size in Heq_get. simpls; lia. 
      }
      * lets Hφ _ : (multitype_eq_typed _ _ _ _ _  _ _ HM_Anil φₚ).
        inverts Hφ.
        lets h : (typed_empty _ _ _ _ _ X); reduce_max; substs.
        exists*.
        apply ctx_eq_typed with (Γ := Γ₂0); autos.
        asserts H_empty_Γ₂ : (Γ₂ = empty).
        {
          repeat match goal with
          | [H : _ \c _ |- _] => clear H 
          | [H : _ \notin _ |- _] => clear H 
          | [H : [|_|] _ |(_, _)- _ ∈ _ |- _] => clear H 
          | [H : [| _ |] _ |( _ , _ )- _ ∈ₘ _ |- _] => clear H 
          | [H : vars |- _] => clear H 
          | [H : nat |- _] => clear H 
          end.
          clear h4 X H8 H7 H1 HeqΔ Hlcp HokΓ₁ V₁0 p.
          apply equals_empty_is_empty.
          apply ok_get_equals; 
          destruct (ok_get_equals (add Γ₂ x M) Δ); try solve[use_equivalences; hint ok_eq, ok_empty, ok_add; autos*].
          intro z.
          apply H with (x := z) in HeqΓ₂.
          simpls.
          destruct Γ₂, Δ.
          unfolds get, add; repeat case_if; unfolds empty; simpls; reduce_max.
          - substs; hint eq_empty_is_empty; use_equivalences; false*.
          - specialize e1 with z; case_if. 
            asserts Heq_contra : (eq_multitype (Types.union (m z) M) M). {
              use_equivalences; hint Types.union_comm; autos*.
            }
            destruct (m z). try solve[use_equivalences; autos].
            apply eq_size in Heq_contra; simpls. rewrite size_union in Heq_contra.
            simpls; lia.
          - specialize e1 with z; use_equivalences; case_if*. 
        }
        substs. rewrites union_empty_l in *. use_equivalences; autos*.
        admit.
      * substs. 
      asserts Hcontra: (eq_multitype M {{A; nil}} ).  admit.
        
    + asserts HMnil :  (M = {{nil}}). {
        clear  HeqΔ Hlcp Hnotin Hsub φₚ p V₂ V₁ b' r' Δ0.
        substs. 
        hint (ok_get_equals Δ (add empty x {{` A `; nil}})), ok_add, ok_union, ok_eq. 
        destruct* Hint as [Heq_get _].
        eapply Heq_get with (x := y) in e.
        unfolds get, add, empty; destruct Δ as [sΔ fΔ]; destruct Γ₂ as [sΓ₂ fΓ₂].
        repeat case_if*.
        unfolds equals; reduce_max.
        specialize HeqΓ₂1 with y; case_if.
        apply eq_empty_is_empty in e.
        clear Heq_get Hint1 Hint2 Hint0. rewrite e in HeqΓ₂1.
        apply eq_empty_is_empty in HeqΓ₂1.
        destruct* M.
        simpls. inversion HeqΓ₂1.
      }
      asserts φ : ([|V₁ \u \{ y}|] Δ0 |( b', r' )- TmFVar x ∈ A). {
        substs.
        inverts φₚ. rewrite union_empty_r in HeqΔ.
        replace (add Γ₂ y {{nil}}) with Γ₂ in * by (unfold add; case_if* ).
        constructor;
        use_equivalences;
        autos*.
      }
      eexists.
      exists*. intros z Hinz; autos.
  - asserts IHφ IH: (
    (* (V₁ \u \{ x}) \u \{y} *)
      ∃ (φ : [|V₁ \u \{ x} \u \{y}|] add Δ x M |( b + b', r + r' )- [y ~> p] t ^ x ∈ A), True
    ). {
      exists*.
      eapply IHφₜ with (Γ₁ := Γ₁) (Γ₂ := add Γ₂ x M) (M := M0) (V₁ := (V₁ \u \{x})) (V₂ := V₂); reduce_max; autos*.
      - hint ok_add; autos.
      - destruct M; try rewrite add_nil; try rewrite dom_add; try absurd; 
        intros z Hinz; reduce_max; try apply fv_open in Hinz; autos*.
      - rewrite ok_get_equals; try solve[hint ok_add; autos].
        intros z. 
        destruct Γ₁, Γ₂, Γ, Δ. unfolds get, add; repeat (case_if || simpls || reduce_max || substs); hint union_perm_tail; autos*;
        try solve[
          match goal with 
          | [ |- context[m1 ?x]] => specialize HeqΓ₂1 with x; case_if*
          end
        ].
      - rewrite ok_get_equals; try solve[hint ok_add, ok_union, ok_eq; autos*].
        intros z. 
        destruct Γ₁, Γ₂, Γ, Δ. unfolds get, add; repeat (case_if || simpls || reduce_max || substs); use_equivalences; autos*;
        repeat match goal with 
        | [ H: context[_ \c _] |- _ ] => clear H 
        | [ H: context[_ \notin _] |- _ ] => clear H 
        | [ H: context[ [| _ |] _ |(_, _)- _ ∈ _ ] |- _ ] => clear H 
        | [ H: context[ [| _ |] _ |(_, _)- _ ∈ₘ _ ] |- _ ] => clear H 
        end;
        hint Types.union_assoc, union_perm_tail; autos*.
    }
    asserts Vf φ : (∃ Vf (φ : [|Vf|] Δ |( S (b + b'), r + r' )- TmAbs ([y ~> p] t) ∈ {{{{` M `}}|-> ` A `}}), True).
    {
      exists (V₁ \u \{y}).
      exists*.
      apply @T_Fun_b with (x := x); reduce_max; autos*; try solve[
          intro;
          asserts H_contra: (x \in fv p \u fv t);
          try solve[apply var_subst with (x := y); autos*];
          simpl_unions; try apply Hsub5 in H_contra; autos*
      ].
      - rewrite dom_equal with (Γ₂ := (Γ₂) ⊎c (Γ₁)); try solve[use_equivalences; autos].
        rewrite dom_union; reduce_max; intro; apply* n1.
      - hint ok_eq, ok_union; autos*.
      - des 
      replace (add (Γ₂) ⊎c (Γ₁) x M0) with ((add Γ₂ x M0) ⊎c Γ₁).
      { admit. }
      {  }
      try solve[
        abstract (
          simpls;
          destruct Γ₂, Γ₁;
          unfold add, union; case_if; fequals; try solve_set_equality;
          apply fun_ext_dep;
          intro;
          case_if*;
          clear 
            IHφ IH Hlcp Hsub HeqΔ HeqΓ₂ C0 C Hfree HokΓ₂ HokΓ₁ φₚ p v0 b' r' 
            IHφₜ φₜ n o v x M t A b r;
          induction* M0;
          simpls;
          fequals
        )
      ];
      abstract (rewrite* lc_open_substs;
      replace ((V₁ \u \{ y}) \u \{ x}) with ((V₁ \u \{ x}) \u \{ y}); 
      try abstract solve_set_equality).
      assumption).
    }
    exists* φ.
  - admit.
  - asserts IHφ IH: (
      ∃ φ :  [|(V₁ \u \{x}) \u \{ y}|] add Δ x {{` T `; nil}} |( b + b', r + r' )- [y ~> p] t ^ x ∈ A, True
    ). {
      apply IHφₜ with (V₂ := V₂) (Γ₁ := Γ₁) (Δ := add Δ x {{` T `; nil}}) (M := M) (Γ₂ := add Γ₂ x {{` T `; nil}}); autos*.
      - hint ok_add; autos.
      - intros z Hinz; reduce_max; try apply fv_open in Hinz; 
        reduce_max; autos.
        rewrite dom_add in Hinz; reduce_max; autos. absurd.
      - rewrite ok_get_equals; try solve[hint ok_add; autos].
        intros z. 
        destruct Γ₁, Γ₂, Γ, Δ. unfolds get, add; repeat (case_if || simpls || reduce_max || substs); hint union_perm_tail, Eq_MT_Cons; use_equivalences; autos*;
        try solve[
          match goal with 
          | [ |- context[m1 ?x]] => specialize HeqΓ₂1 with x; case_if*
          end
        ].
      - unfolds union, add, equals.
        repeat case_if; substs; destruct Γ₁, Γ₂, Δ, Γ; reduce_max; substs; autos*;
        intros z; case_if; substs*; hint Eq_MT_Cons, union_assoc; use_equivalences; autos*.
    }
    asserts φ : ([|V₁ \u \{ y}|] Δ |( b + b', S (r + r') )- TmAbs ([y ~> p] t) ∈ Ty_Tight TC_Abs).
    {
      apply @T_Fun_r with (x := x) (A := A) (T := T); autos*.
      - hint ok_eq, ok_union; autos*.
      - reduce_max; autos*.
        + intro Hin. apply fv_substs in Hin; reduce_max; autos.
        + erewrite <- dom_equal with (Γ₁ := (Γ₂) ⊎c (Γ₁)); 
          try (rewrite dom_union; intro); 
          reduce_max; autos.
      - rewrite* lc_open_substs.
        replace ((V₁ \u \{ y}) \u \{ x}) with ((V₁ \u \{ x}) \u \{ y}); try solve_set_equality.
        assumption.
    }
    exists* φ. 
  - asserts IHφ IH: (
      ∃ φ : [|V₁ \u \{ y}|] Δ |( b + b', r + r' )- [y ~> p0] t ∈ Ty_Tight TC_Neutral, True
    ). {
      eapply IHφₜ; autos*.
      intros z Hin; reduce_max; autos*.
    }
    asserts φ : ([|V₁ \u \{ y}|] Δ |( b + b', S (r + r') )- TmApp ([y ~> p0] t) ([y ~> p0] p) ∈ Ty_Tight TC_Neutral).
    { autos*. }
    exists* φ.
Qed. *)
Admitted. *)

(* Lemma 3.5 *)
Lemma substitution_typing :
  ∀ V₁ Γ₁ x M b₁ r₁ t A 
    (φₜ : [|V₁|] add Γ₁ x M |(b₁, r₁)- t ∈ A)
    V₂ Γ₂ b₂ r₂ p 
    (φₚ : [|V₂|] Γ₂ |(b₂, r₂)- p ∈ₘ M),
  ∃ V Δ (φ : [|V|] Δ |(b₁ + b₂, r₁ + r₂)- [x ~> p]t ∈ A),
      (equals Δ (Γ₁ ⊎c Γ₂))
  /\  (Z_of_nat (size φ) = (Z_of_nat (size φₜ)) + (Z_of_nat (size φₚ)) - (Z_of_nat (size M)))%Z
.
Proof.
  intros V₁ Γ₁ x M b₁ r₁ t A φₜ.
  inductions φₜ; introv.
  - admit.
  - admit.
  - admit.
  - admit.
  - destruct IHφₜ with (φₜ0 := φₜ) (φₚ := φₚ) 
      as [V' [Δ [φ' [HeqΔ Hsize]]]].
    { reflexivity. }
    { reflexivity. }
    exists V'. exists Δ. unshelve exists.
    + simpls*.
    + reduce_max; autos*.
      replace (size (@T_App_hd_r V' Δ ([x ~> p0] t) ([x ~> p0] p) (b + b₂) (r + r₂) φ')) with 
      (1 + size φ').
      2: { simpls*. }
      assert (size (@T_App_hd_r V (add Γ₁ x M) t p b r φₜ) = 1 + size φₜ). { simpls*. }
      replace (Z.of_nat (1 + size φ')) with (1 + Z.of_nat (size φ'))%Z.
      2: { lia. }
      rewrite Hsize. lia.
Admitted.

Lemma open_replace :
  ∀ u q x n,
  lc q ->
  {n ~> TmFVar x} (u ^^ q) = (({S n ~> TmFVar x} u) ^^ ({n ~> TmFVar x} q)).
Proof.
  induction u.
  - 
  Admitted.

Lemma step_open_vars : 
  ∀ t p x,
  lc t ->
  t --> p -> 
  t ^ x --> p ^ x
.
Proof.
  (* unfold "^".
  generalize 0.
  introv Hlc Hst; gen n x;
  inductions Hst; introv.
  - simpls. inverts Hlc. rewrite* open_replace.
  - simpls.
    constructor. apply* IHHst.
  - simpls.
    constructor.
    + induction t; simpls*.
    + apply* IHHst. *)
Admitted.

(* Prop 3.6 *)
Theorem quantitative_subject_reduction : 
  ∀ t p, t --> p ->
  ∀ V Γ b r A (φ : [|V|] Γ |(b, r)- t ∈ A),
  b >= 1 /\ ∃ (φ' : [|V|] Γ |(b - 1, r)- p ∈ A), size φ > size φ'.
Proof.
  induction t using term_size_ind; introv Hst; inverts Hst.
  - admit. 
  - remember (TmAbs t0) as term; destruct φ;
    inverts Heqterm; substs*.
    + destruct H with (p := p0 ^ x) (φ := φ) 
        as [Hb0_sup1 [IHφ HsizeIHφ]].
      { simpls. unfold lt_type. rewrite <- size_for_ind_open. apply le_refl. }
      { apply step_open_vars. 
        - admit.
        - assumption. }
      destruct b; split; try lia.
      simpls.
      asserts IHφ' HsizeIHφ' : (∃ φ : [|V \u \{ x}|] add Γ x M |( b, r )- p0 ^ x ∈ A, size IHφ = size φ). { 
        apply num_eq_typed;
        lia.
      }
      asserts Hfree : (x \notin V \u fv p0 \u dom Γ). { admit. }
      unshelve exists.
      * apply @T_Fun_b with (x := x); assumption.
      * simpls. lia.
    + destruct H with (p := p0 ^ x) (φ := φ) 
        as [Hb0_sup1 [IHφ HsizeIHφ]].
      { simpls. unfold lt_type. rewrite <- size_for_ind_open. apply le_refl. }
      { apply step_open_vars. 
        - admit.
        - assumption. }
      destruct b; split; try lia.
      simpls.
      asserts Hfree : (x \notin V \u fv p0 \u dom Γ). { admit. }
      unshelve exists.
      * apply @T_Fun_r with (x := x) (A := A) (M := M); assumption.
      * simpls. lia.
  - remember (TmApp t0 u) as term. destruct φ; 
    inverts Heqterm; substs*.
    + destruct H with (t' := t0) (p := p0) (φ := φ) 
        as [Hb_sup1 [IHφ HsizeIHφ]].
      { simpls. unfold lt_type. apply Sn_le_Sm. apply le_max_self. }
      { assumption. }
      destruct b; split; try lia.
      simpls.
      rewrite Nat.sub_0_r.
      lets IHφ' HsizeIHφ': (num_eq_typed _ _ _ b _ r _ _ IHφ); 
      try lia.
      unshelve exists; autos*.
      simpls. rewrite <- HsizeIHφ'. 
      lia.
    + destruct H with (t' := t0) (p := p0) (φ := φ) 
        as [Hb_sup1 [IHφ HsizeIHφ]].
      { simpls. unfold lt_type. apply Sn_le_Sm. apply le_max_self. }
      { assumption. }
      destruct b; split; try lia.
      simpls.
      rewrite Nat.sub_0_r.
      lets IHφ' HsizeIHφ': (num_eq_typed _ _ _ b _ r _ _ IHφ); 
      try lia.
      unshelve exists; autos*.
      simpls. rewrite <- HsizeIHφ'. 
      lia.
Admitted.


Inductive reduce_k : nat -> term -> term -> Prop :=
| RK_self : ∀ t, reduce_k 0 t t
| RK_Suc : 
  ∀ k t t' p, 
  t --> t' -> 
  reduce_k k t' p -> 
  reduce_k (S k) t p
.
(* Thm 3.7 *)
Theorem tight_correctness : 
  ∀ V Γ b r t A (φ :[|V|] Γ |(b, r)- t ∈ A),  
  ∃ p k, 
      reduce_k k t p 
  /\  k <= b 
  /\  normal p
  /\  size p + k <= size φ 
  /\  (tight φ -> b = k /\ size p = r /\ A = Ty_Tight TC_Neutral -> neutral p)
.
Proof.

Admitted.

(* Prop 3.8, OK *)
Theorem normal_forms_tightly_typable :
  ∀ t, 
  lc t ->
  normal t -> 
  (
    ∃ V Γ A (φ : [|V|] Γ |(0, size t)- t ∈ A), 
        tight φ
    /\  (neutral t -> A = Ty_Tight TC_Neutral)
    /\  (abs t -> A = Ty_Tight TC_Abs)
  ).
Proof.
  introv Hlc Hnorm.
  induction Hnorm.
  - inductions H.
    + inverts Hlc.
    + asserts: (
      equals 
        (add empty x {{` (Ty_Tight TC_Neutral) `; nil}}) 
        (add empty x {{` (Ty_Tight TC_Neutral) `; nil}})
      ). { use_equivalences; autos. }

      exists (\{} : vars) (add empty x {{`Ty_Tight TC_Neutral` ; nil}}) (Ty_Tight TC_Neutral).
      unshelve exists.
      * apply T_Ax. assumption. 
      * repeat (
          reduce_max || case_if || intro || simpls 
          || unfold tight || unfold add || unfold empty || unfold Tightable_der 
          || unfold Tight_type || unfold Tight_multitype || unfold Tightable_context
        ); autos*.
    + inverts Hlc.
      lets V Γ A φ [Htight [Hneuttight Hneutabs]]: (IHneutral H2).
      exists V Γ (Ty_Tight TC_Neutral).
      apply Hneuttight in H; substs.
      simpls.
      unshelve exists.
      * apply T_App_hd_r; assumption.
      * repeat (
          reduce_max || case_if || intro || simpls 
          || unfold tight || unfold Tightable_der || unfold Tight_multitype
          || unfold Tight_type || unfold Tightable_context
        ); autos*.
  - inverts Hlc.
    pick_fresh x.
    lets V Γ A φ [Htight [Hneuttight Hneutabs]] : (H0 x Fr (H2 x Fr)).
    lets H' : (H x Fr).
    exists V Γ.
    asserts  [Hneut | Habs]: (neutral (t ^ x) \/ abs (t ^ x)). { 
        destruct* t; unfold "^"; simpls*;
        case_if*.
    }
    + apply Hneuttight in Hneut; substs.
      exists (Ty_Tight TC_Abs).
      simpls.
      asserts φ' _ : (∃ φ : [|V \u \{ x}|] add Γ x {{nil}} |( 0, size_aux_term t )- t ^ x ∈ Ty_Tight TC_Neutral, True). {
        destruct vars_eq_typed with (V' := V \u \{ x}) (φ := φ) as [φ' _].
        { admit. }
        destruct num_eq_typed with (b' := 0) (r' := size_aux_term t ) (φ := φ') as [φ'' _].
        { reflexivity. }
        { symmetry. apply size_open. }
        destruct ctx_eq_typed with  (Δ := add Γ x {{nil}} ) (φ := φ'') as [φ''' _].
        { unfold add. case_if. use_equivalences; autos. }
        exists*.
      }

      unshelve exists.
      * apply @T_Fun_r with (x := x) (A := Ty_Tight TC_Neutral) (M := {{nil}}).
        -- apply (typed_ok _ _ _ _ _ _  φ).
        -- admit.
        -- simpls*.
        -- simpls*.
        -- assumption.
      * reduce_max; autos*.     
Admitted. 

(* Lemme 3.9 *)
Lemma anti_substitution_and_typing :
  ∀ V Γ b r t x p A (φ : [|V|] Γ |(b, r)- [x ~> p] t ∈ A),
  lc p ->
  ∃   
      (V : vars)
      (M : multitype)
      (bₜ bₚ rₜ rₚ : nat)
      (Γₜ Γₚ : ctx)
      (φₜ : [|V|] add Γₜ x M |(bₜ, rₜ)- t ∈ A)
      (φₚ : [|V|] Γₚ |(bₚ, rₚ)- p ∈ₘ M),
      equals (Γₜ ⊎c Γₚ) Γ 
  /\  ok Γₜ
  /\  b = bₜ + bₚ 
  /\  r = rₜ + rₚ 
  /\ size φ = size φₜ + size φₚ - size M
.
Proof.
  introv Hlc.
  inductions φ.
  - destruct* t; simpls;
    match goal with 
    | [H : TmFVar _ = _ |- _] => try solve[inverts* H]
    end.
    simpls; case_if.
    + substs*. 
      exists (V \u V) {{A; nil}} 0 0 0 0. exists empty Δ.
      asserts HokΓ: (ok Δ).
      { hint ok_add, ok_eq, ok_empty; use_equivalences;
        autos*. }
      asserts : (equals (add empty v {{` A `; nil}}) (add empty v {{` A `; nil}})). {use_equivalences; autos*. }
      asserts : (equals (empty) ⊎c (Δ) Δ). 
      { rewrite union_empty_l; use_equivalences; autos. }
      change 0 with (0 + 0).
      hint ok_empty. inverts* x.
      unshelve exists; autos*.
    + inverts x2.
      exists V {{nil}}. exists 0 0 0 0. 
      exists Δ empty.
      unshelve exists; autos*.
      ++ apply T_Ax. rewrite add_nil. assumption.
      ++ simpls; inverts x; reduce_max; 
        use_equivalences; hint ok_eq, ok_empty, ok_add;
        try rewrite union_empty_r; autos*.
  - inverts φ0; destruct t; simpls; try case_if; 
    try solve[inverts x2].
    + admit.
    + inverts x2. edestruct (IHφ (t ^ x0) x1 p).
      * admit.
      * admit.
      * assumption.
      * admit.
    + inverts H0. 
  - admit.
  - admit.
  - admit. 
Admitted.



Lemma freevars_step :
  ∀ t p,
  t --> p ->
  fv p \c fv t.
Proof.
  induction t using term_size_ind; destruct t; introv Hst; inverts Hst; simpls.
  - apply* H.
    unfold lt_type. apply le_refl.
  - unfold "^^". apply fv_open.
  - intros z Hin. reduce_max; autos*.
    left.
    specialize H with t1 p0.
    apply* H.    
    unfold lt_type. apply Sn_le_Sm, le_max_self.
Qed.



Lemma eq_size :
  ∀ V Γ b r t t' A (φ : [|V|] Γ |(b, r)- t ∈ A),
  t = t' ->
  ∃ (φ' : [|V|] Γ |(b, r)- t' ∈ A),
  size φ = size φ'.
Proof.
  introv.
  gen t'.
  inductions φ; intros; substs; exists*. 
Qed.
(* Prop 3.10 *)
Theorem quantitative_subject_expansion :
  ∀ t p,
  lc t ->
  t --> p -> 
  ∀ V Γ b r  A (φ : [|V|] Γ |(b, r)- p ∈ A),
  ∃ (φ' : [|V|] Γ |(S b, r)- t ∈ A),
  size φ' > size φ
.
Proof.
  intro t.
  induction t using term_size_ind; destruct t; intros * Hlc Hst *; inverts Hst.
  - remember (TmAbs p0) as ter. destruct φ eqn:Heq; 
    inverts Heqter.
    + asserts Hfree : (x \notin V \u fv t \u dom Γ). { 
        (* C'est faux pour l'instant, voir pour arranger tard *)
        admit.
      }
     destruct H with (t' := t ^ x) (φ := h).
      * unfold lt_type. rewrite <- size_for_ind_open. apply le_refl.
      * inverts* Hlc.
      * apply* step_open_vars.
      * unshelve exists. {
          apply @T_Fun_b with (x := x); assumption.
        }
        simpls; lia.
    + asserts Hfree : (x \notin V \u fv t \u dom Γ). { 
        (* C'est faux pour l'instant, voir pour arranger tard *)
        admit.
      }
     destruct H with (t' := t ^ x) (φ := h).
      * unfold lt_type. rewrite <- size_for_ind_open. apply le_refl.
      * inverts* Hlc.
      * apply* step_open_vars.
      * unshelve exists. {
          apply @T_Fun_r with (x := x) (A := A) (T := T); assumption. 
        }
        simpls; lia.
  - pick_fresh x.
    asserts Heq : (u ^^ t2 = [x ~> t2](u ^ x) ).
    { rewrite* <- open_subst. }
    inverts Hlc.
      lets φ' Hsize : (eq_size _ _ _ _ _ _ _ φ Heq).
    lets V' M bₜ bₚ temp : (anti_substitution_and_typing _ _ _ _ _ _ _ _ φ' H3). 
    lets rₜ rₚ Γₜ Γₚ temp2 : temp; clear temp.
    lets φₜ φₚ HeqΓ HokΓ [Heqb [Heqr Heqsize]] : temp2; clear temp2.
    asserts HVeq : (V \u V = V). 
    { apply union_same. }
    asserts HokΓₚ: (ok Γₚ). {
      apply* multityped_ok. 
    }
    asserts : (x \notin V \u fv u \u dom Γₜ). {
      reduce_max;
      rewrite dom_equal with (Γ₂ := (Γₜ) ⊎c (Γₚ)), dom_union in Fr4; use_equivalences; autos*.
    }
    asserts φₜ' Hsizeφₜ' : (
      ∃ φₜ' : [|V \u \{ x}|] add Γₜ x M |( bₜ, rₜ )- u ^ x ∈ A, 
      size φₜ = size φₜ'
    ). {
      apply vars_eq_typed.
      (* Faux mais on ignore pour l'instant *)
      admit.
    }
    asserts φₚ' Hsizeφₚ' : (
      ∃ φₚ' : [|V|] Γₚ |( bₚ, rₚ )- t2 ∈ₘ M, 
      size φₚ = size φₚ'
    ). {
      apply vars_eq_multityped.
      (* Faux mais on ignore pour l'instant *)
      admit.
    }
    asserts φf Hsizeφf : (∃ φ'0 : [|V \u V|] Γ |( S (bₜ + bₚ), rₜ + rₚ )- TmApp (TmAbs u) t2 ∈ A, size φ'0 > size φ). {
      unshelve exists.
      - change ( S (bₜ + bₚ)) with ( S bₜ + bₚ).
        apply  @T_App_b with (M := M) (Γ₁ := Γₜ) (Γ₂ := Γₚ); 
        try assumption.
        apply @T_Fun_b with (x:= x); assumption.
      - simpls; lia.  
    }
    lets φf' Hsizeφf' : (num_eq_typed _ _ _ (S b) _ r _ _ φf); try lia.
    rewrite Hsizeφf' in Hsizeφf; clear Hsizeφf' φf; rename φf' into φf.
    lets φf' Hsizeφf' : (vars_eq_typed _ _ V _ _ _ _ φf). 
    { apply union_same. }
    exists φf'. lia.
      
  - remember (TmApp p0 t2 ) as ter; destruct φ eqn:Heq; 
    inverts Heqter.
    + destruct H with (t' := t1) (φ := h).
      * unfold lt_type; simpls. apply Sn_le_Sm. apply le_max_self.
      * inverts* Hlc.
      * assumption.
      * unshelve exists. {
        change (S (b + b')) with (S b + b').
          apply @T_App_b with (Γ₁ := Γ₁) (Γ₂ := Γ₂) (M := M); 
          assumption.
        }
        simpls; lia.
    + destruct H with (t' := t1) (φ := h).
      * unfold lt_type; simpls. apply Sn_le_Sm. apply le_max_self.
      * inverts* Hlc.
      * assumption.
      * unshelve exists; autos*. simpls. lia.
Admitted.



Lemma lc_subst :
  ∀ t u x, lc t -> lc u -> lc ([x ~> u] t).
Proof.
  induction t using term_size_ind; destruct t; introv Hlct Hlcu; simpls*.
  - case_if*.
  - constructor. intros y Hnotin. rewrite open_subst.   


Lemma lc_step :
  ∀ t t', 
  lc t -> t --> t' -> lc t'.
Proof.
  induction t using term_size_ind; destruct t; introv Hlc Hstep; 
  inverts Hlc; inverts Hstep.
  - constructor. intros. apply H with (t' := t ^ x).
    + unfold lt_type; rewrite <- size_for_ind_open. apply le_refl.
    + apply H1. admit.
      (* rewrite* <- (freevars_step t p). *)
    + apply* step_open_vars.
  -  admit.
Admitted.

(* Thm 3.11 *)
Theorem tight_completeness :
  ∀ k t p,
  lc t ->
  reduce_k k t p ->
  normal p ->
  ∃ V Γ A (φ : [|V|] Γ |(k, size p)- t ∈ A),
      tight φ
  /\  (neutral p -> A = Ty_Tight TC_Neutral)
  /\  (abs t -> A = Ty_Tight TC_Abs)
.
Proof.
  introv Hlc Hred Hnorm.
  inductions Hred; try solve [apply* normal_forms_tightly_typable].
  destruct IHHred as [V [Γ [A [φ [IHtight [IHneut IHabs]]]]]]. try solve[hint lc_step; autos*].
  lets φ' Hsize : (quantitative_subject_expansion _ _ Hlc H _ _ _ _ _ φ).
  exists V Γ A φ'; unfold tight, Tightable_der in *; reduce_max; autos*.
  intro Habst'.
  inverts Habst'.
  inverts H.
  apply* IHabs.
Qed.
Print Assumptions quantitative_subject_expansion.
  Print Assumptions tight_completeness.
