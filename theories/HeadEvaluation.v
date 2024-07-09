From Coq Require Import Peano Nat Arith ZArith Lia Unicode.Utf8_core.
From TLC Require Import LibLN LibTactics LibFset.
From TTSB Require Import Tactics Classes.
From TTSB.Types Require Import Types Context.
Require Import Coq.Program.Equality.
From TTSB Require Import Syntax.
Import TypesNotations. 


Ltac auto_tilde :=
  try (solve[ auto with head_eval_hints
            | intuition auto with head_eval_hints
            | solve_set_equality
            | absurd ]).

Ltac auto_star ::= 
  try (solve [ eauto with head_eval_hints 
             | jauto 
             | intuition eauto with head_eval_hints
             | solve_set_equality
             | absurd ]).


Inductive neutral : term -> Prop :=
  (* | Neutral_BVar : ∀ (n : nat), neutral (TmBVar n) *)
  | Neutral_FVar : ∀ (x : var), neutral (TmFVar x)
  | Neutral_App : ∀ (t₁ t₂ : term), 
      neutral t₁ -> 
      lc t₂ -> 
      neutral (TmApp t₁ t₂)  
.
Hint Constructors neutral : head_eval_hints.

Inductive normal : term -> Prop :=
  | Normal_Neutral : 
      ∀ (t : term), neutral t -> normal t
  | Normal_Abs :
      ∀ (L : vars) (t : term),
      (∀ (x : var), (x \notin L) -> normal (t ^ x)) -> 
      normal (TmAbs t)
.
Hint Constructors normal : head_eval_hints.

Inductive abs : term -> Prop :=
(* Voir si besoin LC *)
  | Abs : ∀ (t : term), abs (TmAbs t)
.
Hint Constructors abs : head_eval_hints.

Ltac gather_vars := 
  let A := gather_vars_with (fun x : vars => x) in 
  let B := gather_vars_with (fun x : var => \{x}) in 
  let C := gather_vars_with (fun x : ctx => dom x) in 
  let D := gather_vars_with (fun x : term => fv x) in 
  constr:(A \u B \u C \u D).

Reserved Notation "t1 '-->' t2" (at level 50).
Inductive step : term -> term -> Prop :=
| ST_Beta : 
    ∀ (u q : term), 
    (TmApp (TmAbs u) q) --> (u ^^ q)
| ST_Abs : 
    ∀ (L : vars) (t p : term),
    (
      ∀ x, x \notin L \u fv t \u fv p ->
      t ^ x  --> p ^ x
    ) ->
    (* t --> p -> *)
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



Ltac pick_fresh x :=
  let L := gather_vars in pick_fresh_gen L x.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) := 
  apply_fresh_base T gather_vars x.


Definition deterministic {A : Type} (rel : A -> A -> Prop) :=
  ∀ a a₁ a₂, rel a a₁ -> rel a a₂ -> a₁ = a₂.  

Definition rel_normal {A : Type} (rel : A -> A -> Prop) (a : A) :=
  ¬ (∃ a', rel a a').

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

Theorem deterministic_step : deterministic step.
Proof.
  unfold deterministic.
  introv Hstep1 Hstep2.
  gen a₂.
  induction Hstep1; intros; inverts* Hstep2; 
  try solve [
    fequals*; hint open_notin_eq; pick_fresh x; reduce_max; autos*
  | false*
  ].
Qed.
Hint Resolve deterministic_step : head_eval_hints.


Reserved Notation "a -->* b" (at level 50).
Inductive multistep : term -> term -> Prop := 
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
  | [H : neutral (TmBVar _) |- _] => inverts* H
  | [H : neutral (TmAbs _) |- _] => inverts* H
  | [H : abs (TmApp _ _) |- _] => inverts* H
  | [H : abs (TmBVar _) |- _] => inverts* H
  | [H : abs (TmFVar _) |- _] => inverts* H
  | [H : TmFVar _ --> _ |- _] => inverts* H
  | [H : TmBVar _ --> _ |- _] => inverts* H
end : head_eval_hints.



Lemma step_open_vars : 
  ∀ t p x,
  t --> p -> 
  t ^ x --> p ^ x
.
Proof.
  unfold open; generalize 0.
  introv Hst; gen n x;
  inductions Hst; introv.
  - simpls.
    admit.
  - unfold open; simpls.
    let l := gather_vars in
    apply ST_Abs with (L := l).
    intros x' Hin.
    unfold "^".
    repeat rewrite* lc_open_diff.
  - simpls.
    constructor.
    + induction t; simpls*.
    + apply* IHHst.
Admitted.

(* Lemma step_open : 
  ∀ t t' x, 
  t --> t' ->
  ∃ t'', t ^ x --> t''.
Proof.
  unfold "^".
  generalize 0.
  intros n t; gen n; induction t using term_size_ind; destruct t; introv Hstep; inverts* Hstep; simpls*; try
  match goal with 
  | [ H : ?t --> _, IH : context[?t --> _]  |- _ ] => 
    eapply IH in H as [t'' Hst]
  end.
  - eexists; unfold "^"; simpls*.
    let l := gather_vars in apply ST_Abs with (L := l).
    intros y H_y_notin.
  - destruct (H t1) with (n := n) (t' := p) (x := x); autos.
    exists (TmApp x0 ([{n ~> TmFVar x}] t2)); unfold "^"; simpls*.
    applys* ST_App.
    destruct* t1; simpls; try case_if*.
Qed. *)

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
  - admit. (* edestruct IHt; autos*. *)
  - destruct* t1; simpls; try case_if*; inverts H0.
  - destruct* t1; simpls; repeat case_if*; substs*.
    edestruct IHt1; autos*.
Admitted.

Hint Resolve open_irrelevant : head_eval_hints.


Lemma rel_normal_is_normal : 
  ∀ t, lc t -> rel_normal step t -> normal t.
Proof.
  introv H_lc. 
  unfold rel_normal in *.
  inductions H_lc; intro H_rel_normal; autos*.
  + let l := gather_vars in apply Normal_Abs with (L := l).
    intros x Hnotin.
    applys* H0.
    intros [t' Hstep].
    lets t'' Hst : (open_irrelevant t t' x Hstep). 
    autos*.
    apply H_rel_normal.
    exists (TmAbs t'').
    let l := gather_vars in apply (ST_Abs l).
    intros y H_y_notin.
    apply* step_open_vars.
  + destruct* t1.
    * false*. inversion H_lc1.
    * constructor; constructor*.
    * do 2 constructor*.
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
      applys* (H0 x).
  - induction* t.
Qed.

(* TODO: Passer en paramètres les variables interdites *)

Reserved Notation "Γ '|(' b ',' r ')-' t '∈' T" (at level 70).
Reserved Notation "Γ '|(' b ',' r ')-' t '∈ₘ' T" (at level 70).
Inductive has_type : ctx -> nat -> nat -> term -> type -> Type :=
| T_Ax :
    ∀ {x : var} {A : type} {Δ : ctx},
    equals Δ (add empty x {{ A ; nil }}) ->
    Δ |(0, 0)- TmFVar x ∈ A
| T_Fun_b :
    ∀ {L : vars} 
      {Γ : ctx} {t : term} 
      {M : multitype} {A : type} 
      {b r : nat},
    ok Γ ->
    (
      ∀ (x : var), 
      x \notin L \u fv t \u dom Γ -> 
      add Γ x M |(b, r)- t ^ x ∈ A
    ) -> 
    Γ |(S b, r)- TmAbs t ∈ (M |-> A) 
| T_App_b :
    ∀ 
      {Γ₁ Γ₂ Δ : ctx} {t p : term} 
      {M : multitype} {A : type}
      {b r b' r' : nat},
    ok Γ₁ -> ok Γ₂ ->
    equals (union Γ₁ Γ₂) Δ -> 
    Γ₁ |(b, r)- t ∈ (M |-> A) ->
    Γ₂ |(b', r')- p ∈ₘ M ->
    Δ |(b + b', r + r')- (TmApp t p) ∈ A
| T_Fun_r :
    ∀ {L : vars}
      {Γ : ctx} {t : term}
      {b r : nat} {A : type} {M : multitype},
    ok Γ ->
    tight A -> 
    tight M -> 
    (
      ∀ (x : var), 
      x \notin L \u fv t \u dom Γ -> 
      add Γ x M |(b, r)- t ^ x ∈ A
    ) -> 
    Γ |(b, S r)- TmAbs t ∈ Ty_Tight TC_Abs

| T_App_hd_r :
  ∀ {Γ : ctx} {t p : term} {b r : nat},
  Γ |(b, r)- t ∈ Ty_Tight TC_Neutral -> 
  Γ |(b, S r)- TmApp t p ∈ Ty_Tight TC_Neutral
where 
  "Γ '|(' b ',' r ')-' t '∈' T" := (has_type Γ b r t T)
with  has_many_types : ctx -> nat -> nat -> term -> multitype -> Type :=
  | ManyT_Empty :
      ∀ {t : term},
        empty |(0, 0)- t ∈ₘ {{ nil }}
  | ManyT_Union :
        ∀ {Γ₁ Γ₂ Δ: ctx} 
          {t : term} 
          {A : type} {mt : multitype} 
          {b₁ b₂ r₁ r₂ : nat},
        ok Γ₁ -> ok Γ₂ ->
        equals (union Γ₁ Γ₂) Δ ->
        Γ₁ |(b₁, r₁)- t ∈ₘ mt ->
        Γ₂ |(b₂, r₂)- t ∈ A ->
        Δ |(b₁ + b₂, r₁ + r₂)- t ∈ₘ {{A; mt}}
  
where
  "Γ '|(' b ',' r ')-' t '∈ₘ' T" := (has_many_types Γ b r t T)
.
Hint Constructors has_many_types has_type : head_eval_hints.

Scheme has_type_mut_ind := Induction for has_type Sort Type
with has_many_types_mut_ind := Induction for has_many_types Sort Type.



Program Fixpoint size_typing_derivation {b r : nat} {Γ : ctx} {t : term} {T : type} (der : Γ |( b , r )- t ∈ T) : nat :=
    match der with 
      | T_Ax _ => 0
      (* | T_Many_Inv der => size_many_typing_derivation der *)
      | @T_Fun_b L Γ t _ _ _ _ _ der' => 
        let E := L \u fv t \u dom Γ in
        S (size_typing_derivation (der' (var_gen E) ((@var_gen_spec E))))
      | @T_Fun_r L Γ t _ _ _ _ _ _ _ der' =>
        let E := L \u fv t \u dom Γ in
        S (size_typing_derivation (der' (var_gen E) (@var_gen_spec E)))
      | T_App_b _ _ _ der₁ der₂ => 
          S ((size_typing_derivation der₁) + (size_many_typing_derivation der₂))
      | T_App_hd_r der' => S (size_typing_derivation der')
      (* | T_Many_Inv _ _ _ mder _ => 
        size_many_typing_derivation mder *)
      end
  with
    size_many_typing_derivation {b r : nat} {Γ : ctx} {t : term} {M : multitype} (der : Γ |( b , r )- t ∈ₘ M) : nat :=
    match der with 
    | ManyT_Empty => 0
    | ManyT_Union _ _ _ der₁ der₂ => size_many_typing_derivation der₁ + size_typing_derivation der₂
    (* | ManyT_Inv _ _ _  mder der => size_many_typing_derivation mder +  size_typing_derivation der *)
    end
.


#[global] Instance Size_der : 
  ∀ {b r : nat} {Γ : ctx} {t : term} {T : type}, 
  Sized (Γ |( b , r )- t ∈ T) :=
  fun {b r : nat} {Γ : ctx} {t : term} {T : type} =>
  {| size := size_typing_derivation |}
  .
#[global] Instance Size_mder : 
  ∀ {b r : nat} {Γ : ctx} {t : term} {M : multitype}, 
  Sized (Γ |( b , r )- t ∈ₘ M) :=
  fun {b r : nat} {Γ : ctx} {t : term} {M : multitype} =>
  {| size := size_many_typing_derivation |}
  .

#[global] Instance Tightable_der : 
  ∀ {b r : nat} {Γ : ctx} {t : term} {T : type}, 
  Tightable (Γ |( b , r )- t ∈ T) :=
    fun {b r : nat} {Γ : ctx} {t : term} {T : type} => 
    {| tight := fun _ => tight T /\ tight Γ |}.


(* Lemma ManyT_Inv :
      ∀ {V₁ V₂ : vars} {Γ₁ Γ₂ Δ : ctx} {t : term} {A : type} {mt : multitype} 
        {b₁ b₂ r₁ r₂ : nat},
        ok Γ₁ -> ok Γ₂ ->
        equals (union Γ₁ Γ₂) Δ ->
        Δ  |(b₂, r₂)- t ∈ₘ {{A; mt}} ->
        Γ₁ |(b₁, r₁)- t ∈ A ->
        ∃ Γ b r (φ : Γ |(b, r)- t ∈ₘ mt), True.
        
Proof.
  introv Hok1 Hok2 Heq φ1 φ2.
  inverts* φ1.
  exists Γ₂.
  
Qed. *)


Lemma typed_empty :
  ∀ Γ b r t
  (φ : Γ |(b, r)- t ∈ₘ {{nil}}),
  Γ = empty /\ b = 0 /\ r = 0 /\ size φ = 0.
Proof.
  introv.
  inversion φ; substs*; autos.
  inductions φ; autos.
Qed.


Lemma size_typed_var :
  ∀ Γ b r x A
  (φ : Γ |(b, r)- TmFVar x ∈ A),
  size φ = 0.
Proof.
  introv.
  inversion φ; substs*; autos.
  inductions φ; autos.
Qed.


Lemma typed_ok : ∀ {Γ b r t A}, 
Γ |(b, r)- t ∈ A -> ok Γ.
Proof.
  introv φ.
  induction φ; autos*; eauto with context_hints.
  eapply ok_eq.
  - use_equivalences. clear eq_ctx_refl; autos*.
  - apply ok_add, ok_empty. 
Qed.

Lemma multityped_ok : ∀ {Γ b r t M}, 
Γ |(b, r)- t ∈ₘ M -> ok Γ.
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
Example first_derivation : empty |(3, 1)- example_term ∈ (Ty_Tight TC_Abs).
Proof with try solve[
        simpls; reduce_max; intro; auto
        | auto with context_hints
].
  unfold example_term.
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
  - apply @T_Fun_b with (L := \{}); simpls~.
    { intro. split; intros; false*; reduce_max. }
    intros x Hnotinx.
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
    + eapply @T_Fun_b with (L := \{x}); simpls*...
      intros x2 Hnotinx2.
      replace 0 with (0 + 0); autos*.
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
      apply @ManyT_Union with (Γ₁ := empty) (Γ₂ := add empty x {{` abs_abs `; nil}}); autos*...
      { use_equivalences; rewrite* union_empty_l. }
      { constructor; use_equivalences; auto. }

  - unfold Id.
    change 1 with (1 + 0) at 1.
    change 1 with (0 + 1) at 2.
    apply @ManyT_Union with (A := Ty_Tight TC_Abs) (mt := {{ `abs_abs` ; nil }}) (Γ₁ := empty) (Γ₂ := empty); unfold abs_abs; autos...
      { use_equivalences; rewrite* union_empty_l. }
    + apply @ManyT_Union with 
      (Γ₁ := empty) (Γ₂ := empty) (b₁ := 0) (r₁ := 0); autos*...
      { use_equivalences; rewrite* union_empty_l. }
      let myL := gather_vars in 
      eapply @T_Fun_b with (L := myL); autos*...
      intros x Hnotinx. 
      unfold "^"; simpls.
      case_if*.
      constructor; use_equivalences; auto.

    + let myL := gather_vars in 
      apply @T_Fun_r 
      with 
        (L := myL)
        (M := {{`Ty_Tight TC_Abs`; nil}}) 
        (A := Ty_Tight TC_Abs); intros;
      unfold "^"; simpls; repeat case_if; autos*...
      constructor; use_equivalences; auto.
Qed.

Ltac derivation_induction der P0 := 
  induction der using has_type_mut_ind with (P0:=P0); unfold P0 in *; clear P0.


Goal ∀ {Γ: ctx} {t : term} {A : type} {b r : nat} (φ : Γ |(b, r)- t ∈ A),
b + r <= size_typing_derivation φ.
Proof.
  intros.
  pose (P0 (Γ: ctx) (b r : nat) (t : term) (M : multitype) (φ : Γ |(b, r)- t ∈ₘ M) := b + r <= size_many_typing_derivation φ).
  derivation_induction φ P0; simpl;
  try (pose (E := (L \u fv t \u dom Γ)); specialize H with (var_gen E) (var_gen_spec (E := E)); unfold E; clear E);
  try specialize H with (var_gen (L \u fv t \u dom Γ)) (var_gen_spec (E:=L \u fv t \u dom Γ));
  lia.
Qed.

Definition last_rule_is_appb 
    {b r : nat} {Γ : ctx} {t : term} {T : type} 
    (der : Γ |( b , r )- t ∈ T) : Prop := 
  match der with 
  | T_Ax _ => False
  | T_Fun_b _ _ => False
  | T_Fun_r _ _ _ _ => False
  | T_App_b _ _ _ _ _ => True
  | T_App_hd_r _ => False
  end.


Lemma tight_spreading_var :  
  ∀ {Γ : ctx} {b r : nat} {x : var} {A : type}
    (φ : Γ |( b, r )- TmFVar x ∈ A), 
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
  ∀ {Γ : ctx} {b r : nat} {A : type}
    (φ : Γ |(b, r)- t ∈ A), 
  tight Γ ->
  tight A /\ ¬ last_rule_is_appb φ.
Proof.
  intros t H_neutral.
  induction H_neutral as [ x | p u H_neutral_p IH]; introv H_tight.
  - applys* (tight_spreading_var 
              (Γ := Γ) 
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


Lemma normal_open_var_irrelevant : ∀ t x y, normal (t ^ x) -> normal (t ^ y).
Proof.
  unfold "^". generalize 0; intros n t; gen n.
  induction t using term_size_ind; destruct t; introv Hnorm; simpls*.
  - case_if*.
  - inverts* Hnorm.
    apply Normal_Abs with (L := L); intros x0 Hnotinx0.
    apply H1 in Hnotinx0.
    rewrite* lc_open_diff.
    apply H with x.
    + rewrite <- size_for_ind_open. apply le_refl.
    + rewrite* <- lc_open_diff.
  - inverts* Hnorm; inverts* H0.
    do 2 constructor.
    + apply neutral_is_normal_not_abs.
      * apply* H. 
      * destruct t1; simpls*; case_if*.
    + {
      clear H H3 t1.
      gen n x y.
      rename t2 into t.
      induction t using term_size_ind; destruct t; intros * Hlc *; simpls*; try case_if*.
      - inverts Hlc.
        apply LCAbs.
        intro x'. 
        rewrite* lc_open_diff.
        apply H with (x := x); autos.
        rewrite* <- lc_open_diff.
      - inverts* Hlc.
    } 
Qed.  



Lemma normal_size_derivation : 
  ∀ {t : term} {Γ : ctx} {b r : nat} {A : type} 
    (φ : Γ |(b, r)- t ∈ A), 
  normal t -> 
  size t <= size_typing_derivation φ.
Proof with simpls*; try lia.
  introv H_normal_t.
  inductions φ; inverts H_normal_t; subst; simpl; try apply IHφ in H0...
  - specialize H with (var_gen (L \u fv t \u dom Γ)) (var_gen_spec (E:=L \u fv t \u dom Γ)).
    asserts : (normal (t ^ var_gen (L \u fv t \u dom Γ))). {
      pick_fresh x.
      apply normal_open_var_irrelevant with x.
      apply* H1.
    } rewrite <- size_open in H; simpls. apply H in TEMP; lia. 

  - inverts* H; neutral_to_normal t. apply IHφ in H2...
  - specialize H with (var_gen (L \u fv t \u dom Γ)) (var_gen_spec (E:=(L \u fv t \u dom Γ))).
    asserts : (normal (t ^ var_gen (L \u fv t \u dom Γ))). {
      pick_fresh x.
      apply normal_open_var_irrelevant with x.
      apply* H1.
    } rewrite <- size_open in H; simpls. apply H in TEMP; lia. 
  - inverts* H; neutral_to_normal t; apply IHφ in H2...
Qed.

Ltac use_type_spreading Γ :=
  match goal with 
  | [ H : Γ |(_, _)- _ ∈ {{ {{_}} |-> _}} |- _] => 
      apply tigh_spreading_on_neutral_terms in H; eauto; subst; inversion H
  end. 

Theorem normal_tight_der_size_b_r :
  ∀ {t : term} {Γ : ctx} {b r : nat} {A : type} 
    (φ : Γ |(b, r)- t ∈ A), 
  normal t -> 
  tight φ -> 
  b = 0 /\ r = size t.
Proof with try lia; eauto using union_tight_ctx.
  asserts size_eq : (size = size_aux_term)...
  induction t using term_size_ind.
  gen H.
  induction t; intros H_ind_size * H_normal_t H_tight_der; destruct H_tight_der as [H_tight_A H_tight_Γ]; inversion φ; subst; simpl; try (inversion H_tight_A; fail)...
  - inverts H_normal_t; try solve[inversion H].
    pick_fresh x. 
    asserts H_size : (lt_type (size_for_ind (t ^ x)) (size_for_ind (TmAbs t))). 
    { unfold lt_type. hint le_refl. rewrite* <- size_for_ind_open. }
    (* specialize H2 with x. *)
    asserts Hfree : (x \notin fv t). { auto. }
    destruct H_ind_size with (φ := X x ltac:(auto)); autos*.
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
  ∀ {t : term} {Γ : ctx} {b r : nat} 
    (φ : Γ |(b, r)- t ∈ Ty_Tight TC_Neutral), 
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
  ∀ t p n, fv ([{ n ~> p}] t) \c fv t \u fv p.
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




(* Lemma vars_eq_typed : 
  ∀ Γ V V' b r p A (φ : Γ |(b, r)- p ∈ A),
  V = V' ->
  ∃ φ' : Γ |(b, r)- p ∈ A, size φ = size φ'.
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
Qed. *)
(*   
Lemma vars_eq_multityped : 
  ∀ Γ V V' b r p M (φ : Γ |(b, r)- p ∈ₘ M),
  V = V' ->
  ∃ φ' : Γ |(b, r)- p ∈ₘ M, size φ = size φ'.
Proof.
  introv Heq.
  gen V'.
  inductions φ; intros.
  - unshelve exists; autos*. 
  - destruct (IHφ V₁) as [φ' Hsizeφ']; substs*.
Qed.   *)
Locate "{ _ | _ }".

Check @T_Fun_b.
Lemma T_Fun_proof_irrelevant :
  ∀ {L : vars} {Γ : ctx} {t : term} {M : multitype} {A : type} {b r : nat}
  (der : (∀ x : var, x \notin L → add Γ x M |( b, r )- t ^ x ∈ A))
  x₁ x₂ pf₁ pf₂,
  size (der x₁ pf₁) = size (der x₂ pf₂).
Proof.
  unfold open.
  generalize 0.
  introv.
  induction t.
  - remember (der x₁ pf₁) as der₁;
    remember (der x₂ pf₂) as der₂;
    dependent destruction der₁;
    dependent destruction der₂; 
    try solve[unfolds open; simpls; case_if*].
    substs. destruct (der x₂ pf₂); destruct (der x₁ pf₁); 
    simpls*; false*.
  - remember (der x₁ pf₁) as der₁;
    remember (der x₂ pf₂) as der₂;
    dependent destruction der₁;
    dependent destruction der₂; 
    try solve[unfolds open; simpls; case_if*].
    reflexivity.
  - remember (der x₁ pf₁) as der₁;
    remember (der x₂ pf₂) as der₂;
    dependent destruction der₁;
    dependent destruction der₂; 
    try solve[unfolds open; simpls; case_if*].
    simpls*.
    + admit. 
    + admit.
  - remember (der x₁ pf₁) as der₁;
    remember (der x₂ pf₂) as der₂;
    dependent destruction der₁;
    dependent destruction der₂; 
    try solve[unfolds open; simpls; case_if*].
    simpls*.

Admitted.


Lemma open_eq_free_typed : 
  ∀ {Γ b r p A M x} (φ : add Γ x M |(b, r)- p ^ x ∈ A) y,
  ok Γ ->
  (x \notin dom Γ \u fv p) ->
  (y \notin dom Γ \u fv p) ->
  { φ' : add Γ y M |(b, r)- p ^ y ∈ A | size φ = size φ' }.
Proof.
  unfold "^"; generalize 0.
  (* Voir pour généraliser le 0 du open *)
  introv Hok Hxnotin Hynotin.
  (* remember ([{n ~> TmFVar x}] p) as term.
  remember (add Γ x M) as Γ'. *)
  inductions φ; destruct p; intros; substs; unfolds open; simpls; repeat case_if*; 
  try solve [inverts x2 | inverts x1].
  - inverts x2.
    asserts [-> | HeqM] : ({M = {{nil}}} + {eq_multitype M {{A ; nil}}}). {
      clear x.
      destruct* M; right.
      rewrite ok_get_equals in e; autos*; try solve[
        apply ok_eq with (Γ₁ := add empty x1 {{` A `; nil}}); hint ok_add, ok_empty; use_equivalences; autos
      ].
      specialize e with x1.  
      destruct Γ. unfolds add.
      repeat (case_if || simpls).
      destruct (Types.union M (m x1)) eqn:Heq.
      - apply Eq_MT_Cons. {
          clear C φ0 Hynotin Hxnotin Hok Heq C2 C1 C0 x1 y M n0 m v n.
          inductions e; intros.
          - assumption.
          - destruct mt₂;
            apply eq_size in e1; simpls; inverts e1.
            destruct mt₂; inverts H0.
            use_equivalences; autos*.
        }
        apply nil_eq_union in Heq; reduce_max; use_equivalences; substs*.
      - apply eq_size in e; false*. 
    }
    + false. 
      asserts Heqget : (eq_multitype (get Γ x1) {{` A `; nil}}). {
        clear x.
        substs.
        rewrite add_nil in e.
        rewrite (ok_get_equals _ ((add empty x1 {{` A `; nil}})) Hok ltac:(hint ok_add, ok_empty; autos*)) in e.
        specialize e with x1; unfolds add, empty; repeat (simpls || case_if).
        assumption.
      }
      unfolds ok. destruct Γ; simpls.
      destruct* (Hok x1).
      apply Hxnotin.
      reduce_max.
      apply H0.
      destruct* (m x1).
      apply eq_size in Heqget; false*.
    + asserts: (Γ = empty). {
        clear x.
        apply equals_empty_is_empty.
        apply* ok_get_equals. apply ok_empty.
        destruct (ok_get_equals (add Γ x1 M) (add empty x1 {{` A `; nil}})); try solve[hint ok_add, ok_empty; autos*].
        intro x'.
        apply H with x' in e.
        unfolds add; destruct Γ; repeat (simpls || case_if || substs || reduce_max); auto.
        - apply eq_size in HeqM. false*.
        - destruct (Hok x1).
          destruct (m x1).
          + use_equivalences; autos.
          + false.
            apply Hxnotin.
            apply* H2.
      }
      substs.
      asserts : (equals (add empty y M) (add empty y {{` A `; nil}})). {
        use_equivalences; apply* equals_add.
      }
      unshelve eexists; autos*.
      inverts* x.
  - inverts x2; reduce_max.
    asserts : (M = {{ nil }}). { 
      destruct* M.
      clear x.
      rewrite (ok_get_equals (add Γ x1 {{` t `; ` M `}}) (add empty v {{` A `; nil}}) ltac:(hint ok_add, ok_empty; auto) ltac:(hint ok_add, ok_empty; auto)) in e.
      specialize e with x1.
      rewrite get_add_eq in e.
      unfolds add, empty.
      repeat (simpls || case_if).
      apply eq_size in e; false*.
    }
    substs. lets e' : e; rewrite add_nil in *.
    unshelve eexists. 
    + apply T_Ax; assumption.
    + inverts x; simpls*.
  - inverts x1.

    admit.
  - inverts x1. admit.
  - admit.
  - admit.  
Admitted.

Lemma typed_subst :
  ∀ {Γ b r p A} (φ : Γ |(b, r)- p ∈ A)
    Γ' b' r' p' A',
    equals Γ Γ' ->
    b = b' ->
    r = r' ->
    p = p' ->
    eq_type A A' ->
    { φ' : Γ' |(b', r')- p' ∈ A' |
      size φ = size φ' }.
Proof.
  intros Γ b r p A φ.
  induction φ; introv HeqΓ Heqb Heqr Heqp HeqA; substs.
  - asserts : (equals Γ' (add empty x {{` A' `; nil}})). {
      use_equivalences.
      apply eq_ctx_trans with (add empty x {{` A `; nil}}); autos*.
      unfold add, empty, equals; repeat (case_if || reduce_max || simpls); autos.
      intro; case_if*.
      apply* Eq_MT_Cons.
    }
    unshelve eexists; autos*.
  - pose (x := var_gen (L \u fv t \u dom Γ)).
    pose (Hxfree := (@var_gen_spec (L \u fv t \u dom Γ))).
    destruct A' as [ | | M' A']; try solve[false*; inverts HeqA].
    asserts : (eq_type A A'). { inverts* HeqA. }
    asserts : (eq_multitype M M'). { inverts* HeqA. }
    destruct (X x (Hxfree)) with (Γ' := add Γ' x M') (b' := b) (A' := A') (r' := r') (p' := t ^ x); try solve[
      hint equals_add; use_equivalences; autos*
    ].
    asserts HxfreeL : (x \notin L).
    { auto. lets: (@var_gen_spec (L \u fv t \u dom Γ)). unfolds* x. }
    asserts : (x\notin dom Γ').
    { rewrite* <- (dom_equal Γ). unfolds* x.  }
    asserts : (x\notin fv t).
    { intro. apply Hxfree; reduce_max; autos. }
    asserts: (ok Γ').
    { hint ok_eq; autos*. }
    unshelve eexists.
    + apply @T_Fun_b with (L := ((L \u dom Γ) \u dom Γ') \u fv t).
      * assumption.
      * intros x1 Hx1notin.
        destruct (open_eq_free_typed x0 x1);
        try assumption; abstract (reduce_max; autos). 
    + simpls*. fequals.
      match goal with 
      | [ |- context[let (_, _) := ?r in _]] => destruct r
      end.
      unfolds x.
      unfolds Hxfree.
      simpls. lia.
  - destruct IHφ with Γ₁ b r t {{{{` M `}}|-> ` A' `}}; 
    try solve[use_equivalences; try constructor; simpls*].
    asserts : (equals (Γ₁) ⊎c (Γ₂) Γ'). { use_equivalences; autos*. }
    unshelve eexists.
    + apply @T_App_b with (M := M) (Γ₁ := Γ₁) (Γ₂ := Γ₂); assumption.
    + simpls*.
  - pose (x := var_gen (L \u fv t \u dom Γ)).
    pose (Hxfree := (@var_gen_spec (L \u fv t \u dom Γ))).
    edestruct (X x Hxfree) with (Γ' := add Γ' x M) (b' := b') (A' := A); try solve[hint equals_add; use_equivalences; autos*].
    asserts HxfreeL : (x \notin L).
    { unfolds* x, Hxfree. }
    asserts : (x\notin dom Γ').
    { rewrite* <- (dom_equal Γ). unfolds* x, Hxfree. }
    asserts : (x\notin fv t).
    { intro. apply Hxfree. unfolds* x, Hxfree. reduce_max; auto. }
    asserts: (ok Γ').
    { hint ok_eq; autos*. }
    asserts : (Ty_Tight TC_Abs = A'). { inverts* HeqA. } substs*.
    unshelve eexists.
    + apply @T_Fun_r with 
      (L := ((L \u dom Γ) \u dom Γ') \u fv t) (A := A) (M := M); 
      try solve[
        assumption |
        intros; intros y Hin; reduce_max; auto
      ].
      intros x1 Hx1notin.
      destruct (open_eq_free_typed x0 x1);
      try assumption; abstract (try ( reduce_max; autos)).
    + simpls*. fequals.
      match goal with 
      | [ |- context[let (_, _) := ?r in _]] => destruct r
      end.
    unfolds x, Hxfree. simpls. lia.
  - destruct IHφ with Γ' b' r t A';
    try solve[use_equivalences; try constructor; simpls*].
    asserts : (Ty_Tight TC_Neutral = A'). { inverts* HeqA. } substs*.
    unshelve eexists; autos*; simpls*.
Qed.



Lemma multityped_subst :
  ∀ {Γ b r p M} (φ : Γ |(b, r)- p ∈ₘ M)
    Γ' b' r' p' M',
    equals Γ Γ' ->
    b = b' ->
    r = r' ->
    p = p' ->
    eq_multitype M M' ->
    ∃ φ' : Γ' |(b', r')- p' ∈ₘ M',
      size φ = size φ'.
Proof.
  asserts ctx_eq_multityped : (
    ∀ Γ Δ b r p M (φ : Γ |(b, r)- p ∈ₘ M),
    equals Γ Δ ->
    ∃ φ' : Δ |(b, r)- p ∈ₘ M, size φ = size φ'
  ). {
    introv Heq.
    gen Δ.
    inductions φ; intros.
    - use_equivalences. apply eq_ctx_sym in Heq. rewrite equals_empty_is_empty in Heq; substs*.
    - asserts : (equals (Γ₁) ⊎c (Γ₂) Δ0).
      { use_equivalences; autos*. }
      unshelve exists.
      + apply @ManyT_Union with (Γ₁ := Γ₁) (Γ₂ := Γ₂); assumption.
      + simpls*. 
  }
  asserts  num_eq_multityped : (
    ∀ Γ b b' r r' p M (φ : Γ |(b, r)- p ∈ₘ M),
    b = b' ->
    r = r' ->
    ∃ φ' : Γ |(b', r')- p ∈ₘ M, size φ = size φ'
  ). {
    introv Heqb Heqr.
    gen b' r'.
    inductions φ; intros; substs; exists*.
  }
  introv HeqΓ Heqb Heqr Heqp HeqM; substs.
  gen Γ p' r' b' Γ'.
  inductions HeqM; intros.
  - inverts φ.
    asserts : (Γ' = empty). { 
      apply equals_empty_is_empty; use_equivalences; autos*. 
    } substs*.
  - remember {{` t₁ `; ` mt₁ `}} as M. destruct φ eqn:Heqφ; inverts HeqM0.
    destruct IHHeqM with (φ := h) (Γ' := Γ₁). { use_equivalences; autos. }
    destruct (typed_subst h0 Γ₂ b₂ r₂ t t₂); try solve[ use_equivalences; autos* ].
    asserts: (equals (Γ₁) ⊎c (Γ₂) Γ'). { use_equivalences; autos*. }
    unshelve exists; autos*; simpls*.
  - remember ({{` t₁ `; ` t₂ `; ` mt `}}) as t_temp. 
    destruct φ eqn:Heqφ; inverts Heqt_temp.
    remember {{` t₂ `; ` mt `}} as t_temp.
    destruct h eqn:Heqh; inverts Heqt_temp.
    asserts φf Hsizeφf: (∃ φ' : Δ |( b₁ + b₂ + b₂0, r₁ + r₂ + r₂0  )- t ∈ₘ {{` t₂ `; ` t₁ `; ` mt `}}, size φ = size φ'). { 
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
      asserts : (equals (Γ₁) ⊎c (Γ₂) (Γ₁) ⊎c (Γ₂)). {
        use_equivalences; autos.
      }

      
      unshelve exists.
      - apply @ManyT_Union with (Γ₁ := Γ₁ ⊎c Γ₂) (Γ₂ := Γ₂0); try assumption.
        apply @ManyT_Union with (Γ₁ := Γ₁) (Γ₂ := Γ₂); try assumption.
      - substs. simpls. lia.
    }
    asserts: (equals (Γ₁) ⊎c (Γ₂) (Γ₁) ⊎c (Γ₂)). { use_equivalences; autos. }
    asserts φf' Hsizeφf': (∃ φ' : Γ' |( b₁ + b₂ + b₂0, r₁ + r₂ + r₂0  )- t ∈ₘ {{` t₂ `; ` t₁ `; ` mt `}}, size φf = size φ'). {
      apply ctx_eq_multityped. assumption.
    }
    rewrite Heqφ in Hsizeφf.
    rewrite Hsizeφf.
    rewrite Hsizeφf'.
    apply num_eq_multityped; lia.
  - destruct IHHeqM1 with (φ := φ) (Γ' := Γ') as [φ' ->]; autos*.
    apply IHHeqM2.
    use_equivalences; autos.
Qed.

(* Lemma substitution_typing :
  ∀ (V₁ V₂ : vars)
    (Γ₁ Γ₂ Γ₂' Δ : ctx) (y : var) (M : multitype) 
    (t p : term) (A : type)
    (b b' r r' : nat)
    
    (φₜ : Γ₂' |(b, r)- t ∈ A)
    (φₚ : Γ₁ |(b', r')- p ∈ₘ M),
    ok Γ₁ -> ok Γ₂ -> lc p ->
    (V₂ \u dom Γ₁ \u dom Γ₂ \u fv p) \c V₁ ->
    (* (V₂ \u dom Γ₁ \u dom Γ₂ \u fv t \u fv p) \c V₁ -> *)
    y \notin V₁ ->
    equals (add Γ₂ y M) Γ₂' -> 
    equals Γ₂ ⊎c Γ₁ Δ ->
    ∃ (φ : Δ |(b + b', r + r')- [y ~> p] t ∈ A), 
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
          | [H : _ |(_, _)- _ ∈ _ |- _] => clear H 
          | [H : _ |( _ , _ )- _ ∈ₘ _ |- _] => clear H 
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
      asserts φ : (Δ0 |( b', r' )- TmFVar x ∈ A). {
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
      ∃ (φ : add Δ x M |( b + b', r + r' )- [y ~> p] t ^ x ∈ A), True
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
        | [ H: context[ _ |(_, _)- _ ∈ _ ] |- _ ] => clear H 
        | [ H: context[ _ |(_, _)- _ ∈ₘ _ ] |- _ ] => clear H 
        end;
        hint Types.union_assoc, union_perm_tail; autos*.
    }
    asserts Vf φ : (∃ Vf (φ : Δ |( S (b + b'), r + r' )- TmAbs ([y ~> p] t) ∈ {{{{` M `}}|-> ` A `}}), True).
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
      ∃ φ :  add Δ x {{` T `; nil}} |( b + b', r + r' )- [y ~> p] t ^ x ∈ A, True
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
    asserts φ : (Δ |( b + b', S (r + r') )- TmAbs ([y ~> p] t) ∈ Ty_Tight TC_Abs).
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
      ∃ φ : Δ |( b + b', r + r' )- [y ~> p0] t ∈ Ty_Tight TC_Neutral, True
    ). {
      eapply IHφₜ; autos*.
      intros z Hin; reduce_max; autos*.
    }
    asserts φ : (Δ |( b + b', S (r + r') )- TmApp ([y ~> p0] t) ([y ~> p0] p) ∈ Ty_Tight TC_Neutral).
    { autos*. }
    exists* φ.
Qed. *)
Admitted. *)


(* Lemma 3.5 *)
Lemma substitution_typing :
  ∀ {Γ₁ x M b₁ r₁ t A} 
    (φₜ : add Γ₁ x M |(b₁, r₁)- t ∈ A)
    {Γ₂ b₂ r₂ p} 
    (φₚ : Γ₂ |(b₂, r₂)- p ∈ₘ M),
  ∃ Δ (φ : Δ |(b₁ + b₂, r₁ + r₂)- [x ~> p]t ∈ A),
      (equals Δ (Γ₁ ⊎c Γ₂))
  /\  (Z_of_nat (size φ) = (Z_of_nat (size φₜ)) + (Z_of_nat (size φₚ)) - (Z_of_nat (size M)))%Z
.
Proof.
  intros Γ₁ x M b₁ r₁ t A φₜ.
  inductions φₜ; introv.
  - admit.
  - admit.
  - admit.
  - admit.
  - destruct IHφₜ with (φₜ0 := φₜ) (φₚ := φₚ) 
      as [Δ [φ' [HeqΔ Hsize]]]; try solve[reflexivity].
    exists Δ. unshelve exists.
    + simpls*.
    + reduce_max; autos*.
      replace (size (@T_App_hd_r Δ ([x ~> p0] t) ([x ~> p0] p) (b + b₂) (r + r₂) φ')) with 
      (1 + size φ').
      2: { simpls*. }
      assert (size (@T_App_hd_r (add Γ₁ x M) t p b r φₜ) = 1 + size φₜ). { simpls*. }
      replace (Z.of_nat (1 + size φ')) with (1 + Z.of_nat (size φ'))%Z.
      2: { lia. }
      rewrite Hsize. lia.
Admitted.




(* Prop 3.6 *)
Theorem quantitative_subject_reduction : 
  ∀ t p, 
  lc t -> lc p ->
  t --> p ->
  ∀ Γ b r A (φ : Γ |(b, r)- t ∈ A),
  b >= 1 /\ ∃ (φ' : Γ |(b - 1, r)- p ∈ A), size φ > size φ'.
Proof.
  introv Hlct Hlcp Hst.
  gen p Hlct.
  induction t using term_size_ind; intros; destruct Hst.
  - gen_eq : (TmApp (TmAbs u) q); intro.
    destruct φ eqn:Heq; inverts EQX.
    + dependent destruction h.
      split; try lia.
      simpls.
      asserts H_last_rule : (last_rule_is_appb φ). {
        repeat match goal with 
        | [H : _ |- _] =>  try clear H
        end.
        remember (TmApp (TmAbs u) q) as t.
        destruct φ; try solve[inverts Heqt]; simpls*.
        substs*.
        inverts Heqt; substs*.
        inverts φ.
      }
      pose (x := var_gen (L \u fv u \u dom Γ)).
      pose (Hxfree := (var_gen_spec (E:=L \u fv u \u dom Γ))).
      asserts φf Hsize: (
        ∃ φ' : Δ |( b + b' - 0, r + r' )- [x ~> q](u ^ x) ∈ A, S (S (size_typing_derivation (h (var_gen (L \u fv u \u dom Γ)) (var_gen_spec (E:=L \u fv u \u dom Γ))) + size_many_typing_derivation h0)) > size_typing_derivation φ'
      ). {
        pose (φux := h x Hxfree).

        lets Δs φs HeqΔs Hsize : (substitution_typing φux h0).
        asserts : (equals Δ Δs). { use_equivalences; autos*. }
        asserts φ' Hsizeφ' : ({φ' :Δ |( b + b' - 0, r + r' )- [x ~> q] u ^ x ∈ A | size φs = size φ'}). {
          apply (typed_subst φs); use_equivalences; autos*; lia.
        }
        exists φ'.
        simpls.
        rewrite <- Hsizeφ'.
        unfolds φux, x, Hxfree.
        lia.
      }
      asserts φf' Hsizeφf': ({φ' : Δ |( b + b' - 0, r + r' )- u ^^ q ∈ A | size φf = size φ'}). {
        apply (typed_subst φf Δ (b + b' - 0) (r + r') (u ^^ q)); 
        try solve[use_equivalences; autos*].
        unfold x.
        rewrite* <- open_subst.
      }
      exists φf'.
      simpls.
      lia.
    + inverts h.
  - gen_eq : (TmAbs t); intro;
    destruct φ eqn:Heq; inverts EQX.
    + split; try lia.
      inverts Hlcp; inverts Hlct.
      pose (x := var_gen (L \u L0 \u fv t \u fv p \u dom Γ)).
      pose (Hxfree := var_gen_spec (E := L \u L0 \u fv t \u fv p \u dom Γ)).
      lets H_b_sup_1 IHφ Hsize : (H (t ^ x) (ltac:(abstract autos)) (p ^ x) (ltac:(abstract autos)) (ltac:(abstract (unfold x; apply* H0))) ltac:(abstract autos) _ _ _ _ (h x (ltac:((unfold x, Hxfree; abstract autos))))).
      asserts φ' Hsizeφ' : (∃ φ' : Γ |( S (b - 1), r )- TmAbs p ∈ {{{{` M `}}|-> ` A `}}, size (T_Fun_b o h) > size φ'). {
        unshelve exists.
        - let l := gather_vars in apply @T_Fun_b with (L := l); 
          try assumption.
          intros y H_y_notin.
          lets φ_rename Hsize_rename : (open_eq_free_typed IHφ y (ltac:(abstract autos)) (ltac:(abstract (unfold x, Hxfree; autos))) (ltac:(abstract autos))).
          assumption.
        - simpls. 
          match goal with 
          | [ |- context[let (_, _) := ?r in _]] => destruct r
          end.
          simpls.
          rewrite <- e.
          match goal with 
          | [ H :  ?der > size_typing_derivation ?φ 
              |- S (?der2) > S (size_typing_derivation ?φ)
            ] => 
              asserts : (der = der2); 
              solve[apply T_Fun_proof_irrelevant | lia]
          end.
      }
      lets φf Hsizeφf : (
          typed_subst φ' Γ (S b - 1) r (TmAbs p) ({{{{` M `}}|-> ` A `}})
            (ltac:(use_equivalences; auto))
            (ltac:(lia))
            (ltac:(reflexivity))
            (ltac:(reflexivity))
            (ltac:(use_equivalences; auto))
      ).
      exists φf. simpls; lia.
    + inverts Hlcp; inverts Hlct.
      pose (x := var_gen (L \u L0 \u fv t \u fv p \u dom Γ)).
      pose (Hxfree := var_gen_spec (E := L \u L0 \u fv t \u fv p \u dom Γ)).
      lets H_b_sup_1 IHφ Hsize : (H (t ^ x) (ltac:(autos)) (p ^ x) (ltac:(autos)) (ltac:(unfold x; apply* H0)) ltac:(autos) _ _ _ _ (h x (ltac:(unfold x, Hxfree; autos)))).
      split*.
      unshelve exists.
      * let l := gather_vars in apply @T_Fun_r with (M := M) (L := l) (A := A); 
        try assumption.
        intros y H_y_notin.
        lets φ_rename Hsize_rename : (open_eq_free_typed IHφ y (ltac:(autos)) (ltac:(unfold x, Hxfree; autos)) (ltac:(autos))).
        assumption.
      * simpls.
        match goal with 
      | [ |- context[let (_, _) := ?r in _]] => destruct r
        end.
        simpls.
        rewrite <- e.
        match goal with 
        | [ H :  ?der > size_typing_derivation ?φ 
            |- S (?der2) > S (size_typing_derivation ?φ)
          ] => 
            asserts : (der = der2); 
            solve[apply T_Fun_proof_irrelevant | lia]
        end.
  - gen_eq : (TmApp t u); intro;
    destruct φ eqn:Heq; inverts EQX.
    + inverts Hlct; inverts Hlcp.
      lets Hbge1 φ' Hsizeφ : (H t ltac:(abstract (simpls; autos*)) p ltac:(assumption) ltac:(assumption) ltac:(assumption) _ _ _ _ h).
      split; try lia.
      asserts φ'' Hsizeφ'' : (∃ φ'0 : Δ |( (b - 1) + b', r + r' )- TmApp p u ∈ A, size (T_App_b o o0 e h h0) > size φ'0). {
        unshelve exists.
        - apply @T_App_b with (M := M) (Γ₁ := Γ₁) (Γ₂ := Γ₂); assumption.
        - simpls; lia. 
      }
      asserts φf Hsizeφf: (∃ φ'0 : Δ |( b + b' - 1, r + r' )- TmApp p u ∈ A, size φ'' = size φ'0). {
        destruct (typed_subst φ'' Δ (b + b' - 1) (r + r') (TmApp p u) A) as [φf Hsizeφf]; try solve[
          use_equivalences; autos; lia
        ].
        exists φf. assumption.
      }
      exists φf. lia.
    + inverts Hlct; inverts Hlcp.
      lets Hbge1 φ' Hsizeφ : (H t ltac:(abstract (simpls; autos*)) p ltac:(assumption) ltac:(assumption) ltac:(assumption) _ _ _ _ h).
      split; try lia.
      unshelve exists.
      * apply T_App_hd_r. assumption.
      * simpls. lia.
Qed.


Inductive reduce_k : nat -> term -> term -> Prop :=
| RK_self : ∀ t, reduce_k 0 t t
| RK_Suc : 
  ∀ k t t' p, 
  t --> t' -> 
  reduce_k k t' p -> 
  reduce_k (S k) t p
.

Hint Constructors reduce_k : head_eval_hints.

(* Thm 3.7 *)
Theorem tight_correctness : 
  ∀ Γ b r t A (φ :Γ |(b, r)- t ∈ A),  
  ∃ p k, 
      reduce_k k t p 
  /\  k <= b 
  /\  normal p
  /\  size p + k <= size φ 
  /\  (tight φ -> b = k /\ size p = r /\ A = Ty_Tight TC_Neutral -> neutral p)
.
Proof.
  (* TODO: Récurrence sur la taille de φ *)
  (* induction φ.
  - exists (TmFVar x) 0; reduce_max; autos*.
  - pick_fresh x.
    asserts Hxfree : (x \notin L \u fv t \u dom Γ). { autos. } 
    lets t' k H_red_t H_k_le_b [H_norm_t' [H_size_der H_tight_imp]] : (
      H x Hxfree
    ).
    exists (TmAbs ([x ~> (TmBVar 0)]t')) k; reduce_max; autos.
      + admit.
      + apply Normal_Abs with (L := L).
        intros. unfold "^". admit.
      + simpl. 
        asserts : (size ([x ~> TmBVar 0] t') = size t'). {
          repeat match goal with 
          | H : _ |- _ => try clear H 
          end.
          gen t'.
          repeat match goal with 
          | H : _ |- _ => try clear H 
          end.
          gen x.
          repeat match goal with 
          | H : _ |- _ => try clear H 
          end.
          induction t'; simpls*.
          case_if*.
        }
        simpls.
        rewrite TEMP.
        match goal with 
        | [H : ?ineq<= ?size_der |- S (?ineq) <= S (?size_der2)] => asserts : (size_der = size_der2);
        try solve[apply T_Fun_proof_irrelevant | lia]
        end.
      + simpls; intros [F _]; false.
  - lets t' k H_red_t H_k_le_b [H_norm_t' [H_size_der H_tight_imp]] : IHφ. admit.
  - pick_fresh x.
    asserts Hxfree : (x \notin L \u fv t \u dom Γ). { autos. } 
    lets t' k H_red_t H_k_le_b [H_norm_t' [H_size_der H_tight_imp]] : (
      H x Hxfree
    ).
  - admit.
  - admit. *)
Admitted.

(* Prop 3.8, OK *)
Theorem normal_forms_tightly_typable :
  ∀ t, 
  lc t ->
  normal t -> 
  (
    ∃ Γ A (φ : Γ |(0, size t)- t ∈ A), 
        tight φ
    /\  (neutral t -> A = Ty_Tight TC_Neutral)
    /\  (abs t -> A = Ty_Tight TC_Abs)
  ).
Proof.
  introv Hlc Hnorm.
  induction Hnorm.
  - inductions H.
    + asserts: (
      equals 
        (add empty x {{` (Ty_Tight TC_Neutral) `; nil}}) 
        (add empty x {{` (Ty_Tight TC_Neutral) `; nil}})
      ). { use_equivalences; autos. }

      exists (add empty x {{`Ty_Tight TC_Neutral` ; nil}}) (Ty_Tight TC_Neutral).
      unshelve exists.
      * apply T_Ax. assumption. 
      * repeat (
          reduce_max || case_if || intro || simpls 
          || unfold tight || unfold add || unfold empty || unfold Tightable_der 
          || unfold Tight_type || unfold Tight_multitype || unfold Tightable_context
        ); autos*.
    + inverts Hlc.
      lets Γ A φ [Htight [Hneuttight Hneutabs]]: (IHneutral H3).
      exists Γ (Ty_Tight TC_Neutral).
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
    lets Γ A φ [Htight [Hneuttight Hneutabs]] : (H0 x (ltac:(auto)) (H2 x)).
    lets H' : (H x ltac:(auto)).
    exists Γ.
    asserts  [Hneut | Habs]: (neutral (t ^ x) \/ abs (t ^ x)). { 
        destruct* t; unfold "^" in *; simpls*;
        case_if*.
    }
    + apply Hneuttight in Hneut; substs.
      exists (Ty_Tight TC_Abs).
      simpls.
      asserts φ' : (add Γ x {{nil}} |( 0, size_aux_term t )- t ^ x ∈ Ty_Tight TC_Neutral). {
        destruct (
          typed_subst φ (add Γ x {{nil}}) 0 (size_aux_term t) (t ^ x) (Ty_Tight TC_Neutral)) as [φ' _];
          use_equivalences; 
          autos*;
          try rewrite* <- size_open; 
          try rewrite* add_nil.
      }
      asserts HokΓ : (ok Γ). {
        rewrite add_nil in *.
        apply (typed_ok φ').
      } 
      unshelve exists.
      * apply @T_Fun_r with
          (L := L \u fv t) 
          (A := Ty_Tight TC_Neutral) 
          (M := {{nil}}).
        -- assumption.
        -- simpls*.
        -- simpls*.
        -- intros. destruct (open_eq_free_typed φ' x0); try assumption.
         ++ admit. (* Pas prouvable *)
         ++ reduce_max; autos.
      * reduce_max; autos*.    
    + admit. 
Admitted. 

(* Lemme 3.9 *)
Lemma anti_substitution_and_typing :
  ∀ {Γ b r t x p A} (φ : Γ |(b, r)- [x ~> p] t ∈ A),
  lc p ->
  ∃   
      (M : multitype)
      (bₜ bₚ rₜ rₚ : nat)
      (Γₜ Γₚ : ctx)
      (φₜ : add Γₜ x M |(bₜ, rₜ)- t ∈ A)
      (φₚ : Γₚ |(bₚ, rₚ)- p ∈ₘ M),
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
      exists {{A; nil}} 0 0 0 0. exists empty Δ.
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
      exists {{nil}}. exists 0 0 0 0. 
      exists Δ empty.
      unshelve exists; autos*.
      ++ apply T_Ax. rewrite add_nil. assumption.
      ++ simpls; inverts x; reduce_max; 
        use_equivalences; hint ok_eq, ok_empty, ok_add;
        try rewrite union_empty_r; autos*.
  - inverts φ0; destruct t; simpls; try case_if; 
    try solve[false*].
    + admit.
    + admit.
  - inverts φ0; destruct t; simpls; try case_if; 
    try solve[false*]; admit.
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
    admit.
  - unfold "^^". apply fv_open.
  - intros z Hin. reduce_max; autos*.
    left.
    specialize H with t1 p0.
    apply* H.    
Admitted.




(* Prop 3.10 *)
Theorem quantitative_subject_expansion :
  ∀ t p,
  lc t ->
  t --> p -> 
  ∀ Γ b r  A (φ : Γ |(b, r)- p ∈ A),
  ∃ (φ' : Γ |(S b, r)- t ∈ A),
  size φ' > size φ
.
Proof.
  intro t.
  induction t using term_size_ind; destruct t; intros * Hlc Hst *; inverts Hst.
  - remember (TmAbs p0) as ter. destruct φ eqn:Heq; 
    inverts Heqter.
    + pick_fresh x.
      inverts Hlc.
      lets φ' Hsizeφ' : (
        H (t ^ x) (ltac:(autos))  (p0 ^ x) (H2 x) (H1 x (ltac:(autos))) 
          _ _ _ _ (h x (ltac:(autos)))
      ).
      unshelve exists. 
      * let l := gather_vars in apply @T_Fun_b with (L := l); try assumption.
        intros y Hnotin.
        lets φf Hsizeφf : (open_eq_free_typed φ' y); autos.

      * simpls.
        match goal with 
        | [ |- context[let (_, _) := ?r in _]] => destruct r
        end.
        simpls.
        rewrite <- e.
        match goal with 
        | [H : size_typing_derivation ?φ > ?der |- S (size_typing_derivation ?φ) > S (?der2)] => asserts : (der = der2); try solve[apply T_Fun_proof_irrelevant | lia]
        end.
    + pick_fresh x.
      inverts Hlc.
      lets φ' Hsizeφ' : (
        H (t ^ x) (ltac:(autos))  (p0 ^ x) (H2 x) (H1 x (ltac:(autos))) 
          _ _ _ _ (h x (ltac:(autos)))
      ).
      unshelve exists. 
      * let l := gather_vars in apply @T_Fun_r with (L := l) (A := A) (M := M); try assumption.
        intros y Hnotin.
        lets φf Hsizeφf : (open_eq_free_typed φ' y); autos.
      * simpls.
        match goal with 
        | [ |- context[let (_, _) := ?r in _]] => destruct r
        end.
        simpls.
        rewrite <- e.
        match goal with 
        | [H : size_typing_derivation ?φ > ?der |- S (size_typing_derivation ?φ) > S (?der2)] => asserts : (der = der2); try solve[apply T_Fun_proof_irrelevant | lia]
        end.
  - pick_fresh x.
    asserts Heq : (u ^^ t2 = [x ~> t2](u ^ x) ).
    { rewrite* <- open_subst. }
    inverts Hlc.
      lets φ' Hsizeφ' : (typed_subst φ Γ b r ([x ~> t2](u ^ x)) A); try solve[use_equivalences; autos].
    lets M bₜ bₚ temp : (
      anti_substitution_and_typing 
        φ' 
        (ltac:(assumption))
    ).
    lets rₜ rₚ Γₜ Γₚ temp2 : temp; clear temp.
    lets φₜ φₚ HeqΓ HokΓ [Heqb [Heqr Heqsize]] : temp2; clear temp2.
    asserts HokΓₚ: (ok Γₚ). {
      apply* (multityped_ok φₚ). 
    }
    asserts φf Hsizeφf : (∃ φ'0 : Γ |( S (bₜ + bₚ), rₜ + rₚ )- TmApp (TmAbs u) t2 ∈ A, size φ'0 > size φ). {
      unshelve exists.
      - change ( S (bₜ + bₚ)) with ( S bₜ + bₚ).
        apply  @T_App_b with (M := M) (Γ₁ := Γₜ) (Γ₂ := Γₚ); 
        try assumption.
        let l := gather_vars in eapply @T_Fun_b with (L := l). 
        + assumption.
        + intros y Hnotin.
          apply* (open_eq_free_typed φₜ).
          admit.
      - simpls.
        match goal with 
        | [ |- context[let (_, _) := ?r in _]] => destruct r
        end.
        simpls; lia.
    }
    lets φf' Hsizeφf' : (typed_subst φf Γ (S b) r (TmApp (TmAbs u) t2) A); try solve[use_equivalences; autos].
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
  - admit.
Admitted.   


Lemma lc_step :
  ∀ t t', 
  lc t -> t --> t' -> lc t'.
Proof.
  induction t using term_size_ind; destruct t; introv Hlc Hstep; 
  inverts Hlc; inverts Hstep.
  - constructor. intros. apply H with (t' := t ^ x).
    + unfold lt_type; rewrite <- size_for_ind_open. apply le_refl.
    + apply H1. 
      (* rewrite* <- (freevars_step t p). *)
    + apply* step_open_vars. admit.
  -  admit.
Admitted.

(* Thm 3.11 *)
Theorem tight_completeness :
  ∀ k t p,
  lc t ->
  reduce_k k t p ->
  normal p ->
  ∃ Γ A (φ : Γ |(k, size p)- t ∈ A),
      tight φ
  /\  (neutral p -> A = Ty_Tight TC_Neutral)
  /\  (abs t -> A = Ty_Tight TC_Abs)
.
Proof.
  introv Hlc Hred Hnorm.
  inductions Hred; try solve [apply* normal_forms_tightly_typable].
  destruct IHHred as [Γ [A [φ [IHtight [IHneut IHabs]]]]]; try solve[hint lc_step; autos*].
  lets φ' Hsize : (quantitative_subject_expansion _ _ Hlc H _ _ _ _ φ).
  exists Γ A φ'; unfold tight, Tightable_der in *; reduce_max; autos*.
  intro Habst'.
  inverts Habst'.
  inverts H.
  apply* IHabs.
Qed.
Print Assumptions quantitative_subject_expansion.
  Print Assumptions tight_completeness.
