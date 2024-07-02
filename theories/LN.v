From Coq Require Import Unicode.Utf8_core.
From TLC Require Import LibLN LibTactics LibFset.
From TTSB Require Import Types Context.
From Coq Require Import Lia.


Ltac auto_tilde :=
  try (solve[ auto with head_eval_hints
            | intuition auto with head_eval_hints ]).

Ltac auto_star ::= 
  try (solve [ eauto with head_eval_hints 
             | jauto 
             | intuition eauto with head_eval_hints ]).

Inductive term := 
  | TmBVar : nat -> term 
  | TmFVar : var -> term 
  | TmAbs : term -> term 
  | TmApp : term -> term -> term 
.



Reserved Notation "{ k ~> u } t" (at level 67).
Fixpoint open' (k : nat) (u : term) (t : term) : term :=
  match t with 
  | TmBVar i => If i = k then u else t 
  | TmFVar y => t
  | TmAbs t' => TmAbs ({ (S k) ~> u } t')
  | TmApp t1 t2 => TmApp ({k ~> u} t1) (({k ~> u} t2))
  end
  where 
  "{ k ~> u } t" := (open' k u t)
  .

Definition open : term -> term -> term := open' 0.
Notation " t ^^ u " := (open u t) (at level 67).
Notation " t ^ x " := (open (TmFVar x) t).

Inductive lc : term -> Prop :=
  | LCFVar : 
      ∀ (x : var), 
      lc (TmFVar x) 
  | LCAbs : 
      ∀ (t : term), 
      (∀ (x : var), lc (t ^ x)) -> 
      lc (TmAbs t)
  | LCApp : 
      ∀ (t1 t2 : term),
      lc t1 -> lc t2 ->
      lc (TmApp t1 t2)
.

Hint Constructors lc : head_eval_hints.

Fixpoint fv (t : term) : vars :=
  match t with 
  | TmBVar _ => \{}
  | TmFVar x => \{x}
  | TmAbs t' => fv t'
  | TmApp t1 t2 => fv t1 \u fv t2
  end.


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
      (∀ (x : var), normal (t ^ x)) -> 
      normal (TmAbs t)
.
Hint Constructors normal : head_eval_hints.

Inductive abs : term -> Prop :=
(* Voir si besoin LC *)
  | Abs : ∀ (t : term), abs (TmAbs t)
.
Hint Constructors abs : head_eval_hints.


Reserved Notation "[ x ~> u ] t" (at level 67).
Fixpoint subst (x : var) (u : term) (t : term) : term := 
  match t with 
  | TmBVar i => t
  | TmFVar y => If x = y then u else t
  | TmAbs t' => TmAbs ([x ~> u] t')
  | TmApp t1 t2 => TmApp ([x ~> u] t1) ([x ~> u] t2)
  end
  where "[ x ~> u ] t" := (subst x u t)
  .

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
  let C := gather_vars_with (fun x : ctx => let (s, f) := x in s) in 
  let D := gather_vars_with (fun x : term => fv x) in 
  constr:(A \u B \u D).

Ltac pick_fresh x :=
  let L := gather_vars in pick_fresh_gen L x.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) := 
  apply_fresh_base T gather_vars x.

Lemma open_eq :
  ∀ (x : var) (t₁ t₂ : term), 
  x \notin fv t₁ \u fv t₂ -> 
  t₁ ^ x = t₂ ^ x -> 
  t₁ = t₂.
Proof.
  unfold "^".
  generalize 0.
  introv.
  gen n x t₂.
  induction t₁; introv Hnotin Heq.
  - destruct* t₂.
    + destruct n; destruct* n0;
      unfold "^" in *; simpl in *;
      repeat case_if*; substs*.
    + destruct n;
      unfold "^" in *; simpl in *;
      repeat case_if*;
      inversion Heq; substs;
      apply notin_union_r2 in Hnotin;
      apply notin_singleton in Hnotin;
      autos*.
    + destruct n;
      unfold "^" in *; simpl in *;
      repeat case_if*.
    + destruct n;
      unfold "^" in *; simpl in *;
      repeat case_if*.
  - destruct t₂; unfold "^" in *; simpl in *;
    repeat case_if*; inverts* Heq.
    apply notin_union_r1 in Hnotin.
    apply notin_singleton in Hnotin.
    false*.
  - destruct t₂; unfold "^" in *; simpl in *;
    repeat case_if*; inverts* Heq.
    fequals*.
  - destruct t₂; unfold "^" in *; simpl in *;
    repeat case_if*; inverts* Heq.
    fequals*.
    applys* (IHt₁1 n x).
    applys* (IHt₁2 n x).
Qed.


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
end : head_eval_hints.



Lemma step_open : 
  ∀ t t' x, 
  t --> t' ->
  ∃ t'', t ^ x --> t''.
Proof.
  unfold "^".
  generalize 0.
  intros n t; gen n; induction* t; introv Hstep; inverts* Hstep; simpls*.
  - apply IHt with (n := S n) (x := x) in H0 as [t'' Hst].
    eexists.
    unfold "^".
    simpls.
    applys* ST_Abs.
  - apply IHt1 with (n := n) (x := x) in H3 as [t'' Hst]. 
    eexists.
    applys* ST_App.
    destruct* t1; simpls; try case_if*.
    intro.
    inversion H.
  Qed.
  

Lemma open_irrelevant :
  ∀ t t' x, 
  (t ^ x) --> (t') -> 
  ∃ t'', t --> t''.
Proof.
  unfold "^".
  generalize 0.
  intros n t.
  gen n.
  induction* t; introv Hstep; simpls.
  - destruct n; case_if; inverts Hstep.
  - inverts Hstep. 
    edestruct IHt; autos*.
  - inverts Hstep.
    + destruct* t1; simpls; try case_if; inverts H0.
    + destruct* t1; simpls; repeat case_if*; substs*.
      * inversion H3.
      * destruct* (IHt1 _ _ _ H3).
Qed. 

Hint Resolve open_irrelevant : head_eval_hints.


Lemma rel_normal_is_normal : 
  ∀ t, lc t -> rel_normal step t -> normal t.
Proof.
  introv H_lc. 
  unfold rel_normal in *.
  induction* H_lc; intro H_rel_normal.
  + apply Normal_Abs.
    intros.
    applys* H0.
    intros [t' Hstep].
    apply H_rel_normal.
    assert (Hopen := open_irrelevant t t' x Hstep).
    destruct* Hopen as [t'' Hst]; subst.
  + destruct* t1.
    * false*.
    * applys Normal_Neutral. apply Neutral_App. 
      applys* neutral_is_normal_not_abs.
      applys* IHH_lc1.
      introv [a' Hstep].
      applys* H_rel_normal.
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
    induction* Hnormal; intros.
    + gen t'. induction* H; intros; inverts* Hstep.
      inverts* H0.
    + inverts* Hstep.
      inverts* H1.
      pick_fresh x.
      apply step_open with t p x in H3 as [t''].
      applys* (H0 x).
  - induction* t.
Qed.

(* Fixpoint remove_from_context (x: var) (Γ : ctx) :=
  match Γ with 
  | nil => nil
  | (y, mt) :: Γ' => If x = y then remove_from_context x Γ' else (y, mt) :: (remove_from_context x Γ')
  end.

Check map.
Reserved Notation "a '⊎c' b"  (at level 0).
Fixpoint union_ctx (Γ₁ Γ₂ : ctx) : ctx :=
    match Γ₁ with 
    | nil => Γ₂
    | (x, mt) :: Γ₁' =>
        match get x Γ₂ with
        | None => 
            (x, mt) :: (Γ₁' ⊎c (remove_from_context x Γ₂))
        | Some mt' => 
            (x, mt ⊎ mt') :: (Γ₁' ⊎c (remove_from_context x Γ₂))
        end
    end
where
  "a '⊎c' b"  := (union_ctx a b)
.

Notation "a '⊎c' b"  := (union_ctx a b) (at level 0).


Lemma union_ctx_nil_l :
  ∀ (Γ : ctx), 
  (empty ⊎c Γ) = Γ.
Proof.
  rewrite* empty_def.
Qed.
Lemma union_ctx_nil_r :
  ∀ (Γ : ctx), 
  (Γ ⊎c empty) = Γ.
Proof.
  intros.
  induction* Γ.
  unfold union_ctx in *.
  - rewrite* empty_def.
  - destruct a.
    simpls*.
    rewrite* get_empty.
    rewrite empty_def in *.
    simpls*.
    rewrite* IHΓ.
Qed.

Lemma union_ctx_cons :
  ∀ x y E E' (Γ : ctx),
  binds x E (Γ & y ~ E')  ->
  binds x E ((y ~ E') ⊎c Γ).
Proof.
  intros.
  induction Γ;
  unfold binds in *.
  - rewrite* <- empty_def. rewrite union_ctx_nil_r.
    rewrite get_push in H.
    case_var*.
    + rewrite get_single. case_var*.
    + rewrite <- empty_def in *. rewrite* get_empty in H.
      inversion H.
  - destruct a; rewrite cons_to_push.
    rewrite get_push in H.
    case_var. 
    + inversion H; subst.
  Admitted. *)
    


(* Lemma union_ctx_comm :
  ∀ Γ₁ Γ₂ x E,
  binds x (Γ₁ ⊎c Γ₂) E ->
  binds x (Γ₂ ⊎c Γ₁) E.
Proof.
  intros.
  induction* Γ₁; simpls.
  - rewrite <- empty_def. rewrite* union_ctx_nil_r.
  -   
Admitted. *)

Definition is_tight_ctx (Γ : ctx) : Prop :=
  let (_, f) := Γ in 
  ∀ x, 
  is_tight_multitype (f x).

Reserved Notation "Γ '|(' b ',' r ')-' t '∈' T" (at level 70).
Reserved Notation "Γ '|(' b ',' r ')-' t '∈ₘ' T" (at level 70).
Inductive has_type : ctx -> nat -> nat -> term -> type -> Type :=
| T_Ax :
    ∀ {x : var} {A : type},
    (add empty x {{ A ; nil }}) |(0, 0)- TmFVar x ∈ A
| T_Fun_b :
    ∀ {Γ : ctx} {t : term} {M : multitype} {A : type} {x : var} 
      {b r : nat},
    x \notin fv t \u dom Γ ->
    ok Γ ->
    add Γ x M |(b, r)- t ^ x ∈ A ->
    Γ |(S b, r)- TmAbs t ∈ (M |-> A) 
| T_App_b :
    ∀ 
      {Γ₁ Γ₂ Δ : ctx} {t p : term} 
      {M : multitype} {A : type}
      {b r b' r' : nat},
    ok Γ₁ -> ok Γ₂ ->
    eq_ctx (union_ctx Γ₁ Γ₂) Δ -> 
    Γ₁ |(b, r)- t ∈ (M |-> A) ->
    Γ₂ |(b', r')- p ∈ₘ M ->
    Δ |(b + b', r + r')- (TmApp t p) ∈ A
| T_Fun_r :
    ∀ 
      {Γ : ctx} {t : term} {x : var}
      {b r : nat} {A T : type},
    ok Γ ->
    x \notin fv t \u dom Γ ->
    is_tight_type A -> 
    is_tight_type T -> 
    add Γ x {{T; nil}} |(b, r)- t ^ x ∈ A -> 
    Γ |(b, S r)- TmAbs t ∈ Ty_Tight TC_Abs

| T_App_hd_r :
  ∀ {Γ : ctx} {t p : term} {b r : nat},
  Γ |(b, r)- t ∈ Ty_Tight TC_Neutral -> 
  Γ |(b, S r)- TmApp t p ∈ Ty_Tight TC_Neutral

(* | T_Many_Inv :
    ∀ {Γ₁ Γ₂ Δ : ctx} {t : term} {A : type} {mt : multitype} 
      {b₁ b₂ r₁ r₂ : nat},
    ok Γ₁ -> ok Γ₂ ->
    eq_ctx (union_ctx Γ₁ Γ₂) Δ ->
    Δ  |(b₁ + b₂, r₁ + r₂)- t ∈ₘ {{A; mt}} ->
    Γ₂ |(b₂, r₂)- t ∈ₘ mt ->
    Γ₁ |(b₁, r₁)- t ∈ A *)

where 
  "Γ '|(' b ',' r ')-' t '∈' T" := (has_type Γ b r t T)
with  has_many_types : ctx -> nat -> nat -> term -> multitype -> Type :=
  | ManyT_Empty :
      ∀  {t : term},
        empty |(0, 0)- t ∈ₘ {{ nil }}
  | ManyT_Union :
        ∀ {Γ₁ Γ₂ Δ: ctx} {t : term} {A : type} {mt : multitype} {b₁ b₂ r₁ r₂ : nat},
        ok Γ₁ -> ok Γ₂ ->
        eq_ctx (union_ctx Γ₁ Γ₂) Δ ->
        Γ₁ |(b₁, r₁)- t ∈ₘ mt ->
        Γ₂ |(b₂, r₂)- t ∈ A ->
        Δ |(b₁ + b₂, r₁ + r₂)- t ∈ₘ {{A; mt}}
  | ManyT_Inv :
      ∀ {Γ₁ Γ₂ Δ : ctx} {t : term} {A : type} {mt : multitype} 
        {b₁ b₂ r₁ r₂ : nat},
        ok Γ₁ -> ok Γ₂ ->
        eq_ctx (union_ctx Γ₁ Γ₂) Δ ->
        Δ  |(b₁ + b₂, r₁ + r₂)- t ∈ₘ {{A; mt}} ->
        Γ₁ |(b₁, r₁)- t ∈ A ->
        Γ₂ |(b₂, r₂)- t ∈ₘ mt
where
  "Γ '|(' b ',' r ')-' t '∈ₘ' T" := (has_many_types Γ b r t T)
.
Hint Constructors has_many_types has_type : head_eval_hints.
Scheme has_type_mut_ind := Induction for has_type Sort Type
with has_many_types_mut_ind := Induction for has_many_types Sort Type.
Scheme has_type_mut_rec := Induction for has_type Sort Set
with has_many_types_mut_rec := Induction for has_many_types Sort Set.

Lemma bvar_not_typable : 
  ∀ Γ b r n A mt,
  Γ |(b, r)- TmBVar n ∈ₘ {{A; mt}} -> False.
Proof.
  introv φ.
  inductions φ.
  - inversion h.
  - inversion h.
Qed.
  
Lemma fvar_multitype : 
  ∀ s f b r v mt, 
  (s, f) |(b, r)- TmFVar v ∈ₘ mt -> Multitype.eq (f v) mt /\ b = 0 /\ r = 0.
Proof.
  introv φ.
  inductions φ; autos.
  - inversion h; subst.
    destruct Γ₁; unfolds empty, add; repeat case_if; simpls;
    repeat match goal with 
    | [H : _ /\ _ |- _] => destruct H
    end.
    specialize H0 with v.
    case_if.
    Admitted.
    (* apply Multitype.eq_trans with (Multitype.union (m v) {{` A `; nil}}).
    { applys* Multitype.eq_sym. }
    apply Multitype.eq_trans with (Multitype.union {{` A `; nil}} (m v)); simpls*.

    change {{` A `; ` (m v) `}}  with (
        {{ nil }} ⊎ {{` A `; ` (m v) `}} 
    ).
    change {{` A `; ` mt `}}  with (
        {{ nil }} ⊎ {{` A `; ` mt `}} 
    ).
    applys* Multitype.union_insert.
    apply permₜ_refl.
  - inversion h; subst.
    destruct Δ; unfolds empty, add; repeat case_if; simpls;
    repeat match goal with 
    | [H : _ /\ _ |- _] => destruct H
    end.
    specialize H0 with v.
    specialize o with v.
    repeat case_if.
    clear C C0 o.
    specialize IHφ with (v0) (m) v.
    assert (Multitype.eq (m v) {{` A `; ` mt `}}).
    { autos*. }
    assert (∀ A mt1 mt2, 
      Multitype.eq {{A; mt1}} {{A; mt2}} ->
      Multitype.eq {{mt1}} {{mt2}}). admit.
    
    apply H2 with (A := A).
    apply Multitype.eq_trans with ((m v)); simpls*.
Admitted. *)


Lemma T_Many_Inv :
    ∀ {Γ₁ Γ₂ Δ : ctx} {t : term} {A : type} {mt : multitype} 
      {b₁ b₂ r₁ r₂ : nat},
    ok Γ₁ -> ok Γ₂ ->
    eq_ctx (union_ctx Γ₁ Γ₂) Δ ->
    Δ  |(b₁ + b₂, r₁ + r₂)- t ∈ₘ {{A; mt}} ->
    Γ₂ |(b₂, r₂)- t ∈ₘ mt ->
    Γ₁ |(b₁, r₁)- t ∈ A.
Proof.
  introv Hok1 Hok2 Heq_union φₘ₁ φₘ₂.
  induction t.
  - apply bvar_not_typable in φₘ₁. autos*.
  - destruct Δ. apply fvar_multitype in φₘ₁ as [Heq1 [Heq_b1b2 Heq_r1r2]].
    destruct Γ₂. apply fvar_multitype in φₘ₂ as [Heq2 [Heq_b2 Heq_r2]].
    destruct Γ₁.
    simpls.
    destruct Heq_union as [Heq_dom H_eqtype].
    assert ((v2, m1) = add empty v {{A; nil}}) by admit. 
    assert (b₁ = 0 /\ r₁ = 0) as [Hb1 Hr1] by lia; substs.
    rewrite* H.
  - admit. 
  - admit. 
Admitted.

Check has_type_mut_ind.
Goal ∀ Γ b r t A, 
Γ |(b, r)- t ∈ A -> ok Γ.
Proof.
  introv φ.
  induction φ; autos*.
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


Definition δ := TmAbs (TmApp (TmBVar 0) (TmBVar 0)).
Definition Ω := TmApp δ δ.
Goal ¬ normal Ω.
Proof.
  unfold Ω, δ.
  intro.
  inverts* H.
  inverts* H0.
Qed.

Fixpoint size_typing_derivation {b r : nat} {Γ : ctx} {t : term} {T : type} (der : Γ |( b , r )- t ∈ T) : nat :=
    match der with 
      | T_Ax  => 0
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
    size_many_typing_derivation {b r : nat} {Γ : ctx} {t : term} {M : multitype} (der : Γ |( b , r )- t ∈ₘ M) : nat :=
    match der with 
    | ManyT_Empty => 0
    | ManyT_Union _ _ _ der₁ der₂ => size_many_typing_derivation der₁ + size_typing_derivation der₂
    | ManyT_Inv _ _ _  mder der => size_many_typing_derivation mder +  size_typing_derivation der
    end
  .

  Definition is_tight_derivation 
    {b r : nat} {Γ : ctx} {t : term} {T : type} 
    (der : Γ |( b , r )- t ∈ T) : Prop 
  := 
    (is_tight_type T) /\  (is_tight_ctx Γ).


Definition abs_abs := {{ ` Ty_Tight TC_Abs ` ; nil }} |-> Ty_Tight TC_Abs.
Example first_derivation : empty |(3, 1)- example_term ∈ (Ty_Tight TC_Abs).
Proof with eauto using Multitype.eq_refl.
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
  - pick_fresh x.
    
    apply @T_Fun_b with (x := x); simpls~.
    apply @T_App_b with 
      (Γ₁ := add empty x {{ ` Ty_Tight TC_Abs ` ; nil }}) 
      (Γ₂ := add empty x {{ ` abs_abs ` ; nil }}) 
      (b := 1) 
      (b' := 0) 
      (r := 0) 
      (r' := 0)
      (M := {{ abs_abs ; nil}}); repeat case_if; autos~...
    {
      unfold eq_ctx. unfold Context.union_ctx, Context.add, Context.empty. repeat case_if. split.
      - rewrite LibFset.union_empty_l. apply union_same.
      - intros. repeat case_if~...
    }
    repeat case_if. 
    pick_fresh x2.
    apply @T_Fun_b with (x:=x2); simpls~.
    {
      rewrite dom_add;
      repeat (apply notin_union; split); simpls*.
      intro H_contra; inversion H_contra.
    }
    2: replace 0 with (0 + 0); autos*.
    
    apply @T_App_b with 
    (Γ₁ := add empty x2 {{ ` abs_abs ` ; nil }}  )
    (Γ₂ := add empty x  {{ ` Ty_Tight TC_Abs ` ; nil }})
    (b := 0) (b' := 0) (r := 0) (r' := 0) (M := {{ ` Ty_Tight TC_Abs ` ; nil }}); unfold abs_abs; repeat case_if;
    try (change 0 with (0 + 0); autos* ).
    {
      simpls.
      unfold eq_ctx, Context.union_ctx, Context.add, Context.empty. repeat (case_if; try split; try intro); autos*.
      repeat rewrite LibFset.union_empty_l; apply LibFset.union_comm.
    }
    
  - unfold Id.
    change 1 with (1 + 0) at 1.
    change 1 with (0 + 1) at 2.
    apply @ManyT_Union with (A := Ty_Tight TC_Abs) (mt := {{ `abs_abs` ; nil }}) (Γ₁ := empty) (Γ₂ := empty); unfold abs_abs; pick_fresh x; autos.
    + apply @ManyT_Union with 
      (Γ₁ := empty) (Γ₂ := empty) (b₁ := 0) (r₁ := 0); autos.
      * auto_star.
      * apply @T_Fun_b with (x := x); autos*. unfold "^"; simpls.
        case_if*.
    + apply @T_Fun_r 
      with (T := Ty_Tight TC_Abs) (A := Ty_Tight TC_Abs) (x := x); unfold "^"; simpls; repeat case_if; autos*.
Qed.


Ltac derivation_induction der P0 := 
  induction der using has_type_mut_ind with (P0:=P0); unfold P0 in *; clear P0.


Goal ∀ {Γ: ctx} {t : term} {A : type} {b r : nat} (φ : Γ |(b, r)- t ∈ A),
b + r <= size_typing_derivation φ.
Proof.
  intros.
  pose (P0 (Γ: ctx) (b r : nat) (t : term) (M : multitype) (φ : Γ |(b, r)- t ∈ₘ M) := b + r <= size_many_typing_derivation φ).
  derivation_induction φ P0; simpl; lia.
Qed.


Definition last_rule_is_appb 
    {b r : nat} {Γ : ctx} {t : term} {T : type} 
    (der : Γ |( b , r )- t ∈ T) : Prop := 
  match der with 
  | T_Ax => False
  | T_Fun_b _ _ _ => False
  | T_Fun_r _ _ _ _ _ => False
  | T_App_b _ _ _ _ _ => True
  | T_App_hd_r _ => False
  (* | T_Many_Inv _  _ _ _ _ => False *)
  end.


Lemma tight_spreading_var :  
  ∀ {Γ : ctx} {b r : nat} {x : var} {A : type}
    (φ : Γ |( b, r )- TmFVar x ∈ A), 
  is_tight_ctx Γ -> 
  is_tight_type A /\ ¬ last_rule_is_appb φ.
Proof with eauto.
  intros * H_tight.
  split.
  + inversion φ; subst.
    unfold is_tight_ctx, add, empty in H_tight; repeat case_if*.
    specialize H_tight with x; repeat case_if*;
    simpls*.
  + intros * H_contra.
    remember (TmFVar x) as t.
    destruct φ eqn:H_eq...
    inversion Heqt. 
Qed.



Lemma union_tight_ctx :
  ∀ Γ₁ Γ₂ Δ, 
  is_tight_ctx Δ ->
  eq_ctx (union_ctx Γ₁ Γ₂) Δ  ->
  is_tight_ctx Γ₁ /\ is_tight_ctx Γ₂.
Proof.
  intros.
  destruct Γ₁, Γ₂, Δ.
  unfold is_tight_ctx.
  simpls.
  destruct H0.
  split;
  intro x; specialize H with x; specialize H1 with x;
  apply mt_union_tight in H1 as [Htm Htm0]; autos*.
Qed.

Ltac tight_union_ctx Δ :=
  match goal with 
  | [H : eq_ctx (union_ctx ?Γ₁ ?Γ₂) Δ |- _] => 
    let H_tight_Γ₁ := fresh "H_tight_Γ₁" in 
    let H_tight_Γ₂ := fresh "H_tight_Γ₂" in 
      apply union_tight_ctx in H as  [H_tight_Γ₁ H_tight_Γ₂]; eauto 
  end.


Lemma tigh_spreading_on_neutral_terms : 
  ∀ {t : term}, neutral t ->
  ∀ {Γ : ctx} {b r : nat} {A : type}
    (φ : Γ |(b, r)- t ∈ A), 
  is_tight_ctx Γ ->
  is_tight_type A /\ ¬ last_rule_is_appb φ.
Proof with eauto.
  intros t H_neutral.
  induction H_neutral as [ n | x | p u H_neutral_p IH]; intros Γ b r A φ H_tight.
  - inversion φ. 
  - eapply tight_spreading_var...
  - inversion φ; subst...
    + tight_union_ctx Γ.
      apply IH in X; simpls; try contradiction...
    + splits; simpls*...
      remember (TmApp p u) as t.
      remember (Ty_Tight TC_Neutral) as T.
      destruct φ eqn:Heq; simpl; inversion Heqt; subst...
      tight_union_ctx Δ.
      apply IH with (φ := h) in H_tight_Γ₁ as [H_contra _]; simpl in *; contradiction.
Qed.

Fixpoint size t :=
  match t with 
  | TmBVar _ | TmFVar _ => 0
  | TmAbs t' => S (size t')
  | TmApp t₁ t₂ => S (size t₁)
  end.


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
  induction* t; intros; simpls*; repeat case_if*.
Qed.

Hint Resolve size_open : head_eval_hints.

Lemma normal_size_derivation : 
  ∀ {t : term} {Γ : ctx} {b r : nat} {A : type} 
    (φ : Γ |(b, r)- t ∈ A), 
  normal t -> 
  size t <= size_typing_derivation φ.
Proof with try lia.
  intros * H_normal_t.
  induction φ; inversion H_normal_t; subst; simpl; try apply IHφ in H0; autos*.
  - inverts* H_normal_t; substs*. rewrite size_open with ( x:= x). 
    specialize H1 with x. apply IHφ in H1. lia.
  - inverts* H; neutral_to_normal t; apply IHφ in H1. lia.
  - inverts* H_normal_t; substs*. rewrite size_open with ( x:= x).
    specialize H1 with x. apply IHφ in H1. lia.
  - inverts* H; neutral_to_normal t; apply IHφ in H1. lia.
Qed.

Ltac use_type_spreading Γ :=
  match goal with 
  | [ H : Γ |(_, _)- _ ∈ {{ {{_}} |-> _}} |- _] => 
      apply tigh_spreading_on_neutral_terms in H; eauto; subst; inversion H
  end. 


Section term_size_ind.  
  Variable P : term -> Prop.

  Hypothesis H : forall t, (forall t', size t' < size t -> P t') -> P t.

  Theorem term_size_ind : forall xs, P xs.
  Proof.
    assert (
      ∀ t t', size t' <= size t -> P t') as H_ind.
      
    { induction t; intros t' Hlen; apply H; intros l0 H0; simpls; try lia.
      - inversion Hlen; subst; apply IHt; lia.
      - inversion Hlen; subst; apply IHt1; lia.
    }
    intros t.
    apply H_ind with (t := t). lia.
  Qed.
End term_size_ind.
Check term_size_ind.

Theorem normal_tight_der_size_b_r :
  ∀ {t : term} {Γ : ctx} {b r : nat} {A : type} 
    (φ : Γ |(b, r)- t ∈ A), 
  normal t -> 
  is_tight_derivation φ -> 
  b = 0 /\ r = size t.
Proof with try lia; eauto using union_tight_ctx.
  induction t using term_size_ind.
  gen H.
  induction t; intros H_ind_size * H_normal_t H_tight_der; destruct H_tight_der as [H_tight_A H_tight_Γ]; inversion φ; subst; simpl; try (inversion H_tight_A; fail)...
  - inversion H_normal_t; subst; try inversion H.
    assert (size (t ^ x) < size (TmAbs t)). 
    { rewrite* <- size_open. }
    specialize H3 with x.
    destruct* (H_ind_size _ H _ _ _ _ X H3).
    { split*. destruct Γ. unfold add. simpls*. case_if. simpls*. intro. case_if. simpls. split*. apply H_tight_Γ. }
    split*.
    rewrite* (size_open t x).
  - assert (is_tight_ctx Γ₁ /\ is_tight_ctx Γ₂) 
      as [H_tight_Γ₁ H_tight_Γ₂]...
    inversion H_normal_t. inversion H; subst.
    use_type_spreading Γ₁.
  - inversion H_normal_t; inversion H; subst.
    assert (b = 0 ∧ r0 = size t1).
    {
      eapply H_ind_size with (φ := X); autos*.
      splits*.
    }
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

Definition is_free_in_context x (Γ : ctx):= 
  let (s, f) := Γ in 
  x \notin s /\ f x = {{nil}}.

Lemma free_subst :
  ∀ t p x y, 
  y <> x ->
  y \notin fv t ->
  y \notin fv p ->
  y \notin fv ([x ~> p]t).
Proof.
  intro.
  induction* t; introv Hneq H_notin_t H_notin_p; 
  simpls*; case_if*.
Qed.


(* Goal 
  ∀ 
    (Γ Δ : ctx) (x : var) (M : multitype) 
    (t p : term) (A : type)
    (b b' r r' : nat)
    (φₜ : add Δ x M |(b, r)- t ∈ A)
    (φₚ : Γ |(b', r')- p ∈ₘ M),
    is_free_in_context x Γ ->
    Δ ⊎c Γ |(b + b', r + r')- [x ~> p ]t ∈ A.
Proof.
  introv φₜ.
  gen b' r' Γ p. 
  inductions φₜ; simpls; introv φₚ Hfree.
  - case_if; subst.
    +
      assert ( Δ = empty /\ M = {{A; nil}} ).
      {
        split;
        apply not_not_inv;
        intro.

      }
     inverts x. admit.
    + admit.
  - admit.
  - admit.
  - pick_fresh y.
    eapply T_Fun_r.
    {
      apply free_subst;
      repeat match goal with 
      | [H : y \notin _ \u _ |- _] => 
          apply notin_union in H; destruct H
      end;
      autos*.
    }
    exact i.
    autos*.
    apply IHφₜ. *)
    




(* Lemma substitution_typing :
  ∀ 
    (Γ₁ Γ₂ Δ : ctx) (H_u : eq_ctx (Γ₁ ⊎c Γ₂) Δ) (M : multitype) 
    (b r b' r' : nat) (t p : term) (A : type) (x : var) 
    (φₜ : M :: Γ₁ |(b, r)- t ∈ A) (φₚ : Γ₂ |(b', r')- p ∈ₘ M),
    Δ |(b + b', r + r')- lower 0 <{[0 <- p]t}> ∈ A
    (* (φ : Δ |(b + b', r + r')- lower 0 <{t[0 <- p]}> ∈ A),
    size_typing_derivation φ = size_many_typing_derivation φₚ + size_typing_derivation φₜ - Multitype.size M *)
  .
Proof with eauto with arith.
  intros.
  induction φₜ eqn:Heqt.
  - induction φₚ eqn:Heqp; simpl.
    + admit.  
    + admit.  
  
Admitted. *)
(* End HeadTypingSystem. *)

