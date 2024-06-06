(* From Coq Require Import Unicode.Utf8_core.


Inductive Context : nat -> Set :=
  | C_Empty : Context 0
  | C_Cons : ∀ {n : nat}, nat -> Context n -> Context (S n)
  .

Equations sum {n : nat} (g1 g2 : Context n) : Context n :=
sum C_Empty C_Empty := C_Empty ;
sum (C_Cons h1 t1) (C_Cons h2 t2) := C_Cons (h1 + h2) (sum t1 t2).

Compute sum (C_Cons 1 C_Empty) (C_Cons 4 C_Empty).


(*
From Coq Require Import Unicode.Utf8_core.
From TLC Require Import LibLN.
From TLC Require Import LibFset.
Require Import EvaluationSystem.

Inductive trm : Set := 
| trm_bvar : nat -> trm 
| trm_fvar : var -> trm 
| trm_app : trm -> trm -> trm 
| trm_abs : trm -> trm 
.

Declare Custom Entry term.
Notation "<{ t }>" := t (t custom term at level 99).
Notation "( x )" := x (in custom term, x at level 99).
(* Notation "x" := x (in custom term at level 0, x constr at level 0). *)
Notation "x" := x (in custom term at level 0, x constr at level 0).
Notation "'$' x '$'" := x (in custom term at level 0, x constr at level 0).
Notation "'#' n" := (trm_bvar n) (in custom term at level 0, n constr).
Notation "'@' x" := (trm_fvar x) (in custom term at level 0).
Notation "x  y" := (trm_app x y) (in custom term at level 2, left associativity).
Notation "'λ' t" := (trm_abs t) (
  in custom term at level 90, 
  t custom term at level 99,
  left associativity
).


Parameter Y : var.
Definition demo_rep1 := trm_abs (trm_app (trm_fvar Y) (trm_bvar 0)).

Eval compute in demo_rep1.


(* Supposing u is locally closed: all indices are bound to an abstraction, Attention: bien fermer les termes sur les propriétés *)
Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | <{ #i }>     => If k = i then u else <{ #i }>
  | <{ @x }>    => <{ @x }>
  | <{ λ t1}>    => <{ λ $ (open_rec (S k) u t1) $ }>
  | <{ t1 t2 }> => <{ $(open_rec k u t1)$ $(open_rec k u t2)$ }>
  end.

Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (trm_fvar x)).


Lemma demo_open :
  (trm_app (trm_abs (trm_app (trm_bvar 1) (trm_bvar 0))) (trm_bvar 0)) ^ Y =
       (trm_app (trm_abs (trm_app (trm_fvar Y) (trm_bvar 0))) (trm_fvar Y)).
Proof.
  unfold "^". unfold "{ a ~> b } c". repeat case_if. reflexivity.
Qed.

Inductive term : vars -> trm -> Prop :=
  | term_var : ∀ (L : vars) (x : var),
      x \in L ->
      term L <{ @x }> 
  | term_abs : ∀ (L : vars) (t : trm) (x : var),
      x \notin L -> term (L \u \{x}) (t ^ x) ->
      term L <{ λ t }>
  | term_app : ∀ (L : vars) (t₁ t₂ : trm),
      term L t₁ ->
      term L t₂ ->
      term L <{ t₁ t₂ }>.



Inductive neutral : vars -> trm -> Prop :=
| Neutral_FVar : ∀ (L : vars) (v : var), term L <{@v}> -> neutral L <{ @v }>
| Neutral_App : 
  ∀ (L : vars) (t p : trm), 
  neutral L t -> 
  term L p ->
  neutral L <{ t p }>
.
Inductive normal : vars -> trm -> Prop := 
| Normal_Neutral : ∀ (L : vars) (t : trm), neutral L t -> normal L t 
| Normal_Abs : 
    ∀ (L : vars) (t : trm) (x : var),
    x \notin L -> normal (L \u \{x}) (t ^ x) -> 
    normal L (trm_abs t) 
.
Hint Constructors term : core.
Hint Constructors neutral : core.
Hint Constructors normal : core.

Lemma neutral_is_term : ∀ L t, neutral L t -> term L t.
Proof with eauto.
  intros * H_neut.
  induction t; subst; inversion H_neut; subst...
Qed.
Hint Resolve neutral_is_term : core.

Lemma normal_is_term : ∀ L t, normal L t -> term L t.
Proof with eauto.
  intros * H_norm;
  induction H_norm...
Qed.
  
Hint Resolve normal_is_term : core.



Inductive abs : vars -> trm -> Prop := 
| Abs : ∀ (L : vars) (t : trm), term L <{ λ t }> -> abs L  <{ λ t }>
. 
Hint Constructors abs : core.


Fixpoint fv (t : trm) {struct t} : vars :=
  match t with
  | <{ #i }>    => \{}
  | <{ @x }>    => \{x}
  | <{ λ t }>    => (fv t)
  | <{ t₁ t₂ }> => (fv t₁) \u (fv t₂)
  end.

Reserved Notation "a '-[' L ']->' b" (at level 0).
Inductive step : vars -> trm -> trm -> Prop :=
| ST_Beta : 
    ∀ (L : vars) (u q : trm), 
    term L <{ λ  u }> -> 
    term L q -> 
    <{ (λ u) q }> -[ L ]-> (u ^^ q)
| ST_Abs : ∀ (L : vars) (t p : trm) (x : var),
    x \notin L -> (t ^ x) -[ (L \u \{x}) ]-> (p ^ x) -> 
    <{ λ t }> -[ L ]-> <{ λ p }>
| ST_App : 
  ∀ (L : vars) (t p u : trm), 
    term L u ->
    ¬ abs L t -> 
    t -[ L ]-> p ->
    <{t u}> -[ L ]-> <{p u}>
where 
  "a -[ L ]-> b" := (step L a b)
.
Hint Constructors step : core.



Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  (* let C := gather_vars_with (fun x : ctx => dom x) in *)
  let D := gather_vars_with (fun x : trm => fv x) in
  (* constr:(A \u B \u C \u D). *)
  constr:(A \u B \u D).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Ltac reduce_notin_union := 
  match goal with
  | [ H : _ \notin (_ \u _) |- _] =>  apply notin_union in H; destruct H 
  end.

Theorem open_eq : 
  ∀ (v : nat) (x : var) (t₁ t₂ : trm),
  x \notin (fv t₁ \u fv t₂) -> {v ~> trm_fvar x} t₁ = {v ~> trm_fvar x} t₂ -> t₁ = t₂.
Proof with eauto.
  intros *.
  generalize dependent v.
  generalize dependent x.
  generalize dependent t₂.
  induction t₁; intros.
  - destruct n.
    + unfold "^" in *. simpl in *. case_if. destruct t₂; inversion H0. 
      * case_if. destruct n... subst... 
      * simpl in *. reduce_notin_union. apply notin_singleton in H1.
        contradiction.
      * destruct t₂; inversion H0; destruct n; case_if... 
    + reduce_notin_union; unfold "^" in *. simpl in *. case_if.
      destruct t₂; inversion H0; try destruct n0; try case_if; subst...
      apply notin_singleton in H1. contradiction.
      destruct t₂; inversion H0. destruct n0; case_if... 
  - unfold "^" in *. simpl in *. destruct t₂; inversion H0; 
    reduce_notin_union...
    case_if. apply notin_singleton in H. inversion H2; symmetry in H4. contradiction.
  - unfold "^" in *. simpl in *. destruct t₂; inversion H0; 
    try case_if.
    fequals;
    [eapply IHt₁1 | eapply  IHt₁2]; eauto;
    simpl in H; repeat reduce_notin_union...
  - unfold "^" in *. simpl in *. destruct t₂; inversion H0; 
    try case_if.
    fequals...
Qed.
Hint Resolve open_eq : core.

Ltac abs_not_abs := 
  match goal with 
  | [H : ¬ abs _ (trm_abs _) |- _] => exfalso; apply H; apply Abs
  end.
Theorem deterministic_step : ∀ (L : vars), deterministic (step L).
Proof with eauto.
  unfold deterministic.
  intros *.
  intro H.
  generalize dependent a₂.
  induction H; intros; 
  try (match goal with 
  | [H : step _ _ _ |- _] => inversion H; subst; try f_equal; try abs_not_abs
  end; eauto; fail).
  inversion H1; subst...
  repeat reduce_notin_union.
  assert (p ^ x = p0 ^ x).
  apply IHstep...
  fequals.
  specialize H4 with x.
  eapply open_eq with _ x...
Qed.
Hint Resolve deterministic_step : core.

(* Definition multistep : trm -> trm -> Prop := reflexive_closure (transitive_closure step).
Notation "a -->* b" := (multistep a b) (at level 0). *)

Fixpoint size (t : trm) : nat := 
  match t with
  | <{ #_ }> => 0 
  | <{ @_ }> => 0 
  | <{λ t}> 
  | <{ t _ }> => 1 + size t
  end.
Hint Unfold size  : HeadEvaluation.

Ltac solve_var_in_union := 
  match goal with 
  | [ |- term _ (trm_fvar _)] => apply term_var; solve_var_in_union
  | [ |- _ \in \{ _ }] => rewrite in_singleton; eauto
  | [ |- _ \in _ \u _ ] => rewrite in_union; try (left; solve_var_in_union; fail); try (right; solve_var_in_union; fail)
  end.

Goal <{(λ λ (#1) (#0)) (λ #0)}> -[\{}]-> <{ λ (λ # 0) # 0 }>.
Proof with eauto.
assert (H_eq : <{ λ (λ # 0) # 0 }> = <{ λ (#1) (#0)}> ^^ <{λ #0}>).
{ unfold open, open_rec in *. repeat case_if... }
rewrite H_eq.
apply ST_Beta.
- pick_fresh x.  apply term_abs with x... 
  pick_fresh x'. apply term_abs with x'... repeat case_if.
  apply term_app; try case_if; apply term_var; solve_var_in_union.
- pick_fresh x. apply term_abs with x... intros. unfold open, open_rec. case_if. solve_var_in_union.
Qed.

Lemma neutral_is_normal_not_abs : ∀ L t, normal L t /\ ¬ abs L t -> neutral L t.
Proof with eauto.
  intros * [H_normal_t H_not_abs_t].
  inversion H_normal_t; subst. assumption. abs_not_abs...
Qed.
Hint Resolve neutral_is_normal_not_abs : core.


Lemma step_normal_is_normal : ∀ (L : vars) (t : trm), term L t -> rel_normal (step L) t -> normal L t.
Proof with eauto.
  intros L t H_term H_rel_normal.
  unfold rel_normal in *.
  induction H_term...
  (* - inversion H_term. *)
  
  - apply Normal_Abs with x... apply IHH_term. 
    intros [a' H_st].
    apply H_rel_normal.
    (* assert (Hst' := H_st). *)
    eexists.
    apply ST_Abs. intros.
    subst.
    admit.
  - induction t1...
    + apply Normal_Neutral. inversion H_term. inversion H1.
    + apply Normal_Neutral. apply Neutral_App... inversion H_term... 
    + apply Normal_Neutral. apply Neutral_App; inversion H_term; subst...
      apply neutral_is_normal_not_abs. split.
      {
        apply IHt1...
        intros [a' Hst].
        apply H_rel_normal...
        exists <{a' t2}>.
        apply ST_App...
        intro H_contra. inversion H_contra.
      }
      {
        intro H_contra. inversion H_contra. 
      }
    + inversion H_term. exfalso...
           
Admitted.

Hint Resolve step_normal_is_normal : core.

Theorem head_red_eval_system :
  evaluation_system trm term step normal neutral abs.
Proof with eauto.
  repeat split...
  - intro H_norm.
    induction H_norm...
    + induction H0; intros [a Hst]; inversion Hst; subst.
      * inversion H0.
      * apply neutral_is_term in H0. apply IHneutral in H0...    
    + intros [a H_st].
      inversion H_st; subst... 
      pick_fresh x.
      repeat reduce_notin_union... eapply H1...
  - intro. inversion H; subst; inversion H0; inversion H1.
Qed. *) *)
