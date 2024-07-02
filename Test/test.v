Require Import Unicode.Utf8_core.
Require Import String.
Inductive term := 
| Var : string -> term
| Abs : string -> term -> term 
| App : term -> term -> term
.
Declare Custom Entry term.



Notation "<{ e }>" := e (e custom term at level 99).
Notation "( e )" := e (in custom term, e at level 99).
Notation "x" := x (in custom term at level 0, x constr at level 0).
Notation " '`' x '`' " := x (in custom term at level 0, x constr at level 0).
Notation " # x " := (Var x) (in custom term at level 0, x constr at level 0).
Notation "x y" := (App x y) (in custom term at level 1, left associativity).
Notation "'λ' x ',' t" :=
  (Abs x t) 
  (
    in custom term at level 90, 
    x constr at level 99,
    t custom term at level 99,
    no associativity
  ).

Definition x := "x"%string.
Check <{ λ x, #x }>.

Search ({_ = _} + {_ ≠ _})%string.

Reserved Notation "[ x ~> u ] t" (at level 67).
Fixpoint sub (s : term) (x : string) (t : term) :=
  match t with 
  | <{ #y }> => if string_dec x y then s else Var x
  | <{ λ y, t' }> => if string_dec x y then t else <{ λ y, ` [ x ~> s ] t' `}>
  | <{ t1 t2 }> => <{ ` [ x ~> s ] t1 ` ` [ x ~> s ] t2 ` }>
  end
  where "[ x ~> u ] t" := (sub u x t)
  .

Reserved Notation "a --> b" (at level 0).
Inductive step : term -> term -> Prop := 
| ST_App : 
  ∀ u u' v, 
  u --> u' ->
  <{u v}> --><{u' v}>
| ST_Beta :
  ∀ x u v, 
  <{ (λ x, u) v}> --> (sub v x u)
where 
  "a --> b" := (step a b)
.

Reserved Notation "a -->* b" (at level 0).
Inductive multistep : term -> term -> Prop :=
| MS_Self :
    ∀ t, t -->* t
| MS_Trans :
    ∀ t1 t2 t3, 
    t1 --> t2 ->
    t2 -->* t3 ->
    t1 -->* t3
where 
  "a -->* b" := (multistep a b)
.

Fixpoint eval (n : nat) (t : term) :=
  match n with 
  | 0 => None 
  | S n => 
    match t with 
    | <{ #y }> => Some t
    | <{ λ y, t' }> => Some t
    | <{ t1 t2 }> =>
        match eval n t1 with 
        | None => None 
        | Some <{ λ x, t1' }> => eval n ([x ~> t2] t1)
        | Some t1' => Some <{t1' t2}>
        end
    end
  end.

Lemma multistep_app :
  ∀ t1 t1' t2,
  t1 -->* t1' -> 
  <{t1 t2}> -->* <{t1' t2}>.
Proof.
  intros.
  induction H.
  - apply MS_Self.
  - apply MS_Trans with (t2 := <{ ` t0 ` ` t2 ` }>).
    + apply ST_App. assumption.
    + assumption.
Qed.

Lemma multistep_trans :
  ∀ t1 t2 t3, 
  t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof with eauto.
  intros * Hms1 Hms2.
  induction Hms1...
  eapply MS_Trans...
Qed.


Ltac remove_absurd :=
  try match goal with 
  | [H : None = Some _ |- _] => inversion H
  end.
Goal 
  ∀ t t' n, 
  eval n t = Some t' -> 
  t -->* t'.
Proof.
  intro t.
  induction t; intros.
  - destruct n; inversion H.
    apply MS_Self.
  - destruct n; inversion H.
    apply MS_Self.
  - destruct n; inversion H.
    destruct (eval n t1) eqn:Heq; remove_absurd.
    destruct t.
    + apply IHt1 in Heq.
      inversion H1.
      apply multistep_app. assumption.
    + apply IHt1 in Heq.
      eapply multistep_trans.
      * apply multistep_app.
        exact Heq.
      * eapply MS_Trans.
        -- apply ST_Beta.
        -- Axiom F : False. exfalso; exact F.
    + apply IHt1 in Heq.
      inversion H1.
      apply multistep_app. assumption.
Qed.
