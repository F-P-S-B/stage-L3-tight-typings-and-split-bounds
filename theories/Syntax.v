From Coq Require Import Unicode.Utf8_core.
From TLC Require Import LibLN LibTactics LibFset.
From TTSB Require Import Tactics.



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

Fixpoint fv (t : term) : vars :=
  match t with 
  | TmBVar _ => \{}
  | TmFVar x => \{x}
  | TmAbs t' => fv t'
  | TmApp t1 t2 => fv t1 \u fv t2
  end.

Inductive lc : term -> Prop :=
  | LCFVar : 
      ∀ (x : var), 
      lc (TmFVar x) 
  | LCAbs : 
      ∀ (t : term), 
      (∀ (x : var), (x \notin fv t) -> lc (t ^ x)) -> 
      lc (TmAbs t)
  | LCApp : 
      ∀ (t1 t2 : term),
      lc t1 -> lc t2 ->
      lc (TmApp t1 t2)
.



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


Lemma open_eq :
  ∀ (x : var) (t₁ t₂ : term), 
  x \notin fv t₁ \u fv t₂ -> 
  t₁ ^ x = t₂ ^ x -> 
  t₁ = t₂.
Proof.
  unfold "^".
  generalize 0.
  introv.
  inductions t₁ gen n; introv Hnotin Heq; 
  destruct t₂; unfold "^" in *; simpls*; try solve [inverts Heq];
  repeat case_if*; substs*; inverts Heq; 
  repeat (simpl_unions; split_and_or_max); autos*; fequals*.
Qed.

Lemma open_subst :
  ∀ t u x,
  x \notin fv t -> 
  t ^^ u = [x ~> u](t ^ x). 
Proof.
  unfold "^^", "^".
  generalize 0.
  intros n t; gen n.
  induction* t; introv Hnotin; repeat (simpls || reduce_max || case_if); fequals*.
Qed.