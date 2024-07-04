From Coq Require Import Unicode.Utf8_core.
From Coq Require Import Peano Nat Arith Lia.
From TLC Require Import LibLN LibTactics LibFset.
From TTSB Require Import Tactics.



Inductive term := 
  | TmBVar : nat -> term 
  | TmFVar : var -> term 
  | TmAbs : term -> term 
  | TmApp : term -> term -> term 
.

Reserved Notation "[{ k ~> u }] t" (at level 67).
Fixpoint open' (k : nat) (u : term) (t : term) : term :=
  match t with 
  | TmBVar i => If i = k then u else t 
  | TmFVar y => t
  | TmAbs t' => TmAbs ([{ (S k) ~> u }] t')
  | TmApp t1 t2 => TmApp ([{k ~> u}] t1) (([{k ~> u}] t2))
  end
  where 
  "[{ k ~> u }] t" := (open' k u t)
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
      ∀ (L : vars) (t : term), 
      (∀ (x : var), (x \notin L) -> lc (t ^ x)) -> 
      lc (TmAbs t)
  | LCApp : 
      ∀ (t1 t2 : term),
      lc t1 -> lc t2 ->
      lc (TmApp t1 t2)
.
#[global]
Hint Constructors lc : core.



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
      unfolds max; simpls*. case_if.
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

#[global]
Hint Extern 1 (lt_type (size_for_ind (_ ^ _))  _) => 
  rewrite <- size_for_ind_open; apply le_refl : core.
#[global]
Hint Extern 1 (lt_type _  (S (max _ _))) => 
  apply Sn_le_Sm; try solve[apply le_max_self]; rewrite max_comm; apply le_max_self : core.

Local Ltac gather_vars := 
  let A := gather_vars_with (fun x : vars => x) in 
  let B := gather_vars_with (fun x : var => \{x}) in 
  let C := gather_vars_with (fun x : term => fv x) in 
  constr:(A \u B \u C).

Local Ltac pick_fresh x :=
  let L := gather_vars in pick_fresh_gen L x.

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
  is_free_BVar (n) ([{k ~> TmFVar x}] t).
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
  [{n ~> p}] t = t.
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


Lemma lc_open_diff : 
  ∀ t p x k, k ≠ 0 -> lc p -> ([{k ~> p}] t) ^ x = [{k ~> p}](t ^ x).
Proof.
  unfold "^". generalize 0.
  introv Hneq Hlc; gen n k x p.
  inductions t; intros; repeat (case_if || reduce_max || simpls || substs); autos*.
  - apply free_Bvar_open, lc_no_free_bvar. assumption.
  - fequals.
    apply* IHt.
  - fequals. 
    + rewrite* IHt1.
    + rewrite* IHt2.
Qed.