(* Require Import String.
Require Import PeanoNat.
Require Import Coq.Init.Nat.
Require Import Arith Lia.
From Coq Require Import Unicode.Utf8.
Require Import EvaluationSystem.
Require Import Fin.
Module Syntax.

Inductive term : nat -> Set :=
  (* | T_Free_Var (x : string) : term *)
  | T_Bound_Var : ∀ {lvl : nat}, Fin.t lvl -> term lvl
  | T_App : ∀ {lvl : nat},  term lvl -> term lvl -> term lvl
  | T_Abs : ∀ {lvl : nat}, term (S lvl) -> term lvl
.

Definition shift : ∀ {lvl : nat} ( n k : nat), term lvl -> term (lvl + n).
Proof.
  unshelve refine (fix f {lvl : nat} ( n : nat) (k : nat) (t : term lvl) : term (lvl + n) :=
    match t in term lvl return term (lvl + n) with 
    | T_Bound_Var var => 
      match Fin.to_nat var with 
      | exist _ p p_lt_n0 => 
        match le_gt_dec p k with 
        | left _ => T_Bound_Var (Fin.of_nat_lt _)
        | right _ => T_Bound_Var (Fin.of_nat_lt _)
        end
      end
    | T_App  t₁ t₂ => 
        let t'₁ := f n k t₁ in
        let t'₂ := f n k t₂ in
        T_App t'₁ t'₂
    | T_Abs t => T_Abs (f n k t)
    end
  ).
  - exact p.
  - exact (p + n - 1).
  - lia.
  - lia.
Defined.

Definition loosen_l : ∀ {lvl n : nat}, term lvl → term (n + lvl).
Proof.
  refine (
    fix loosen {lvl n : nat} (t : term lvl) := 
      match t with 
      | T_Bound_Var m => T_Bound_Var (Fin.R n m)
      | T_App t₁ t₂ => T_App (loosen t₁) (loosen t₂)
      | T_Abs t => T_Abs _
      end 
  ).
  rewrite Nat.add_comm. rewrite <- plus_Sn_m. rewrite Nat.add_comm. apply loosen. exact t.
Defined.

Definition loosen_r : ∀ {lvl n : nat}, term lvl → term (lvl + n).
Proof.
  intros. rewrite Nat.add_comm. apply loosen_l. exact H.
Defined.


Definition subst : ∀ {lvl : nat}, term lvl -> ∀ (n : nat), term lvl -> term (lvl + n).
Proof.
  refine(
    fix subst {lvl : nat} (t : term lvl) (n : nat) (s : term lvl) : 
      term (lvl + n) :=
        match t, s in term lvl return term (lvl + n) with 
        | T_Bound_Var m, _ => match Fin.to_nat m with 
          | exist _ p p_lt_n0 => 
            match Nat.eq_dec n p with 
            | left eq => shift n 0 s
            | right neq => loosen_r (T_Bound_Var m)
            end
          end
        | T_App t₁ t₂, _ => T_App (subst t₁ n s) (subst t₂ n s)
        | T_Abs t, _ => T_Abs _
        end
  ).
  
  pose (su := subst (S n0) t (S n) (@loosen_l _ 1 s)).
Defined.

Definition lower : ∀ {lvl : nat}, nat -> term lvl -> term lvl.
Proof.
  refine (
    fix lower {lvl : nat} (n : nat) (t : term lvl) : term lvl := 
    match t with 
    | T_Bound_Var m => match Fin.to_nat m with 
        | exist _ p p_lt_n0 => 
          match le_gt_dec p n with 
          | left m_le_n => T_Bound_Var m
          | right m_gt_n => T_Bound_Var (Fin.of_nat_lt _)
          end
        end
      (* match le_gt_dec m n with 
      | left m_le_n => t
      | right m_gt_n => <{#`m-1`}>
      end *)
    | T_App t₁ t₂ => T_App (lower n t₁) (lower n t₂)
    | T_Abs t => T_Abs (lower (n+1) t)
    end
  ).
  assert (pred p < n0) by lia.
  exact H.
Defined.



Lemma gt_4_5 : 4 < 5. lia. Qed.
Lemma gt_0_6 : 0 < 6. lia. Qed.

Compute subst (T_Abs (T_Bound_Var (Fin.of_nat_lt gt_0_6))) 0 (T_Bound_Var (Fin.of_nat_lt gt_4_5)).
Compute (Fin.of_nat_lt gt_4_5). *)