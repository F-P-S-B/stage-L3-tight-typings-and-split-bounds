Require Import PeanoNat.
Require Import Arith.
From Coq Require Import Unicode.Utf8.

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
