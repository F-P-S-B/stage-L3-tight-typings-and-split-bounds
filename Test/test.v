Unset Guard Checking.

Fixpoint f (n : nat) : nat := S (f n).

Set Guard Checking.
Opaque f.
(* Arguments f _ : simpl never. *)

Theorem thm : f 0 = S (f 0).
  generalize 0.
  intro n.
  unfold f at 1.
  simpl.
Admitted.

Theorem contra :
  exists n, n = S n.
Proof.
  exists (f 0).
  apply thm.
Qed.

Goal False.
  assert (exists n, n = S n) by exact contra.
  destruct H.
  induction x.
  inversion H.
  inversion H.
  apply IHx.
  assumption.
Qed.

(* 

  t ::=
    | variable
    | t₁ t₂ <=> t₁(t₂)
    | λ x . t <=> x |-> t

  (β) (λ x. t) t' -> t[x <- t']
  
(x |-> x + 2)(7)
  t  = x + 2
  t₁ = λ x . t
  t₂ = 7

  t₁ t₂ = (λ x . x + 2) 7 -> 7 + 2 = 9


(λ x . (λ y. y y) x) z
-> (λ x . x x) z
   (λ y . y y) z

(λ x . x + 7) z -> z + 7


δ = (λ x . x x x) 
δ δ = (λ x . x x x) δ -> δ δ δ
(λ x . x)

x (λ y . y y y) 


(λ y . (λ z . z) y)

 x y z

(λ y . y + 2) (λ y . y + 3)

f(x) = 3 + x

f(3) = 3 + 3 = 6


(λ y . y + 2) 7 -> 7 + 2 = 9

y


(λ y . (x + 7))



t = λ x . t'

t p


f(x) = (x + 1) / (x + 0.5)
x : [ℕ, ℝ]



I = λ z . z



(λ x₁ . (λ x₀ . x₀ x₁ ) x₁) I -> 
(λ x₀ . x₀ I ) I ->
I I = (λ z . z) (λ z . z) -> 
(λ z . z)


 |<variable>| := 0
 |λ x . t| := 1 + |t|
 |t p| := 1 + |t|



 x : [ℕ] ⊢ x + 3 : ℕ

Γ = x : [ℕ]

        Γ ⊢ x + 3 : ℕ
--------------------------------
Γ \\ x ⊢ λ x . x + 3 : Γ(x) -> ℕ



 ⊢ λ x . x + 3 : [ℕ] -> ℕ

 *)