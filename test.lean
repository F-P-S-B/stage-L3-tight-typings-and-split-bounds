inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
deriving Repr

def sum {n : Nat} (l1 l2 : Vect Nat n) : Vect Nat n :=
match l1, l2 with
| Vect.nil, Vect.nil => Vect.nil
| Vect.cons n1 l1', Vect.cons n2 l2' => Vect.cons (n1 + n2) (sum l1' l2')

#eval (sum (Vect.cons 1 Vect.nil) (Vect.cons 2 Vect.nil))
