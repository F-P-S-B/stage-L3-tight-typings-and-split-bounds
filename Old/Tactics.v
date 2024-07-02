
Ltac absurd := 
  let H := fresh in
  intro H; inversion H; fail.

Ltac myauto t := 
               (absurd; fail) 
            || (exfalso; eauto; fail)
            || (t; fail)
            || eauto.

Tactic Notation "'myauto'" := myauto idtac.


Ltac split_and := 
  match goal with 
  | [ |- _ /\ _ ] => split
  | [H : _ /\ _ |- _] => destruct H
  end.
