
Ltac absurd := 
  let H := fresh in
  intro H; inversion H; fail.

Ltac myauto t := 
               (absurd; fail) 
            || (exfalso; eauto; fail)
            || (t; fail)
            || eauto.

Tactic Notation "'myauto'" := myauto idtac.