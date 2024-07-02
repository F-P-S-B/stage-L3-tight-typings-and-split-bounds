From TLC Require Import LibFset LibTactics.

Lemma split_subset :
  forall (T : Type) (A B C : fset T),
  A \u B \c C -> 
  A \c C /\ B \c C.
Proof.
  intros.
  split;
  intros x Hin; unfold "\c" in H;
  apply H; rewrite in_union; autos.
Qed.

Ltac split_and_or := 
  match goal with 
  | [ |- _ /\ _] => split
  | [ |- _ <-> _] => split
  | [ H : _ /\ _ |- _] => 
      let H1 := fresh H in
      let H2 := fresh H in
      destruct H as [H1 H2]
  | [ H : _ <-> _ |- _] => 
      let H1 := fresh H in
      let H2 := fresh H in
      destruct H as [H1 H2]
  | [ H : _ \/ _ |- _] => 
      destruct H as [H | H]
  end.

Ltac simpl_unions := 
  match goal with 
  | [  |- context[\{} \u _] ] => rewrite LibFset.union_empty_l
  | [  |- context[_ \u \{}] ] => rewrite LibFset.union_empty_r
  | [ H : context[\{} \u _] |- _] => rewrite LibFset.union_empty_l in H
  | [ H : context[_ \u \{}] |- _] => rewrite LibFset.union_empty_r in H
  | [ H : context[_ \in \{}] |- _ ] => rewrite in_empty in H; contradiction
  | [ H : context[_ \in \{ _ }] |- _ ] => rewrite in_singleton in H
  | [  |- context[_ \in \{ _ }]] => rewrite in_singleton
  | [  |- context[_ \in _ \u _]] => rewrite in_union
  | [ H : context[_ \in _ \u _] |- _] => rewrite in_union in H
  | [ H : context[_ \notin \{ _ }] |- _] => rewrite notin_singleton in H
  | [ H : context[_ \notin _ \u _] |- _] => rewrite notin_union in H
  | [ |- context[_ \notin \{ _ }]] => rewrite notin_singleton
  | [ |- context[_ \notin _ \u _]] => rewrite notin_union
  | [ H : context[_ \notin _ \u _] |- _] => rewrite notin_union in H
  | [ H : _ \u _ \c _ |- _] => apply split_subset in H
  | [ |- context[(_ \u _) \- _]] => rewrite union_remove
  | [ H : context[(_ \u _) \- _] |- _] => rewrite union_remove in H
  | [ H : context[_ \in _ \- _] |- _] => rewrite in_remove in H
  | [ |- context[_ \in _ \- _] ] => rewrite in_remove
  end.

Ltac split_and_or_max := repeat split_and_or.

Ltac use_equivalences := idtac.

Ltac absurd := let H := fresh in intro H; inverts H; fail.

Ltac reduce_max := repeat (simpl_unions || split_and_or).


Lemma jmeq_to_eq :
  forall A (v1 v2 : fset A), 
  v1 = v2 -> JMeq.JMeq v1 v2.
Proof.
  intros; substs*.
Qed.

Ltac solve_set_equality :=
  try apply jmeq_to_eq;
  let x := fresh "x" in 
  let Hin := fresh "Hin" x in 
  apply fset_extens; intros x Hin; reduce_max; autos.