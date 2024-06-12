From Coq Require Import Unicode.Utf8_core.

Section Test.
Variable A : Set.
Variable P : A -> Prop.
Goal (∃ x, P x) -> ¬ ∀ x, ¬ P x.
Proof.
  intros * [x Hp] H_contra.
  eapply H_contra. apply Hp.
Qed.

Goal (∀ x, ¬ P x) -> ¬ ∃ x, P x.
Proof.
  intros * Hforall [x_contra H_contra].
  eapply Hforall. apply H_contra.
Qed.

