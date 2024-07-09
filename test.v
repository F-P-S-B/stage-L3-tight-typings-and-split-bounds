Require Import String.
Inductive b :=
| BVar : string -> b
| BApp : b -> b -> b
| BAbs : string -> b -> b
| Ext : string -> list b -> b
.

Inductive t :=
| TVar : string -> t
| TApp : t -> t -> t
| TAbs : string -> t -> t
.

Fixpoint has_ext (e : b) : Prop :=
  match e with 
  | BVar _ => False
  | BApp e1 e2 => has_ext e1 \/ has_ext e2
  | BAbs _ e => has_ext e
  | Ext _ _ => True
  end.

Ltac my_tauto := 
    simpl in *;
    tauto
  .

Program Fixpoint b_to_t (e : b) (h : ~ has_ext e) : t :=
  match e with 
  | BVar x => TVar x
  | BApp e1 e2 => TApp (b_to_t e1 _) (b_to_t e2 _)
  | BAbs x e => TAbs x (b_to_t e _)
  | Ext _ _ => _
  end.
Next Obligation.
  my_tauto.
Qed.
Next Obligation.
  my_tauto.
Qed.
Next Obligation.
  exfalso.
  apply h.
  simpl.
  exact I.
Qed.
  