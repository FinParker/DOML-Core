From Stdlib Require Import Strings.String.
From DOMLCore Require Import Syntax Context Typing Operational.

Ltac inv H := inversion H; subst; clear H.

Ltac crush_core :=
  repeat match goal with
  | H : value (tLam _ _ _) |- _ => inv H
  | H : has_type _ _ _ _ |- _ => progress (inversion H; subst; clear H)
  | H : lookup _ (extend _ _ _) = Some _ |- _ =>
      unfold extend in H; simpl in H
  | |- context [String.eqb ?x ?x] => rewrite String.eqb_refl
  | H : ?x <> ?y |- context [String.eqb ?x ?y] => rewrite String.eqb_neq by exact H
  | |- _ => eauto with core
  end.

