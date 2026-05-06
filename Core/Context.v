From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From DOMLCore Require Import Syntax.

Import ListNotations.

Fixpoint lookup {A : Type} (x : string) (env : list (string * A)) : option A :=
  match env with
  | [] => None
  | (y, v) :: env' => if String.eqb x y then Some v else lookup x env'
  end.

Definition extend (Gamma : context) (x : var) (T : tm) : context :=
  (x, T) :: Gamma.

Lemma lookup_extend_eq :
  forall Gamma x T, lookup x (extend Gamma x T) = Some T.
Proof.
  intros. unfold extend. simpl. now rewrite String.eqb_refl.
Qed.

Lemma lookup_extend_neq :
  forall Gamma x y T,
    x <> y ->
    lookup x (extend Gamma y T) = lookup x Gamma.
Proof.
  intros Gamma x y T Hneq. unfold extend. simpl.
  apply String.eqb_neq in Hneq. now rewrite Hneq.
Qed.

