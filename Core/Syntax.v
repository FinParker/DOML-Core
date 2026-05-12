From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.

Import ListNotations.
Open Scope Z_scope.

(**
  Syntax of the DOML-Core.
 *)

Definition var := string.
Definition dom_name := string.
Definition const_name := string.

Inductive state : Type :=
| Required
| Optional
| Removed.

Inductive tm : Type :=
| tSort : nat -> tm
| tBool : tm
| tInt : tm
| tUnit : tm
| tEmpty : tm
| tTrue : tm
| tFalse : tm
| tIntLit : Z -> tm
| tUnitLit : tm
| tVar : var -> tm
| tConst : const_name -> tm
| tLet : var -> tm -> tm -> tm
| tPi : var -> tm -> tm -> tm
| tLam : var -> tm -> tm -> tm
| tApp : tm -> tm -> tm
| tSigma : var -> tm -> tm -> tm
| tPair : tm -> tm -> tm
| tFst : tm -> tm
| tSnd : tm -> tm
| tSum : tm -> tm -> tm
| tInl : tm -> tm -> tm
| tInr : tm -> tm -> tm
| tCase : tm -> var -> tm -> var -> tm -> tm
| tEq : tm -> tm -> tm -> tm
| tRefl : tm -> tm
| tEqElim : tm -> tm -> tm -> tm -> tm -> tm
| tPlus : tm -> tm -> tm
| tMinus : tm -> tm -> tm.

Inductive node_sig : Type :=
| ValNode : tm -> state -> node_sig
| StructNode : child_sig -> node_sig
with child_sig : Type :=
| ChildNil : child_sig
| ChildCons : var -> node_sig -> child_sig -> child_sig.

Scheme node_sig_ind' := Induction for node_sig Sort Prop
with child_sig_ind' := Induction for child_sig Sort Prop.
Combined Scheme sig_ind from node_sig_ind', child_sig_ind'.

Record domain_entry : Type := {
  de_tree : child_sig;
  de_constraint : tm
}.

Definition context := list (var * tm).
Definition dom_context := list (dom_name * domain_entry).
Definition const_context := list (const_name * tm).

(**
  [elab_tree] is the Core type generated from a normalized field signature.
  In a full implementation this is a structurally recursive function over
  [child_sig].  Here it is abstract: Core checks the generated type, not the
  Surface tree algorithm.
 *)
Parameter elab_tree : child_sig -> tm.

Definition domain_type (ent : domain_entry) : tm :=
  let a := "_args"%string in
  tSigma a (elab_tree (de_tree ent))
    (tEq tBool (tApp (de_constraint ent) (tVar a)) tTrue).

Definition intro_dom (args proof : tm) : tm :=
  tPair args proof.

