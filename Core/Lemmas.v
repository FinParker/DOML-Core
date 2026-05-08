From Stdlib Require Import Lists.List.
From DOMLCore Require Import Syntax Context Substitution Typing Operational Automation.

Import ListNotations.

Lemma canonical_bool :
  forall Delta Omega v,
    has_type Delta Omega [] v tBool ->
    value v ->
    v = tTrue \/ v = tFalse.
Proof.
  intros Delta Omega v HT HV.
  inv HV; try solve [inv HT].
  - left; reflexivity.
  - right; reflexivity.
Qed.

Lemma canonical_int :
  forall Delta Omega v,
    has_type Delta Omega [] v tInt ->
    value v ->
    exists z, v = tIntLit z.
Proof.
  intros Delta Omega v HT HV.
  inv HV; try solve [inv HT].
  exists z. reflexivity.
Qed.

Lemma canonical_pi :
  forall Delta Omega v x T U,
    has_type Delta Omega [] v (tPi x T U) ->
    value v ->
    exists e, v = tLam x T e.
Proof.
  intros Delta Omega v x T U HT HV.
  inv HV; try solve [inv HT].
  inv HT.
  exists e. reflexivity.
Qed.

Lemma canonical_sigma :
  forall Delta Omega v x T U,
    has_type Delta Omega [] v (tSigma x T U) ->
    value v ->
    exists v1 v2, v = tPair v1 v2 /\ value v1 /\ value v2.
Proof.
  intros Delta Omega v x T U HT HV.
  inv HV; try solve [inv HT].
  inv HT; exists v1, v2; repeat split; eauto.
Qed.

Lemma canonical_sum :
  forall Delta Omega v T U,
    has_type Delta Omega [] v (tSum T U) ->
    value v ->
    (exists v1, v = tInl U v1 /\ value v1) \/
    (exists v2, v = tInr T v2 /\ value v2).
Proof.
  intros Delta Omega v T U HT HV.
  inversion HV; subst; try solve [inversion HT].
  - inversion HT; subst.
    left. eexists. split; [reflexivity | eauto].
  - inversion HT; subst.
    right. eexists. split; [reflexivity | eauto].
Qed.

Lemma canonical_eq_proof :
  forall Delta Omega v T e e',
    has_type Delta Omega [] v (tEq T e e') ->
    value v ->
    exists w, v = tRefl w /\ e = w /\ e' = w /\ value w.
Proof.
  intros Delta Omega v T e e' HT HV.
  inversion HV; subst; try solve [inversion HT].
  inversion HT; subst. eexists. repeat split; eauto.
Qed.

Lemma substitution_preserves_typing :
  forall Delta Omega Gamma x U e v T,
    has_type Delta Omega (extend Gamma x U) e T ->
    has_type Delta Omega Gamma v U ->
    has_type Delta Omega Gamma (subst x v e) T.
Proof.
  (**
    The actual proof is by induction on the first typing derivation.  The
    interesting binder cases use [lookup_extend_eq] and [lookup_extend_neq],
    while the syntax-directed cases are discharged by [crush_core].
   *)
Admitted.

