From Stdlib Require Import Lists.List.
From DOMLCore Require Import Syntax Context Substitution Typing Operational Lemmas.

Import ListNotations.

Theorem preservation :
  forall Delta e e' T,
    has_type Delta [] e T ->
    step e e' ->
    has_type Delta [] e' T.
Proof.
  (**
    Standard induction on the reduction derivation.  The beta and let cases
    use [substitution_preserves_typing]; projections use [canonical_sigma];
    case reductions use [canonical_sum].  Arithmetic cases use
    [canonical_int].
   *)
Admitted.

Theorem progress :
  forall Delta e T,
    has_type Delta [] e T ->
    value e \/ exists e', step e e'.
Proof.
  (**
    Standard induction on typing.  Canonical-form lemmas handle elimination
    forms over values; congruence rules handle reducible subterms.  Domain
    introductions are values once their argument and proof fields are values.
   *)
Admitted.

