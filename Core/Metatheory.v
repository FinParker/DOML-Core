From Stdlib Require Import Lists.List.
From DOMLCore Require Import Syntax Context Substitution Typing Operational Lemmas.

Import ListNotations.

Theorem preservation :
  forall Delta e e' T,
    closed e ->
    closed T ->
    has_type Delta [] [] e T ->
    step e e' ->
    exists T',
      has_type Delta [] [] e' T' /\
      defeq T T'.
Proof.
  exact preservation_driver.
Qed.

Theorem progress :
  forall Delta e T,
    has_type Delta [] [] e T ->
    value e \/ exists e', step e e'.
Proof.
  intros Delta e T HT.
  remember (@nil (const_name * tm)) as Omega eqn:HOmega.
  remember (@nil (var * tm)) as Gamma eqn:HGamma.
  induction HT; subst; eauto with core; try discriminate.
  - right. destruct IHHT2; auto.
    + eauto with core.
    + destruct H as [e1' Hstep]. eauto with core.
  - right. destruct IHHT1; auto.
    + destruct IHHT2; auto.
      * destruct (canonical_pi Delta [] e1 x T U HT1 H) as [body Heq].
        subst. eauto with core.
      * destruct H0 as [e2' Hstep]. eauto with core.
    + destruct H as [e1' Hstep]. eauto with core.
  - destruct (IHHT2 eq_refl eq_refl) as [Hv1 | [e1' Hstep1]].
    + destruct (IHHT3 eq_refl eq_refl) as [Hv2 | [e2' Hstep2]].
      * left. constructor; assumption.
      * right. exists (tPair e1 e2'). constructor; assumption.
    + right. exists (tPair e1' e2). constructor; assumption.
  - right. destruct IHHT; auto.
    + destruct (canonical_sigma Delta [] e x T U HT H)
        as [v1 [v2 [Heq [Hv1 Hv2]]]].
      subst. eauto with core.
    + destruct H as [e' Hstep]. eauto with core.
  - right. destruct IHHT; auto.
    + destruct (canonical_sigma Delta [] e x T U HT H)
        as [v1 [v2 [Heq [Hv1 Hv2]]]].
      subst. eauto with core.
    + destruct H as [e' Hstep]. eauto with core.
  - destruct (IHHT2 eq_refl eq_refl) as [Hv | [e' Hstep]].
    + left. constructor. assumption.
    + right. exists (tInl U e'). constructor. assumption.
  - destruct (IHHT1 eq_refl eq_refl) as [Hv | [e' Hstep]].
    + left. constructor. assumption.
    + right. exists (tInr T e'). constructor. assumption.
  - right. destruct IHHT1; auto.
    + destruct (canonical_sum Delta [] e T U HT1 H) as
        [[v1 [Heq Hv1]] | [v2 [Heq Hv2]]].
      * subst. eauto with core.
      * subst. eauto with core.
    + destruct H as [e' Hstep]. eauto with core.
  - destruct (IHHT2 eq_refl eq_refl) as [Hv | [e0' Hstep]].
    + left. constructor. assumption.
    + right. exists (tRefl e0'). constructor. assumption.
  - right.
    destruct (IHHT2 eq_refl eq_refl) as [Hvp | [p' Hstepp]].
    + destruct (IHHT3 eq_refl eq_refl) as [Hvq | [q' Hstepq]].
      * destruct (canonical_eq_proof Delta [] p T e e' HT2 Hvp)
          as [w [Hp [He [He' Hvw]]]].
        subst. exists q. constructor. assumption.
      * exists (tEqElim P e e' p q'). constructor; assumption.
    + exists (tEqElim P e e' p' q). constructor. assumption.
  - left. unfold domain_type. constructor.
  - destruct (IHHT2 eq_refl eq_refl) as [HvArgs | [args' HstepArgs]].
    + destruct (IHHT3 eq_refl eq_refl) as [HvProof | [proof' HstepProof]].
      * left. unfold intro_dom. constructor; assumption.
      * right. exists (intro_dom args proof').
        unfold intro_dom. constructor; assumption.
    + right. exists (intro_dom args' proof).
      unfold intro_dom. constructor; assumption.
  - right.
    destruct (IHHT1 eq_refl eq_refl) as [Hv1 | [e1' Hstep1]].
    + destruct (IHHT2 eq_refl eq_refl) as [Hv2 | [e2' Hstep2]].
      * destruct (canonical_int Delta [] _ HT1 Hv1) as [z1 Heq1].
        destruct (canonical_int Delta [] _ HT2 Hv2) as [z2 Heq2].
        subst. eauto with core.
      * eexists. eapply ST_Plus2; eauto.
    + eexists. eapply ST_Plus1; eauto.
  - right.
    destruct (IHHT1 eq_refl eq_refl) as [Hv1 | [e1' Hstep1]].
    + destruct (IHHT2 eq_refl eq_refl) as [Hv2 | [e2' Hstep2]].
      * destruct (canonical_int Delta [] _ HT1 Hv1) as [z1 Heq1].
        destruct (canonical_int Delta [] _ HT2 Hv2) as [z2 Heq2].
        subst. eauto with core.
      * eexists. eapply ST_Minus2; eauto.
    + eexists. eapply ST_Minus1; eauto.
Qed.

