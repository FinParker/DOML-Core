From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From DOMLCore Require Import Syntax Context Substitution Typing Operational Automation.

Import ListNotations.

Inductive appears_free_in : var -> tm -> Prop :=
| AF_Var : forall x,
    appears_free_in x (tVar x)
| AF_Let1 : forall x y e1 e2,
    appears_free_in x e1 ->
    appears_free_in x (tLet y e1 e2)
| AF_Let2 : forall x y e1 e2,
    x <> y ->
    appears_free_in x e2 ->
    appears_free_in x (tLet y e1 e2)
| AF_Pi1 : forall x y T U,
    appears_free_in x T ->
    appears_free_in x (tPi y T U)
| AF_Pi2 : forall x y T U,
    x <> y ->
    appears_free_in x U ->
    appears_free_in x (tPi y T U)
| AF_Lam1 : forall x y T e,
    appears_free_in x T ->
    appears_free_in x (tLam y T e)
| AF_Lam2 : forall x y T e,
    x <> y ->
    appears_free_in x e ->
    appears_free_in x (tLam y T e)
| AF_App1 : forall x e1 e2,
    appears_free_in x e1 ->
    appears_free_in x (tApp e1 e2)
| AF_App2 : forall x e1 e2,
    appears_free_in x e2 ->
    appears_free_in x (tApp e1 e2)
| AF_Sigma1 : forall x y T U,
    appears_free_in x T ->
    appears_free_in x (tSigma y T U)
| AF_Sigma2 : forall x y T U,
    x <> y ->
    appears_free_in x U ->
    appears_free_in x (tSigma y T U)
| AF_Pair1 : forall x e1 e2,
    appears_free_in x e1 ->
    appears_free_in x (tPair e1 e2)
| AF_Pair2 : forall x e1 e2,
    appears_free_in x e2 ->
    appears_free_in x (tPair e1 e2)
| AF_Fst : forall x e,
    appears_free_in x e ->
    appears_free_in x (tFst e)
| AF_Snd : forall x e,
    appears_free_in x e ->
    appears_free_in x (tSnd e)
| AF_Sum1 : forall x T U,
    appears_free_in x T ->
    appears_free_in x (tSum T U)
| AF_Sum2 : forall x T U,
    appears_free_in x U ->
    appears_free_in x (tSum T U)
| AF_Inl1 : forall x U e,
    appears_free_in x U ->
    appears_free_in x (tInl U e)
| AF_Inl2 : forall x U e,
    appears_free_in x e ->
    appears_free_in x (tInl U e)
| AF_Inr1 : forall x T e,
    appears_free_in x T ->
    appears_free_in x (tInr T e)
| AF_Inr2 : forall x T e,
    appears_free_in x e ->
    appears_free_in x (tInr T e)
| AF_CaseScrut : forall x e y el z er,
    appears_free_in x e ->
    appears_free_in x (tCase e y el z er)
| AF_CaseLeft : forall x e y el z er,
    x <> y ->
    appears_free_in x el ->
    appears_free_in x (tCase e y el z er)
| AF_CaseRight : forall x e y el z er,
    x <> z ->
    appears_free_in x er ->
    appears_free_in x (tCase e y el z er)
| AF_EqTy : forall x T e1 e2,
    appears_free_in x T ->
    appears_free_in x (tEq T e1 e2)
| AF_EqLeft : forall x T e1 e2,
    appears_free_in x e1 ->
    appears_free_in x (tEq T e1 e2)
| AF_EqRight : forall x T e1 e2,
    appears_free_in x e2 ->
    appears_free_in x (tEq T e1 e2)
| AF_Refl : forall x e,
    appears_free_in x e ->
    appears_free_in x (tRefl e)
| AF_EqElimP : forall x P e e' p q,
    appears_free_in x P ->
    appears_free_in x (tEqElim P e e' p q)
| AF_EqElimLeft : forall x P e e' p q,
    appears_free_in x e ->
    appears_free_in x (tEqElim P e e' p q)
| AF_EqElimRight : forall x P e e' p q,
    appears_free_in x e' ->
    appears_free_in x (tEqElim P e e' p q)
| AF_EqElimProof : forall x P e e' p q,
    appears_free_in x p ->
    appears_free_in x (tEqElim P e e' p q)
| AF_EqElimBody : forall x P e e' p q,
    appears_free_in x q ->
    appears_free_in x (tEqElim P e e' p q)
| AF_Plus1 : forall x e1 e2,
    appears_free_in x e1 ->
    appears_free_in x (tPlus e1 e2)
| AF_Plus2 : forall x e1 e2,
    appears_free_in x e2 ->
    appears_free_in x (tPlus e1 e2)
| AF_Minus1 : forall x e1 e2,
    appears_free_in x e1 ->
    appears_free_in x (tMinus e1 e2)
| AF_Minus2 : forall x e1 e2,
    appears_free_in x e2 ->
    appears_free_in x (tMinus e1 e2).

Definition closed (e : tm) : Prop :=
  forall x, ~ appears_free_in x e.

Inductive wf_context (Delta : dom_context) (Omega : const_context) : context -> Prop :=
| WF_Empty : wf_context Delta Omega []
| WF_Extend : forall Gamma x T s,
    wf_context Delta Omega Gamma ->
    closed T ->
    has_type Delta Omega Gamma T (tSort s) ->
    wf_context Delta Omega (extend Gamma x T).

Definition closed_context (Gamma : context) : Prop :=
  forall x T, lookup x Gamma = Some T -> closed T.

Lemma closed_context_empty :
  closed_context [].
Proof.
  intros x T Hlookup. discriminate.
Qed.

Definition context_equiv (Gamma Gamma' : context) : Prop :=
  forall x, lookup x Gamma = lookup x Gamma'.

Lemma context_equiv_refl :
  forall Gamma,
    context_equiv Gamma Gamma.
Proof.
  intros Gamma x. reflexivity.
Qed.

Lemma context_equiv_extend :
  forall Gamma Gamma' x T,
    context_equiv Gamma Gamma' ->
    context_equiv (extend Gamma x T) (extend Gamma' x T).
Proof.
  intros Gamma Gamma' x T Heq y.
  unfold extend. simpl.
  destruct (String.eqb y x); auto.
Qed.

Lemma typing_context_equiv :
  forall Delta Omega Gamma Gamma' e T,
    context_equiv Gamma Gamma' ->
    has_type Delta Omega Gamma e T ->
    has_type Delta Omega Gamma' e T.
Proof.
  intros Delta Omega Gamma Gamma' e T Heq HT.
  generalize dependent Gamma'.
  induction HT; intros Gamma' Heq; try solve [constructor; eauto].
  - apply T_Var. rewrite <- Heq. assumption.
  - eapply T_Let.
    + apply IHHT1. assumption.
    + apply IHHT2. assumption.
    + apply IHHT3. apply context_equiv_extend. assumption.
  - eapply T_Pi.
    + apply IHHT1. assumption.
    + apply IHHT2. apply context_equiv_extend. assumption.
  - eapply T_Lam.
    + apply IHHT1. assumption.
    + apply IHHT2. apply context_equiv_extend. assumption.
  - eapply T_App.
    + apply IHHT1. assumption.
    + apply IHHT2. assumption.
  - eapply T_Sigma.
    + apply IHHT1. assumption.
    + apply IHHT2. apply context_equiv_extend. assumption.
  - eapply T_Pair.
    + apply IHHT1. assumption.
    + apply IHHT2. assumption.
    + apply IHHT3. assumption.
  - eapply T_Fst. apply IHHT. assumption.
  - eapply T_Snd. apply IHHT. assumption.
  - eapply T_Inl.
    + apply IHHT1. assumption.
    + apply IHHT2. assumption.
    + apply IHHT3. assumption.
  - eapply T_Inr.
    + apply IHHT1. assumption.
    + apply IHHT2. assumption.
    + apply IHHT3. assumption.
  - eapply T_Case.
    + apply IHHT1. assumption.
    + apply IHHT2. apply context_equiv_extend. assumption.
    + apply IHHT3. apply context_equiv_extend. assumption.
  - eapply T_Eq.
    + apply IHHT1. assumption.
    + apply IHHT2. assumption.
    + apply IHHT3. assumption.
  - eapply T_Refl.
    + apply IHHT1. assumption.
    + apply IHHT2. assumption.
  - eapply T_EqElim.
    + apply IHHT1. assumption.
    + apply IHHT2. assumption.
    + apply IHHT3. assumption.
  - eapply T_DomainType.
    + eauto.
    + apply IHHT1. assumption.
    + apply IHHT2. assumption.
  - eapply T_IntroDom.
    + eauto.
    + apply IHHT1. assumption.
    + apply IHHT2. assumption.
    + apply IHHT3. assumption.
  - eapply T_Conv.
    + apply IHHT. assumption.
    + assumption.
Qed.

Lemma wf_context_tail :
  forall Delta Omega Gamma x T,
    wf_context Delta Omega (extend Gamma x T) ->
    wf_context Delta Omega Gamma.
Proof.
  intros Delta Omega Gamma x T Hwf.
  inversion Hwf; subst. assumption.
Qed.

Lemma wf_context_head_closed :
  forall Delta Omega Gamma x T,
    wf_context Delta Omega (extend Gamma x T) ->
    closed T.
Proof.
  intros Delta Omega Gamma x T Hwf.
  inversion Hwf; subst. assumption.
Qed.

Lemma wf_context_closed_context :
  forall Delta Omega Gamma,
    wf_context Delta Omega Gamma ->
    closed_context Gamma.
Proof.
  intros Delta Omega Gamma Hwf.
  induction Hwf; unfold closed_context in *; intros y U Hlookup.
  - discriminate.
  - unfold extend in Hlookup. simpl in Hlookup.
    destruct (String.eqb_spec y x) as [Heq | Hneq].
    + inversion Hlookup; subst. assumption.
    + eapply IHHwf. exact Hlookup.
Qed.

Lemma closed_context_extend :
  forall Gamma x T,
    closed_context Gamma ->
    closed T ->
    closed_context (extend Gamma x T).
Proof.
  intros Gamma x T Hctx HT y U Hlookup.
  unfold extend in Hlookup. simpl in Hlookup.
  destruct (String.eqb_spec y x) as [Heq | Hneq].
  - inversion Hlookup; subst. assumption.
  - eapply Hctx. exact Hlookup.
Qed.

Lemma lookup_shadow :
  forall Gamma x U T,
    lookup x (extend (extend Gamma x U) x T) = Some T.
Proof.
  intros. apply lookup_extend_eq.
Qed.

Lemma lookup_drop_shadow :
  forall Gamma x U T y,
    lookup y (extend (extend Gamma x U) x T) =
    lookup y (extend Gamma x T).
Proof.
  intros Gamma x U T y.
  unfold extend. simpl.
  destruct (String.eqb y x); reflexivity.
Qed.

Lemma typing_drop_shadow :
  forall Delta Omega Gamma x U T e V,
    has_type Delta Omega (extend (extend Gamma x U) x T) e V ->
    has_type Delta Omega (extend Gamma x T) e V.
Proof.
  intros Delta Omega Gamma x U T e V HT.
  eapply typing_context_equiv; [| exact HT].
  intros y. apply lookup_drop_shadow.
Qed.

Lemma typing_shadow_weaken :
  forall Delta Omega Gamma x U T e V,
    has_type Delta Omega (extend Gamma x T) e V ->
    has_type Delta Omega (extend (extend Gamma x U) x T) e V.
Proof.
  intros Delta Omega Gamma x U T e V HT.
  eapply typing_context_equiv; [| exact HT].
  intros y. symmetry. apply lookup_drop_shadow.
Qed.

Lemma closed_app_inv :
  forall e1 e2,
    closed (tApp e1 e2) -> closed e1 /\ closed e2.
Proof.
  intros e1 e2 H. split; unfold closed in *; intros x Hfree; apply (H x).
  - apply AF_App1. exact Hfree.
  - apply AF_App2. exact Hfree.
Qed.

Lemma closed_let_bound_inv :
  forall y e1 e2,
    closed (tLet y e1 e2) -> closed e1.
Proof.
  intros y e1 e2 H. unfold closed in *. intros x Hfree. apply (H x).
  apply AF_Let1. exact Hfree.
Qed.

Lemma closed_pi_domain_inv :
  forall y T U,
    closed (tPi y T U) -> closed T.
Proof.
  intros y T U H. unfold closed in *. intros x Hfree. apply (H x).
  apply AF_Pi1. exact Hfree.
Qed.

Lemma closed_lam_type_inv :
  forall y T e,
    closed (tLam y T e) -> closed T.
Proof.
  intros y T e H. unfold closed in *. intros x Hfree. apply (H x).
  apply AF_Lam1. exact Hfree.
Qed.

Lemma closed_sigma_domain_inv :
  forall y T U,
    closed (tSigma y T U) -> closed T.
Proof.
  intros y T U H. unfold closed in *. intros x Hfree. apply (H x).
  apply AF_Sigma1. exact Hfree.
Qed.

Lemma closed_pair_inv :
  forall e1 e2,
    closed (tPair e1 e2) -> closed e1 /\ closed e2.
Proof.
  intros e1 e2 H. split; unfold closed in *; intros x Hfree; apply (H x).
  - apply AF_Pair1. exact Hfree.
  - apply AF_Pair2. exact Hfree.
Qed.

Lemma closed_fst_inv :
  forall e,
    closed (tFst e) -> closed e.
Proof.
  intros e H. unfold closed in *. intros x Hfree. apply (H x).
  apply AF_Fst. exact Hfree.
Qed.

Lemma closed_snd_inv :
  forall e,
    closed (tSnd e) -> closed e.
Proof.
  intros e H. unfold closed in *. intros x Hfree. apply (H x).
  apply AF_Snd. exact Hfree.
Qed.

Lemma closed_sum_inl_inv :
  forall U e,
    closed (tInl U e) -> closed U /\ closed e.
Proof.
  intros U e H. split; unfold closed in *; intros x Hfree; apply (H x).
  - apply AF_Inl1. exact Hfree.
  - apply AF_Inl2. exact Hfree.
Qed.

Lemma closed_sum_inr_inv :
  forall T e,
    closed (tInr T e) -> closed T /\ closed e.
Proof.
  intros T e H. split; unfold closed in *; intros x Hfree; apply (H x).
  - apply AF_Inr1. exact Hfree.
  - apply AF_Inr2. exact Hfree.
Qed.

Lemma closed_case_inv :
  forall e x el y er,
    closed (tCase e x el y er) -> closed e.
Proof.
  intros e x el y er H. unfold closed in *. intros z Hfree. apply (H z).
  apply AF_CaseScrut. exact Hfree.
Qed.

Lemma closed_refl_inv :
  forall e,
    closed (tRefl e) -> closed e.
Proof.
  intros e H. unfold closed in *. intros x Hfree. apply (H x).
  apply AF_Refl. exact Hfree.
Qed.

Lemma closed_eqelim_inv :
  forall P e e' p q,
    closed (tEqElim P e e' p q) ->
    closed P /\ closed e /\ closed e' /\ closed p /\ closed q.
Proof.
  intros P e e' p q H. repeat split; unfold closed in *; intros x Hfree;
    apply (H x).
  - apply AF_EqElimP. exact Hfree.
  - apply AF_EqElimLeft. exact Hfree.
  - apply AF_EqElimRight. exact Hfree.
  - apply AF_EqElimProof. exact Hfree.
  - apply AF_EqElimBody. exact Hfree.
Qed.

Lemma closed_plus_inv :
  forall e1 e2,
    closed (tPlus e1 e2) -> closed e1 /\ closed e2.
Proof.
  intros e1 e2 H. split; unfold closed in *; intros x Hfree; apply (H x).
  - apply AF_Plus1. exact Hfree.
  - apply AF_Plus2. exact Hfree.
Qed.

Lemma closed_minus_inv :
  forall e1 e2,
    closed (tMinus e1 e2) -> closed e1 /\ closed e2.
Proof.
  intros e1 e2 H. split; unfold closed in *; intros x Hfree; apply (H x).
  - apply AF_Minus1. exact Hfree.
  - apply AF_Minus2. exact Hfree.
Qed.

Lemma subst_not_free :
  forall e x s,
    ~ appears_free_in x e ->
    subst x s e = e.
Proof.
  induction e; intros x s Hnot; simpl; try reflexivity.
  - destruct (String.eqb_spec x v) as [Heq | Hneq].
    + subst. exfalso. apply Hnot. constructor.
    + reflexivity.
  - f_equal.
    + apply IHe1. intros Hfree. apply Hnot. apply AF_Let1. exact Hfree.
    + destruct (String.eqb_spec x v) as [Heq | Hneq].
      * reflexivity.
      * apply IHe2. intros Hfree. apply Hnot.
        apply AF_Let2; assumption.
  - f_equal.
    + apply IHe1. intros Hfree. apply Hnot. apply AF_Pi1. exact Hfree.
    + destruct (String.eqb_spec x v) as [Heq | Hneq].
      * reflexivity.
      * apply IHe2. intros Hfree. apply Hnot.
        apply AF_Pi2; assumption.
  - f_equal.
    + apply IHe1. intros Hfree. apply Hnot. apply AF_Lam1. exact Hfree.
    + destruct (String.eqb_spec x v) as [Heq | Hneq].
      * reflexivity.
      * apply IHe2. intros Hfree. apply Hnot.
        apply AF_Lam2; assumption.
  - f_equal.
    + apply IHe1. intros Hfree. apply Hnot. apply AF_App1. exact Hfree.
    + apply IHe2. intros Hfree. apply Hnot. apply AF_App2. exact Hfree.
  - f_equal.
    + apply IHe1. intros Hfree. apply Hnot. apply AF_Sigma1. exact Hfree.
    + destruct (String.eqb_spec x v) as [Heq | Hneq].
      * reflexivity.
      * apply IHe2. intros Hfree. apply Hnot.
        apply AF_Sigma2; assumption.
  - f_equal.
    + apply IHe1. intros Hfree. apply Hnot. apply AF_Pair1. exact Hfree.
    + apply IHe2. intros Hfree. apply Hnot. apply AF_Pair2. exact Hfree.
  - f_equal. apply IHe. intros Hfree. apply Hnot. apply AF_Fst. exact Hfree.
  - f_equal. apply IHe. intros Hfree. apply Hnot. apply AF_Snd. exact Hfree.
  - f_equal.
    + apply IHe1. intros Hfree. apply Hnot. apply AF_Sum1. exact Hfree.
    + apply IHe2. intros Hfree. apply Hnot. apply AF_Sum2. exact Hfree.
  - f_equal.
    + apply IHe1. intros Hfree. apply Hnot. apply AF_Inl1. exact Hfree.
    + apply IHe2. intros Hfree. apply Hnot. apply AF_Inl2. exact Hfree.
  - f_equal.
    + apply IHe1. intros Hfree. apply Hnot. apply AF_Inr1. exact Hfree.
    + apply IHe2. intros Hfree. apply Hnot. apply AF_Inr2. exact Hfree.
  - f_equal.
    + apply IHe1. intros Hfree. apply Hnot. apply AF_CaseScrut. exact Hfree.
    + destruct (String.eqb_spec x v) as [Heq | Hneq].
      * reflexivity.
      * apply IHe2. intros Hfree. apply Hnot.
        apply AF_CaseLeft; assumption.
    + destruct (String.eqb_spec x v0) as [Heq | Hneq].
      * reflexivity.
      * apply IHe3. intros Hfree. apply Hnot.
        apply AF_CaseRight; assumption.
  - f_equal.
    + apply IHe1. intros Hfree. apply Hnot. apply AF_EqTy. exact Hfree.
    + apply IHe2. intros Hfree. apply Hnot. apply AF_EqLeft. exact Hfree.
    + apply IHe3. intros Hfree. apply Hnot. apply AF_EqRight. exact Hfree.
  - f_equal. apply IHe. intros Hfree. apply Hnot. apply AF_Refl. exact Hfree.
  - f_equal.
    + apply IHe1. intros Hfree. apply Hnot. apply AF_EqElimP. exact Hfree.
    + apply IHe2. intros Hfree. apply Hnot. apply AF_EqElimLeft. exact Hfree.
    + apply IHe3. intros Hfree. apply Hnot. apply AF_EqElimRight. exact Hfree.
    + apply IHe4. intros Hfree. apply Hnot. apply AF_EqElimProof. exact Hfree.
    + apply IHe5. intros Hfree. apply Hnot. apply AF_EqElimBody. exact Hfree.
  - f_equal.
    + apply IHe1. intros Hfree. apply Hnot. apply AF_Plus1. exact Hfree.
    + apply IHe2. intros Hfree. apply Hnot. apply AF_Plus2. exact Hfree.
  - f_equal.
    + apply IHe1. intros Hfree. apply Hnot. apply AF_Minus1. exact Hfree.
    + apply IHe2. intros Hfree. apply Hnot. apply AF_Minus2. exact Hfree.
Qed.

Lemma subst_closed :
  forall e x s,
    closed e ->
    subst x s e = e.
Proof.
  intros e x s Hclosed. apply subst_not_free. apply Hclosed.
Qed.

Lemma subst_replacement_defeq :
  forall e x s s',
    defeq s s' ->
    defeq (subst x s e) (subst x s' e).
Proof.
  induction e; intros x s s' Hdef; simpl; try apply DE_Refl.
  - destruct (String.eqb x v); [assumption | apply DE_Refl].
  - apply DE_Let.
    + apply IHe1. assumption.
    + destruct (String.eqb x v); [apply DE_Refl | apply IHe2; assumption].
  - apply DE_Pi.
    + apply IHe1. assumption.
    + destruct (String.eqb x v); [apply DE_Refl | apply IHe2; assumption].
  - apply DE_Lam.
    + apply IHe1. assumption.
    + destruct (String.eqb x v); [apply DE_Refl | apply IHe2; assumption].
  - apply DE_App; [apply IHe1 | apply IHe2]; assumption.
  - apply DE_Sigma.
    + apply IHe1. assumption.
    + destruct (String.eqb x v); [apply DE_Refl | apply IHe2; assumption].
  - apply DE_Pair; [apply IHe1 | apply IHe2]; assumption.
  - apply DE_Fst. apply IHe. assumption.
  - apply DE_Snd. apply IHe. assumption.
  - apply DE_Sum; [apply IHe1 | apply IHe2]; assumption.
  - apply DE_Inl; [apply IHe1 | apply IHe2]; assumption.
  - apply DE_Inr; [apply IHe1 | apply IHe2]; assumption.
  - apply DE_Case.
    + apply IHe1. assumption.
    + destruct (String.eqb x v); [apply DE_Refl | apply IHe2; assumption].
    + destruct (String.eqb x v0); [apply DE_Refl | apply IHe3; assumption].
  - apply DE_Eq; [apply IHe1 | apply IHe2 | apply IHe3]; assumption.
  - apply DE_ReflTm. apply IHe. assumption.
  - apply DE_EqElim;
      [apply IHe1 | apply IHe2 | apply IHe3 | apply IHe4 | apply IHe5];
      assumption.
  - apply DE_Plus; [apply IHe1 | apply IHe2]; assumption.
  - apply DE_Minus; [apply IHe1 | apply IHe2]; assumption.
Qed.

Lemma canonical_bool :
  forall Delta Omega v,
    has_type Delta Omega [] v tBool ->
    value v ->
    v = tTrue \/ v = tFalse.
Proof.
Admitted.

Lemma canonical_int :
  forall Delta Omega v,
    has_type Delta Omega [] v tInt ->
    value v ->
    exists z, v = tIntLit z.
Proof.
Admitted.

Lemma canonical_pi :
  forall Delta Omega v x T U,
    has_type Delta Omega [] v (tPi x T U) ->
    value v ->
    exists e, v = tLam x T e.
Proof.
Admitted.

Lemma canonical_sigma :
  forall Delta Omega v x T U,
    has_type Delta Omega [] v (tSigma x T U) ->
    value v ->
    exists v1 v2, v = tPair v1 v2 /\ value v1 /\ value v2.
Proof.
Admitted.

Lemma canonical_sum :
  forall Delta Omega v T U,
    has_type Delta Omega [] v (tSum T U) ->
    value v ->
    (exists v1, v = tInl U v1 /\ value v1) \/
    (exists v2, v = tInr T v2 /\ value v2).
Proof.
Admitted.

Lemma canonical_eq_proof :
  forall Delta Omega v T e e',
    has_type Delta Omega [] v (tEq T e e') ->
    value v ->
    exists w, v = tRefl w /\ e = w /\ e' = w /\ value w.
Proof.
Admitted.

Lemma free_in_context :
  forall Delta Omega Gamma e T x,
    appears_free_in x e ->
    has_type Delta Omega Gamma e T ->
    exists U, lookup x Gamma = Some U.
Proof.
Admitted.

Lemma typed_empty_closed :
  forall Delta Omega e T,
    has_type Delta Omega [] e T ->
    closed e.
Proof.
  unfold closed. intros Delta Omega e T HT x Hfree.
  destruct (free_in_context Delta Omega [] e T x Hfree HT) as [U Hlookup].
  discriminate.
Qed.

Lemma substitution_preserves_typing :
  forall Delta Omega Gamma x U e v T,
    wf_context Delta Omega (extend Gamma x U) ->
    closed_context Gamma ->
    closed v ->
    has_type Delta Omega (extend Gamma x U) e T ->
    has_type Delta Omega Gamma v U ->
    has_type Delta Omega Gamma (subst x v e) (subst x v T).
Proof.
  (**
    The intended proof is by induction on the first typing derivation.  The
    strengthened conclusion accounts for dependency in the result type:
    substitution acts on both the subject and its type.  The additional
    well-formedness and closedness hypotheses are the side conditions needed
    for the named-variable presentation used in this development.
   *)
Admitted.

Lemma wf_singleton_empty :
  forall Delta Omega x T s,
    has_type Delta Omega [] T (tSort s) ->
    wf_context Delta Omega (extend [] x T).
Proof.
  intros Delta Omega x T s HT.
  apply WF_Extend with (s := s).
  - apply WF_Empty.
  - exact (typed_empty_closed Delta Omega T (tSort s) HT).
  - exact HT.
Qed.

Lemma substitution_preserves_typing_empty :
  forall Delta Omega x U e v T s,
    has_type Delta Omega [] U (tSort s) ->
    has_type Delta Omega (extend [] x U) e T ->
    has_type Delta Omega [] v U ->
    has_type Delta Omega [] (subst x v e) (subst x v T).
Proof.
  intros Delta Omega x U e v T s HU He Hv.
  eapply substitution_preserves_typing.
  - apply wf_singleton_empty with (s := s). exact HU.
  - apply closed_context_empty.
  - exact (typed_empty_closed Delta Omega v U Hv).
  - exact He.
  - exact Hv.
Qed.

Lemma preservation_rebuild_let_step :
  forall Delta x e1 e1' e2 T T' U s,
    has_type Delta [] [] T (tSort s) ->
    has_type Delta [] [] e1' T' ->
    defeq T T' ->
    defeq e1 e1' ->
    has_type Delta [] (extend [] x T) e2 U ->
    exists R,
      has_type Delta [] [] (tLet x e1' e2) R /\
      defeq (subst x e1 U) R.
Proof.
  intros Delta x e1 e1' e2 T T' U s HTy He1' HTdef Hedef He2.
  exists (subst x e1' U). split.
  - eapply T_Let.
    + exact HTy.
    + eapply T_Conv.
      * exact He1'.
      * apply DE_Sym. exact HTdef.
    + exact He2.
  - apply subst_replacement_defeq. exact Hedef.
Qed.

Lemma preservation_rebuild_pair_left :
  forall Delta x e1 e1' e2 T T' U s,
    has_type Delta [] [] (tSigma x T U) (tSort s) ->
    has_type Delta [] [] e1' T' ->
    defeq T T' ->
    defeq e1 e1' ->
    has_type Delta [] [] e2 (subst x e1 U) ->
    exists R,
      has_type Delta [] [] (tPair e1' e2) R /\
      defeq (tSigma x T U) R.
Proof.
  intros Delta x e1 e1' e2 T T' U s HSigma He1' HTdef Hedef He2.
  exists (tSigma x T U). split.
  - eapply T_Pair.
    + exact HSigma.
    + eapply T_Conv.
      * exact He1'.
      * apply DE_Sym. exact HTdef.
    + eapply T_Conv.
      * exact He2.
      * apply subst_replacement_defeq. exact Hedef.
  - apply DE_Refl.
Qed.

Lemma preservation_rebuild_pair_right :
  forall Delta x v1 e2' T U T' s,
    has_type Delta [] [] (tSigma x T U) (tSort s) ->
    has_type Delta [] [] v1 T ->
    has_type Delta [] [] e2' T' ->
    defeq (subst x v1 U) T' ->
    exists R,
      has_type Delta [] [] (tPair v1 e2') R /\
      defeq (tSigma x T U) R.
Proof.
  intros Delta x v1 e2' T U T' s HSigma Hv1 He2' Hdef.
  exists (tSigma x T U). split.
  - eapply T_Pair.
    + exact HSigma.
    + exact Hv1.
    + eapply T_Conv.
      * exact He2'.
      * apply DE_Sym. exact Hdef.
  - apply DE_Refl.
Qed.

Lemma preservation_rebuild_app_left :
  forall Delta e1' e2 x T U T',
    has_type Delta [] [] e1' T' ->
    defeq (tPi x T U) T' ->
    has_type Delta [] [] e2 T ->
    exists R,
      has_type Delta [] [] (tApp e1' e2) R /\
      defeq (subst x e2 U) R.
Proof.
  intros Delta e1' e2 x T U T' He1' Hdef He2.
  exists (subst x e2 U). split.
  - eapply T_App.
    + eapply T_Conv.
      * exact He1'.
      * apply DE_Sym. exact Hdef.
    + exact He2.
  - apply DE_Refl.
Qed.

Lemma preservation_rebuild_app_right :
  forall Delta v1 e2 e2' x T U T',
    has_type Delta [] [] v1 (tPi x T U) ->
    has_type Delta [] [] e2' T' ->
    defeq T T' ->
    defeq e2 e2' ->
    exists R,
      has_type Delta [] [] (tApp v1 e2') R /\
      defeq (subst x e2 U) R.
Proof.
  intros Delta v1 e2 e2' x T U T' Hv1 He2' HTdef Hedef.
  exists (subst x e2' U). split.
  - eapply T_App.
    + exact Hv1.
    + eapply T_Conv.
      * exact He2'.
      * apply DE_Sym. exact HTdef.
  - apply subst_replacement_defeq. exact Hedef.
Qed.

Lemma preservation_rebuild_fst_step :
  forall Delta e' x T U T',
    has_type Delta [] [] e' T' ->
    defeq (tSigma x T U) T' ->
    exists R,
      has_type Delta [] [] (tFst e') R /\
      defeq T R.
Proof.
  intros Delta e' x T U T' He' Hdef.
  exists T. split.
  - eapply T_Fst. eapply T_Conv.
    + exact He'.
    + apply DE_Sym. exact Hdef.
  - apply DE_Refl.
Qed.

Lemma preservation_rebuild_snd_step :
  forall Delta e e' x T U T',
    has_type Delta [] [] e' T' ->
    defeq (tSigma x T U) T' ->
    defeq e e' ->
    exists R,
      has_type Delta [] [] (tSnd e') R /\
      defeq (subst x (tFst e) U) R.
Proof.
  intros Delta e e' x T U T' He' HTdef Hedef.
  exists (subst x (tFst e') U). split.
  - eapply T_Snd. eapply T_Conv.
    + exact He'.
    + apply DE_Sym. exact HTdef.
  - apply subst_replacement_defeq. apply DE_Fst. exact Hedef.
Qed.

Lemma preservation_rebuild_plus_left :
  forall Delta e1' e2 T',
    has_type Delta [] [] e1' T' ->
    defeq tInt T' ->
    has_type Delta [] [] e2 tInt ->
    exists R,
      has_type Delta [] [] (tPlus e1' e2) R /\
      defeq tInt R.
Proof.
  intros Delta e1' e2 T' He1' Hdef He2.
  exists tInt. split.
  - apply T_Plus.
    + eapply T_Conv; [exact He1' | apply DE_Sym; exact Hdef].
    + exact He2.
  - apply DE_Refl.
Qed.

Lemma preservation_rebuild_plus_right :
  forall Delta v1 e2' T',
    has_type Delta [] [] v1 tInt ->
    has_type Delta [] [] e2' T' ->
    defeq tInt T' ->
    exists R,
      has_type Delta [] [] (tPlus v1 e2') R /\
      defeq tInt R.
Proof.
  intros Delta v1 e2' T' Hv1 He2' Hdef.
  exists tInt. split.
  - apply T_Plus.
    + exact Hv1.
    + eapply T_Conv; [exact He2' | apply DE_Sym; exact Hdef].
  - apply DE_Refl.
Qed.

Lemma preservation_rebuild_minus_left :
  forall Delta e1' e2 T',
    has_type Delta [] [] e1' T' ->
    defeq tInt T' ->
    has_type Delta [] [] e2 tInt ->
    exists R,
      has_type Delta [] [] (tMinus e1' e2) R /\
      defeq tInt R.
Proof.
  intros Delta e1' e2 T' He1' Hdef He2.
  exists tInt. split.
  - apply T_Minus.
    + eapply T_Conv; [exact He1' | apply DE_Sym; exact Hdef].
    + exact He2.
  - apply DE_Refl.
Qed.

Lemma preservation_rebuild_minus_right :
  forall Delta v1 e2' T',
    has_type Delta [] [] v1 tInt ->
    has_type Delta [] [] e2' T' ->
    defeq tInt T' ->
    exists R,
      has_type Delta [] [] (tMinus v1 e2') R /\
      defeq tInt R.
Proof.
  intros Delta v1 e2' T' Hv1 He2' Hdef.
  exists tInt. split.
  - apply T_Minus.
    + exact Hv1.
    + eapply T_Conv; [exact He2' | apply DE_Sym; exact Hdef].
  - apply DE_Refl.
Qed.

Lemma preservation_rebuild_inl_step :
  forall Delta U e' T T' s1 s2,
    has_type Delta [] [] T (tSort s1) ->
    has_type Delta [] [] e' T' ->
    defeq T T' ->
    has_type Delta [] [] U (tSort s2) ->
    exists R,
      has_type Delta [] [] (tInl U e') R /\
      defeq (tSum T U) R.
Proof.
  intros Delta U e' T T' s1 s2 HT He' Hdef HU.
  exists (tSum T U). split.
  - eapply T_Inl.
    + exact HT.
    + eapply T_Conv; [exact He' | apply DE_Sym; exact Hdef].
    + exact HU.
  - apply DE_Refl.
Qed.

Lemma preservation_rebuild_inr_step :
  forall Delta T e' U U' s1 s2,
    has_type Delta [] [] e' U' ->
    defeq U U' ->
    has_type Delta [] [] T (tSort s1) ->
    has_type Delta [] [] U (tSort s2) ->
    exists R,
      has_type Delta [] [] (tInr T e') R /\
      defeq (tSum T U) R.
Proof.
  intros Delta T e' U U' s1 s2 He' Hdef HT HU.
  exists (tSum T U). split.
  - eapply T_Inr.
    + eapply T_Conv; [exact He' | apply DE_Sym; exact Hdef].
    + exact HT.
    + exact HU.
  - apply DE_Refl.
Qed.

Lemma preservation_rebuild_case_step :
  forall Delta e' x el y er T U R S,
    has_type Delta [] [] e' S ->
    defeq (tSum T U) S ->
    has_type Delta [] (extend [] x T) el R ->
    has_type Delta [] (extend [] y U) er R ->
    exists R',
      has_type Delta [] [] (tCase e' x el y er) R' /\
      defeq R R'.
Proof.
  intros Delta e' x el y er T U R S He' Hdef Hel Her.
  exists R. split.
  - eapply T_Case.
    + eapply T_Conv; [exact He' | apply DE_Sym; exact Hdef].
    + exact Hel.
    + exact Her.
  - apply DE_Refl.
Qed.

Lemma preservation_rebuild_refl_step :
  forall Delta e e' T T' s,
    has_type Delta [] [] T (tSort s) ->
    has_type Delta [] [] e' T' ->
    defeq T T' ->
    defeq e e' ->
    exists R,
      has_type Delta [] [] (tRefl e') R /\
      defeq (tEq T e e) R.
Proof.
  intros Delta e e' T T' s HT He' HTdef Hedef.
  exists (tEq T e' e'). split.
  - eapply T_Refl.
    + exact HT.
    + eapply T_Conv; [exact He' | apply DE_Sym; exact HTdef].
  - apply DE_Eq; [apply DE_Refl | exact Hedef | exact Hedef].
Qed.

Lemma preservation_rebuild_eqelim_proof_step :
  forall Delta P e e' p' q x T s S,
    has_type Delta [] [] P (tPi x T (tSort s)) ->
    has_type Delta [] [] p' S ->
    defeq (tEq T e e') S ->
    has_type Delta [] [] q (tApp P e) ->
    exists R,
      has_type Delta [] [] (tEqElim P e e' p' q) R /\
      defeq (tApp P e') R.
Proof.
  intros Delta P e e' p' q x T s S HP Hp' Hdef Hq.
  exists (tApp P e'). split.
  - eapply T_EqElim.
    + exact HP.
    + eapply T_Conv; [exact Hp' | apply DE_Sym; exact Hdef].
    + exact Hq.
  - apply DE_Refl.
Qed.

Lemma preservation_rebuild_eqelim_body_step :
  forall Delta P e e' p q' x T s S,
    has_type Delta [] [] P (tPi x T (tSort s)) ->
    has_type Delta [] [] p (tEq T e e') ->
    has_type Delta [] [] q' S ->
    defeq (tApp P e) S ->
    exists R,
      has_type Delta [] [] (tEqElim P e e' p q') R /\
      defeq (tApp P e') R.
Proof.
  intros Delta P e e' p q' x T s S HP Hp Hq' Hdef.
  exists (tApp P e'). split.
  - eapply T_EqElim.
    + exact HP.
    + exact Hp.
    + eapply T_Conv; [exact Hq' | apply DE_Sym; exact Hdef].
  - apply DE_Refl.
Qed.

Lemma step_defeq :
  forall e e',
    step e e' ->
    defeq e e'.
Proof.
  intros e e' Hstep.
  induction Hstep.
  - apply DE_Let. assumption. apply DE_Refl.
  - apply DE_LetBeta. assumption.
  - apply DE_App. assumption. apply DE_Refl.
  - apply DE_App. apply DE_Refl. assumption.
  - apply DE_Beta. assumption.
  - apply DE_Pair. assumption. apply DE_Refl.
  - apply DE_Pair. apply DE_Refl. assumption.
  - apply DE_Fst. assumption.
  - apply DE_FstPair; assumption.
  - apply DE_Snd. assumption.
  - apply DE_SndPair; assumption.
  - apply DE_Inl. apply DE_Refl. assumption.
  - apply DE_Inr. apply DE_Refl. assumption.
  - apply DE_Case. assumption. apply DE_Refl. apply DE_Refl.
  - apply DE_CaseInl. assumption.
  - apply DE_CaseInr. assumption.
  - apply DE_EqElim.
    + apply DE_Refl.
    + apply DE_Refl.
    + apply DE_Refl.
    + assumption.
    + apply DE_Refl.
  - apply DE_EqElim.
    + apply DE_Refl.
    + apply DE_Refl.
    + apply DE_Refl.
    + apply DE_Refl.
    + assumption.
  - apply DE_EqElimRefl. assumption.
  - apply DE_ReflTm. assumption.
  - apply DE_Plus. assumption. apply DE_Refl.
  - apply DE_Plus. apply DE_Refl. assumption.
  - apply DE_PlusInts.
  - apply DE_Minus. assumption. apply DE_Refl.
  - apply DE_Minus. apply DE_Refl. assumption.
  - apply DE_MinusInts.
Qed.

Definition progresses (e : tm) : Prop :=
  value e \/ exists e', step e e'.

