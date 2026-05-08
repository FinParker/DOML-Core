From Stdlib Require Import ZArith.ZArith.
From DOMLCore Require Import Syntax Substitution Typing.

Open Scope Z_scope.

Inductive step : tm -> tm -> Prop :=
| ST_LetStep : forall x e1 e1' e2,
    step e1 e1' ->
    step (tLet x e1 e2) (tLet x e1' e2)
| ST_LetValue : forall x v e2,
    value v ->
    step (tLet x v e2) (subst x v e2)
| ST_App1 : forall e1 e1' e2,
    step e1 e1' ->
    step (tApp e1 e2) (tApp e1' e2)
| ST_App2 : forall v1 e2 e2',
    value v1 ->
    step e2 e2' ->
    step (tApp v1 e2) (tApp v1 e2')
| ST_Beta : forall x T e v,
    value v ->
    step (tApp (tLam x T e) v) (subst x v e)
| ST_Pair1 : forall e1 e1' e2,
    step e1 e1' ->
    step (tPair e1 e2) (tPair e1' e2)
| ST_Pair2 : forall v1 e2 e2',
    value v1 ->
    step e2 e2' ->
    step (tPair v1 e2) (tPair v1 e2')
| ST_FstStep : forall e e',
    step e e' ->
    step (tFst e) (tFst e')
| ST_FstPair : forall v1 v2,
    value v1 ->
    value v2 ->
    step (tFst (tPair v1 v2)) v1
| ST_SndStep : forall e e',
    step e e' ->
    step (tSnd e) (tSnd e')
| ST_SndPair : forall v1 v2,
    value v1 ->
    value v2 ->
    step (tSnd (tPair v1 v2)) v2
| ST_Inl : forall U e e',
    step e e' ->
    step (tInl U e) (tInl U e')
| ST_Inr : forall T e e',
    step e e' ->
    step (tInr T e) (tInr T e')
| ST_CaseStep : forall e e' x el y er,
    step e e' ->
    step (tCase e x el y er) (tCase e' x el y er)
| ST_CaseInl : forall U v x el y er,
    value v ->
    step (tCase (tInl U v) x el y er) (subst x v el)
| ST_CaseInr : forall T v x el y er,
    value v ->
    step (tCase (tInr T v) x el y er) (subst y v er)
| ST_EqElimProof : forall P e e' p p' q,
    step p p' ->
    step (tEqElim P e e' p q) (tEqElim P e e' p' q)
| ST_EqElimBody : forall P e e' p q q',
    value p ->
    step q q' ->
    step (tEqElim P e e' p q) (tEqElim P e e' p q')
| ST_EqElimRefl : forall P e q,
    value e ->
    step (tEqElim P e e (tRefl e) q) q
| ST_Refl : forall e e',
    step e e' ->
    step (tRefl e) (tRefl e')
| ST_Plus1 : forall e1 e1' e2,
    step e1 e1' ->
    step (tPlus e1 e2) (tPlus e1' e2)
| ST_Plus2 : forall v1 e2 e2',
    value v1 ->
    step e2 e2' ->
    step (tPlus v1 e2) (tPlus v1 e2')
| ST_PlusInts : forall z1 z2,
    step (tPlus (tIntLit z1) (tIntLit z2)) (tIntLit (z1 + z2))
| ST_Minus1 : forall e1 e1' e2,
    step e1 e1' ->
    step (tMinus e1 e2) (tMinus e1' e2)
| ST_Minus2 : forall v1 e2 e2',
    value v1 ->
    step e2 e2' ->
    step (tMinus v1 e2) (tMinus v1 e2')
| ST_MinusInts : forall z1 z2,
    step (tMinus (tIntLit z1) (tIntLit z2)) (tIntLit (z1 - z2)).

Hint Constructors step : core.

