From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From DOMLCore Require Import Syntax Context Substitution.

Open Scope Z_scope.

Inductive value : tm -> Prop :=
| V_Sort : forall s, value (tSort s)
| V_BoolTy : value tBool
| V_IntTy : value tInt
| V_UnitTy : value tUnit
| V_EmptyTy : value tEmpty
| V_True : value tTrue
| V_False : value tFalse
| V_IntLit : forall z, value (tIntLit z)
| V_UnitLit : value tUnitLit
| V_Pi : forall x T U, value (tPi x T U)
| V_Lam : forall x T e, value (tLam x T e)
| V_Sigma : forall x T U, value (tSigma x T U)
| V_Pair : forall e1 v2, value v2 -> value (tPair e1 v2)
| V_Sum : forall T U, value (tSum T U)
| V_Inl : forall U v, value v -> value (tInl U v)
| V_Inr : forall T v, value v -> value (tInr T v)
| V_Eq : forall T e1 e2, value (tEq T e1 e2)
| V_Refl : forall v, value v -> value (tRefl v).

Inductive defeq : tm -> tm -> Prop :=
| DE_Refl : forall T, defeq T T
| DE_Sym : forall T U, defeq T U -> defeq U T
| DE_Trans : forall T U V, defeq T U -> defeq U V -> defeq T V
| DE_LetBeta : forall x v e,
    value v ->
    defeq (tLet x v e) (subst x v e)
| DE_Let : forall x e1 e1' e2 e2',
    defeq e1 e1' ->
    defeq e2 e2' ->
    defeq (tLet x e1 e2) (tLet x e1' e2')
| DE_Beta : forall x T e v,
    value v ->
    defeq (tApp (tLam x T e) v) (subst x v e)
| DE_FstPair : forall e1 v2,
    value v2 ->
    defeq (tFst (tPair e1 v2)) e1
| DE_SndPair : forall e1 v2,
    value v2 ->
    defeq (tSnd (tPair e1 v2)) v2
| DE_CaseInl : forall U v x el y er,
    value v ->
    defeq (tCase (tInl U v) x el y er) (subst x v el)
| DE_CaseInr : forall T v x el y er,
    value v ->
    defeq (tCase (tInr T v) x el y er) (subst y v er)
| DE_PlusInts : forall z1 z2,
    defeq (tPlus (tIntLit z1) (tIntLit z2)) (tIntLit (z1 + z2))
| DE_MinusInts : forall z1 z2,
    defeq (tMinus (tIntLit z1) (tIntLit (z2))) (tIntLit (z1 - z2))
| DE_App : forall e1 e1' e2 e2',
    defeq e1 e1' ->
    defeq e2 e2' ->
    defeq (tApp e1 e2) (tApp e1' e2')
| DE_Pi : forall x T T' U U',
    defeq T T' ->
    defeq U U' ->
    defeq (tPi x T U) (tPi x T' U')
| DE_Lam : forall x T T' e e',
    defeq T T' ->
    defeq e e' ->
    defeq (tLam x T e) (tLam x T' e')
| DE_Sigma : forall x T T' U U',
    defeq T T' ->
    defeq U U' ->
    defeq (tSigma x T U) (tSigma x T' U')
| DE_Sum : forall T T' U U',
    defeq T T' ->
    defeq U U' ->
    defeq (tSum T U) (tSum T' U')
| DE_Eq : forall T T' e1 e1' e2 e2',
    defeq T T' ->
    defeq e1 e1' ->
    defeq e2 e2' ->
    defeq (tEq T e1 e2) (tEq T' e1' e2')
| DE_Fst : forall e e',
    defeq e e' ->
    defeq (tFst e) (tFst e')
| DE_Snd : forall e e',
    defeq e e' ->
    defeq (tSnd e) (tSnd e')
| DE_Pair : forall e1 e1' e2 e2',
    defeq e1 e1' ->
    defeq e2 e2' ->
    defeq (tPair e1 e2) (tPair e1' e2')
| DE_Inl : forall U U' e e',
    defeq U U' ->
    defeq e e' ->
    defeq (tInl U e) (tInl U' e')
| DE_Inr : forall T T' e e',
    defeq T T' ->
    defeq e e' ->
    defeq (tInr T e) (tInr T' e')
| DE_Case : forall e e' x el el' y er er',
    defeq e e' ->
    defeq el el' ->
    defeq er er' ->
    defeq (tCase e x el y er) (tCase e' x el' y er')
| DE_ReflTm : forall e e',
    defeq e e' ->
    defeq (tRefl e) (tRefl e')
| DE_EqElim : forall P P' e e' u u' p p' q q',
    defeq P P' ->
    defeq e e' ->
    defeq u u' ->
    defeq p p' ->
    defeq q q' ->
    defeq (tEqElim P e u p q) (tEqElim P' e' u' p' q')
| DE_EqElimRefl : forall P e e' w q,
    value w ->
    defeq e w ->
    defeq e' w ->
    defeq (tEqElim P e e' (tRefl w) q) q
| DE_Plus : forall e1 e1' e2 e2',
    defeq e1 e1' ->
    defeq e2 e2' ->
    defeq (tPlus e1 e2) (tPlus e1' e2')
| DE_Minus : forall e1 e1' e2 e2',
    defeq e1 e1' ->
    defeq e2 e2' ->
    defeq (tMinus e1 e2) (tMinus e1' e2').

Inductive has_type : dom_context -> const_context -> context -> tm -> tm -> Prop :=
| T_Sort : forall Delta Omega Gamma s,
    has_type Delta Omega Gamma (tSort s) (tSort (S s))
| T_Bool : forall Delta Omega Gamma,
    has_type Delta Omega Gamma tBool (tSort 0)
| T_Int : forall Delta Omega Gamma,
    has_type Delta Omega Gamma tInt (tSort 0)
| T_Unit : forall Delta Omega Gamma,
    has_type Delta Omega Gamma tUnit (tSort 0)
| T_Empty : forall Delta Omega Gamma,
    has_type Delta Omega Gamma tEmpty (tSort 0)
| T_True : forall Delta Omega Gamma,
    has_type Delta Omega Gamma tTrue tBool
| T_False : forall Delta Omega Gamma,
    has_type Delta Omega Gamma tFalse tBool
| T_IntLit : forall Delta Omega Gamma z,
    has_type Delta Omega Gamma (tIntLit z) tInt
| T_UnitLit : forall Delta Omega Gamma,
    has_type Delta Omega Gamma tUnitLit tUnit
| T_Var : forall Delta Omega Gamma x T,
    lookup x Gamma = Some T ->
    has_type Delta Omega Gamma (tVar x) T
| T_Const : forall Delta Omega Gamma c T,
    lookup c Omega = Some T ->
    has_type Delta Omega Gamma (tConst c) T
| T_Let : forall Delta Omega Gamma x e1 e2 T U s,
    has_type Delta Omega Gamma T (tSort s) ->
    has_type Delta Omega Gamma e1 T ->
    has_type Delta Omega (extend Gamma x T) e2 U ->
    has_type Delta Omega Gamma (tLet x e1 e2) (subst x e1 U)
| T_Pi : forall Delta Omega Gamma x T U s1 s2,
    has_type Delta Omega Gamma T (tSort s1) ->
    has_type Delta Omega (extend Gamma x T) U (tSort s2) ->
    has_type Delta Omega Gamma (tPi x T U) (tSort (Nat.max s1 s2))
| T_Lam : forall Delta Omega Gamma x T e U s,
    has_type Delta Omega Gamma T (tSort s) ->
    has_type Delta Omega (extend Gamma x T) e U ->
    has_type Delta Omega Gamma (tLam x T e) (tPi x T U)
| T_App : forall Delta Omega Gamma e1 e2 x T U,
    has_type Delta Omega Gamma e1 (tPi x T U) ->
    has_type Delta Omega Gamma e2 T ->
    has_type Delta Omega Gamma (tApp e1 e2) (subst x e2 U)
| T_Sigma : forall Delta Omega Gamma x T U s1 s2,
    has_type Delta Omega Gamma T (tSort s1) ->
    has_type Delta Omega (extend Gamma x T) U (tSort s2) ->
    has_type Delta Omega Gamma (tSigma x T U) (tSort (Nat.max s1 s2))
| T_Pair : forall Delta Omega Gamma x e1 e2 T U s,
    has_type Delta Omega Gamma (tSigma x T U) (tSort s) ->
    has_type Delta Omega Gamma e1 T ->
    has_type Delta Omega Gamma e2 (subst x e1 U) ->
    has_type Delta Omega Gamma (tPair e1 e2) (tSigma x T U)
| T_Fst : forall Delta Omega Gamma e x T U,
    has_type Delta Omega Gamma e (tSigma x T U) ->
    has_type Delta Omega Gamma (tFst e) T
| T_Snd : forall Delta Omega Gamma e x T U,
    has_type Delta Omega Gamma e (tSigma x T U) ->
    has_type Delta Omega Gamma (tSnd e) (subst x (tFst e) U)
| T_Sum : forall Delta Omega Gamma T U s1 s2,
    has_type Delta Omega Gamma T (tSort s1) ->
    has_type Delta Omega Gamma U (tSort s2) ->
    has_type Delta Omega Gamma (tSum T U) (tSort (Nat.max s1 s2))
| T_Inl : forall Delta Omega Gamma U e T s1 s2,
    has_type Delta Omega Gamma T (tSort s1) ->
    has_type Delta Omega Gamma e T ->
    has_type Delta Omega Gamma U (tSort s2) ->
    has_type Delta Omega Gamma (tInl U e) (tSum T U)
| T_Inr : forall Delta Omega Gamma T e U s1 s2,
    has_type Delta Omega Gamma e U ->
    has_type Delta Omega Gamma T (tSort s1) ->
    has_type Delta Omega Gamma U (tSort s2) ->
    has_type Delta Omega Gamma (tInr T e) (tSum T U)
| T_Case : forall Delta Omega Gamma e x el y er T U R,
    has_type Delta Omega Gamma e (tSum T U) ->
    has_type Delta Omega (extend Gamma x T) el R ->
    has_type Delta Omega (extend Gamma y U) er R ->
    has_type Delta Omega Gamma (tCase e x el y er) R
| T_Eq : forall Delta Omega Gamma T e1 e2 s,
    has_type Delta Omega Gamma T (tSort s) ->
    has_type Delta Omega Gamma e1 T ->
    has_type Delta Omega Gamma e2 T ->
    has_type Delta Omega Gamma (tEq T e1 e2) (tSort 0)
| T_Refl : forall Delta Omega Gamma e T s,
    has_type Delta Omega Gamma T (tSort s) ->
    has_type Delta Omega Gamma e T ->
    has_type Delta Omega Gamma (tRefl e) (tEq T e e)
| T_EqElim : forall Delta Omega Gamma P e e' p q x T s,
    has_type Delta Omega Gamma P (tPi x T (tSort s)) ->
    has_type Delta Omega Gamma p (tEq T e e') ->
    has_type Delta Omega Gamma q (tApp P e) ->
    has_type Delta Omega Gamma (tEqElim P e e' p q) (tApp P e')
| T_DomainType : forall Delta Omega Gamma d ent s,
    lookup d Delta = Some ent ->
    has_type Delta Omega Gamma (elab_tree (de_tree ent)) (tSort s) ->
    has_type Delta Omega Gamma (de_constraint ent)
      (tPi "_args"%string (elab_tree (de_tree ent)) tBool) ->
    has_type Delta Omega Gamma (domain_type ent) (tSort 0)
| T_IntroDom : forall Delta Omega Gamma d ent args proof s,
    lookup d Delta = Some ent ->
    has_type Delta Omega Gamma (domain_type ent) (tSort s) ->
    has_type Delta Omega Gamma args (elab_tree (de_tree ent)) ->
    has_type Delta Omega Gamma proof
      (tEq tBool (tApp (de_constraint ent) args) tTrue) ->
    has_type Delta Omega Gamma (intro_dom args proof) (domain_type ent)
| T_Plus : forall Delta Omega Gamma e1 e2,
    has_type Delta Omega Gamma e1 tInt ->
    has_type Delta Omega Gamma e2 tInt ->
    has_type Delta Omega Gamma (tPlus e1 e2) tInt
| T_Minus : forall Delta Omega Gamma e1 e2,
    has_type Delta Omega Gamma e1 tInt ->
    has_type Delta Omega Gamma e2 tInt ->
    has_type Delta Omega Gamma (tMinus e1 e2) tInt.

Hint Constructors value : core.
Hint Resolve
  DE_Refl DE_LetBeta DE_Beta DE_FstPair DE_SndPair DE_CaseInl
  DE_Let DE_CaseInr DE_PlusInts DE_MinusInts DE_App DE_Pi DE_Lam DE_Sigma DE_Sum
  DE_Eq DE_Fst DE_Snd DE_Pair DE_Inl DE_Inr DE_Case DE_ReflTm
  DE_EqElim DE_EqElimRefl DE_Plus DE_Minus : core.
Hint Resolve
  T_Sort T_Bool T_Int T_Unit T_Empty T_True T_False T_IntLit T_UnitLit
  T_Var T_Const T_Let T_Pi T_Lam T_App T_Sigma T_Pair T_Fst T_Snd
  T_Sum T_Inl T_Inr T_Case T_Eq T_Refl T_EqElim T_DomainType
  T_IntroDom T_Plus T_Minus : core.

