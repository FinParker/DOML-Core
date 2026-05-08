From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Strings.String.
From DOMLCore Require Import Syntax Context Substitution.

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
| V_Pair : forall v1 v2, value v1 -> value v2 -> value (tPair v1 v2)
| V_Sum : forall T U, value (tSum T U)
| V_Inl : forall U v, value v -> value (tInl U v)
| V_Inr : forall T v, value v -> value (tInr T v)
| V_Eq : forall T e1 e2, value (tEq T e1 e2)
| V_Refl : forall v, value v -> value (tRefl v).

Inductive defeq : tm -> tm -> Prop :=
| DE_Refl : forall T, defeq T T.

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

Hint Constructors value defeq has_type : core.

