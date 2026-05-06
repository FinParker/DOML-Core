From Stdlib Require Import Arith.PeanoNat.
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
| V_Refl : forall v, value v -> value (tRefl v)
| V_Dom : forall d, value (tDom d)
| V_IntroDom : forall d args proof,
    value args -> value proof -> value (tIntroDom d args proof).

Inductive has_type : dom_context -> context -> tm -> tm -> Prop :=
| T_Sort : forall Delta Gamma s,
    has_type Delta Gamma (tSort s) (tSort (S s))
| T_Bool : forall Delta Gamma,
    has_type Delta Gamma tBool (tSort 0)
| T_Int : forall Delta Gamma,
    has_type Delta Gamma tInt (tSort 0)
| T_Unit : forall Delta Gamma,
    has_type Delta Gamma tUnit (tSort 0)
| T_Empty : forall Delta Gamma,
    has_type Delta Gamma tEmpty (tSort 0)
| T_True : forall Delta Gamma,
    has_type Delta Gamma tTrue tBool
| T_False : forall Delta Gamma,
    has_type Delta Gamma tFalse tBool
| T_IntLit : forall Delta Gamma z,
    has_type Delta Gamma (tIntLit z) tInt
| T_UnitLit : forall Delta Gamma,
    has_type Delta Gamma tUnitLit tUnit
| T_Var : forall Delta Gamma x T,
    lookup x Gamma = Some T ->
    has_type Delta Gamma (tVar x) T
| T_Let : forall Delta Gamma x e1 e2 T U,
    has_type Delta Gamma e1 T ->
    has_type Delta (extend Gamma x T) e2 U ->
    has_type Delta Gamma (tLet x e1 e2) U
| T_Pi : forall Delta Gamma x T U s1 s2,
    has_type Delta Gamma T (tSort s1) ->
    has_type Delta (extend Gamma x T) U (tSort s2) ->
    has_type Delta Gamma (tPi x T U) (tSort (Nat.max s1 s2))
| T_Lam : forall Delta Gamma x T e U,
    has_type Delta (extend Gamma x T) e U ->
    has_type Delta Gamma (tLam x T e) (tPi x T U)
| T_App : forall Delta Gamma e1 e2 x T U,
    has_type Delta Gamma e1 (tPi x T U) ->
    has_type Delta Gamma e2 T ->
    has_type Delta Gamma (tApp e1 e2) (subst x e2 U)
| T_Sigma : forall Delta Gamma x T U s1 s2,
    has_type Delta Gamma T (tSort s1) ->
    has_type Delta (extend Gamma x T) U (tSort s2) ->
    has_type Delta Gamma (tSigma x T U) (tSort (Nat.max s1 s2))
| T_Pair : forall Delta Gamma x e1 e2 T U,
    has_type Delta Gamma e1 T ->
    has_type Delta Gamma e2 (subst x e1 U) ->
    has_type Delta Gamma (tPair e1 e2) (tSigma x T U)
| T_Fst : forall Delta Gamma e x T U,
    has_type Delta Gamma e (tSigma x T U) ->
    has_type Delta Gamma (tFst e) T
| T_Snd : forall Delta Gamma e x T U,
    has_type Delta Gamma e (tSigma x T U) ->
    has_type Delta Gamma (tSnd e) (subst x (tFst e) U)
| T_Sum : forall Delta Gamma T U s1 s2,
    has_type Delta Gamma T (tSort s1) ->
    has_type Delta Gamma U (tSort s2) ->
    has_type Delta Gamma (tSum T U) (tSort (Nat.max s1 s2))
| T_Inl : forall Delta Gamma U e T s,
    has_type Delta Gamma e T ->
    has_type Delta Gamma U (tSort s) ->
    has_type Delta Gamma (tInl U e) (tSum T U)
| T_Inr : forall Delta Gamma T e U s,
    has_type Delta Gamma e U ->
    has_type Delta Gamma T (tSort s) ->
    has_type Delta Gamma (tInr T e) (tSum T U)
| T_Case : forall Delta Gamma e x el y er T U R,
    has_type Delta Gamma e (tSum T U) ->
    has_type Delta (extend Gamma x T) el R ->
    has_type Delta (extend Gamma y U) er R ->
    has_type Delta Gamma (tCase e x el y er) R
| T_Eq : forall Delta Gamma T e1 e2 s,
    has_type Delta Gamma T (tSort s) ->
    has_type Delta Gamma e1 T ->
    has_type Delta Gamma e2 T ->
    has_type Delta Gamma (tEq T e1 e2) (tSort 0)
| T_Refl : forall Delta Gamma e T,
    has_type Delta Gamma e T ->
    has_type Delta Gamma (tRefl e) (tEq T e e)
| T_Dom : forall Delta Gamma d ent,
    lookup d Delta = Some ent ->
    has_type Delta Gamma (tDom d) (tSort 0)
| T_IntroDom : forall Delta Gamma d ent args proof,
    lookup d Delta = Some ent ->
    has_type Delta Gamma args (elab_tree (de_tree ent)) ->
    has_type Delta Gamma proof
      (tEq tBool (tApp (de_constraint ent) args) tTrue) ->
    has_type Delta Gamma (tIntroDom d args proof) (tDom d)
| T_Plus : forall Delta Gamma e1 e2,
    has_type Delta Gamma e1 tInt ->
    has_type Delta Gamma e2 tInt ->
    has_type Delta Gamma (tPlus e1 e2) tInt
| T_Minus : forall Delta Gamma e1 e2,
    has_type Delta Gamma e1 tInt ->
    has_type Delta Gamma e2 tInt ->
    has_type Delta Gamma (tMinus e1 e2) tInt.

Hint Constructors value has_type : core.

