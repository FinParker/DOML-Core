From Stdlib Require Import Strings.String.
From DOMLCore Require Import Syntax.

Fixpoint subst (x : var) (s : tm) (e : tm) : tm :=
  match e with
  | tSort n => tSort n
  | tBool => tBool
  | tInt => tInt
  | tUnit => tUnit
  | tEmpty => tEmpty
  | tTrue => tTrue
  | tFalse => tFalse
  | tIntLit z => tIntLit z
  | tUnitLit => tUnitLit
  | tVar y => if String.eqb x y then s else tVar y
  | tLet y e1 e2 =>
      tLet y (subst x s e1)
        (if String.eqb x y then e2 else subst x s e2)
  | tPi y T U =>
      tPi y (subst x s T)
        (if String.eqb x y then U else subst x s U)
  | tLam y T e1 =>
      tLam y (subst x s T)
        (if String.eqb x y then e1 else subst x s e1)
  | tApp e1 e2 => tApp (subst x s e1) (subst x s e2)
  | tSigma y T U =>
      tSigma y (subst x s T)
        (if String.eqb x y then U else subst x s U)
  | tPair e1 e2 => tPair (subst x s e1) (subst x s e2)
  | tFst e1 => tFst (subst x s e1)
  | tSnd e1 => tSnd (subst x s e1)
  | tSum T U => tSum (subst x s T) (subst x s U)
  | tInl U e1 => tInl (subst x s U) (subst x s e1)
  | tInr T e1 => tInr (subst x s T) (subst x s e1)
  | tCase e0 y el z er =>
      tCase (subst x s e0)
        y (if String.eqb x y then el else subst x s el)
        z (if String.eqb x z then er else subst x s er)
  | tEq T e1 e2 => tEq (subst x s T) (subst x s e1) (subst x s e2)
  | tRefl e1 => tRefl (subst x s e1)
  | tDom d => tDom d
  | tIntroDom d args proof => tIntroDom d (subst x s args) (subst x s proof)
  | tPlus e1 e2 => tPlus (subst x s e1) (subst x s e2)
  | tMinus e1 e2 => tMinus (subst x s e1) (subst x s e2)
  end.

