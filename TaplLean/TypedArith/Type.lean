import TaplLean.TypedArith.Arith
open Term

inductive Ty : Type where
  | TNat
  | TBool

inductive HasTy : Term → Ty → Prop where
  | has_ty_tru : HasTy tru TBool
  | has_ty_fls : HasTy fls TBool
  | has_ty_if : ∀ {t1 t2 t3 : Term} {T : Ty},
      HasTy t1 TBool → HasTy t2 T → HasTy t3 T
      → HasTy (ite t1 t2 t3) T
  | has_ty_zero : HasTy zero TNat
  | has_ty_succ : ∀ {t : Term},
      HasTy t TNat → HasTy (succ t) TNat
  | has_ty_pred : ∀ {t : Term},
      HasTy t TNat → HasTy (pred t) TNat
  | has_ty_iszero : ∀ {t : Term},
      HasTy t TNat → HasTy (iszero t) TBool

notation:10 "⊢ " e " : " τ => HasTy e τ

open HasTy

example : ⊢ pred (succ (pred (succ zero))) : TNat := by
  apply has_ty_pred
  apply has_ty_succ
  apply has_ty_pred
  apply has_ty_succ
  apply has_ty_zero
  done

theorem rev_ty_tru : ∀ {T : Ty}, (⊢ tru : T) → T = TBool := by
  intros T h
  sorry
  -- have ht : ⊢ tru : TBool := has_ty_tru
