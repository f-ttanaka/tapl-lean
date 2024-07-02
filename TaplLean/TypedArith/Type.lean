import TaplLean.TypedArith.Arith

inductive Ty : Type where
  | TNat
  | TBool
  deriving DecidableEq

open Term
open Ty

-- 型付け関係
inductive WellTyped : Term → Ty → Prop where
  | wt_tru : WellTyped tru TBool
  | wt_fls : WellTyped fls TBool
  | wt_if : ∀ {t1 t2 t3 : Term} {T : Ty},
      WellTyped t1 TBool → WellTyped t2 T → WellTyped t3 T
      → WellTyped (ite t1 t2 t3) T
  | wt_zero : WellTyped zero TNat
  | wt_succ : ∀ {t : Term},
      WellTyped t TNat → WellTyped (succ t) TNat
  | wt_pred : ∀ {t : Term},
      WellTyped t TNat → WellTyped (pred t) TNat
  | wt_iszero : ∀ {t : Term},
      WellTyped t TNat → WellTyped (iszero t) TBool

notation:10 "⊢ " e " : " τ => WellTyped e τ

open WellTyped

example : ⊢ pred (succ (pred (succ zero))) : TNat := by
  apply wt_pred
  apply wt_succ
  apply wt_pred
  apply wt_succ
  apply wt_zero
  done

-- 補題8.2.2 逆転補題 START
theorem rev_ty_tru : ∀ {T : Ty}, (⊢ tru : T) → T = TBool := by
  intro T h
  cases h
  rfl

theorem rev_ty_fls : ∀ {T : Ty}, (⊢ fls : T) → T = TBool := by
  intro T h
  cases h
  rfl

theorem rev_ty_ite : ∀ {T : Ty} {t1 t2 t3 : Term},
  (⊢ ite t1 t2 t3 : T) → WellTyped t1 TBool ∧ WellTyped t2 T ∧ WellTyped t3 T
  := by
  intro T t1 t2 t3 h
  cases h
  apply And.intro; assumption
  apply And.intro <;> assumption

theorem rev_ty_zero : ∀ {T : Ty}, (⊢ zero : T) → T = TNat := by
  intro T h; cases h; rfl

theorem rev_ty_succ :
  ∀ {T : Ty} {t : Term}, (⊢ succ t : T) → T = TNat ∧ (⊢ t : TNat)
  := by
  intro T t h; cases h
  apply And.intro; rfl; assumption

theorem rev_ty_pred :
  ∀ {T : Ty} {t : Term}, (⊢ pred t : T) → T = TNat ∧ (⊢ t : TNat)
  := by
  intro T t h; cases h
  apply And.intro; rfl; assumption

theorem rev_ty_iszero :
  ∀ {T : Ty} {t : Term}, (⊢ iszero t : T) → T = TBool ∧ (⊢ t : TNat)
  := by
  intro T t h; cases h
  apply And.intro; rfl; assumption
-- 補題8.2.2 逆転補題 END

-- 演習8.2.3 START
def hasType (t : Term) : Prop := ∃ (T : Ty), WellTyped t T

theorem sub_ty_ite :
  ∀ {t1 t2 t3 : Term},
    hasType (ite t1 t2 t3) → hasType t1 ∧ hasType t2 ∧ hasType t3
  := by
  intro t1 t2 t3 h; cases h; rename_i T h
  have h_subs := rev_ty_ite h
  have h1 := h_subs.left
  have h2 := h_subs.right.left
  have h3 := h_subs.right.right
  -- hasType t1の証明
  apply And.intro
  exists TBool
  -- hasType t2 ∧ hasType t3 の証明
  apply And.intro <;> exists T

theorem sub_ty_succ :
  ∀ {t : Term}, hasType (succ t) → hasType t
  := by
  intro t h; cases h; rename_i T h
  have h_sub := (rev_ty_succ h).right
  exists TNat

theorem sub_ty_pred :
  ∀ {t : Term}, hasType (pred t) → hasType t
  := by
  intro t h; cases h; rename_i T h
  have h_sub := (rev_ty_pred h).right
  exists TNat

theorem sub_ty_iszero :
  ∀ {t : Term}, hasType (iszero t) → hasType t
  := by
  intro t h; cases h; rename_i T h
  have h_sub := (rev_ty_iszero h).right
  exists TNat
-- 演習8.2.3 END

-- 定理8.2.3 型の一意性
theorem ty_uniqueness :
  ∀ {t : Term} {T1 T2 : Ty},
    (⊢ t : T1) ∧ (⊢ t : T2) → T1 = T2
  := by
  sorry
