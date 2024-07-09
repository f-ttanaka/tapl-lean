import TaplLean.STLC.Env
import TaplLean.STLC.Internal

open Term
open Ty

-- 9.3.1 逆転補題
-- START
theorem ty_rev_var :
  ∀ Γ x T, (Γ ⊢ var x ∈: T) → Γ x = some T
  := by
  intro Γ x T HTx; cases HTx; assumption

theorem ty_rev_abs :
  ∀ Γ x t T1 S, (Γ ⊢ λ x : T1, t ∈: S) →
  ∃ T2, ((x |→ T1; Γ) ⊢ t ∈: T2) ∧ S = (T1 :-> T2)
  := by
  intro Γ x t T1 S HTl; cases HTl; rename_i T2 HTl; exists T2

theorem ty_rev_app :
  ∀ Γ t1 t2 T, (Γ ⊢ app t1 t2 ∈: T) →
  ∃ R, (Γ ⊢ t1 ∈: (R :-> T)) ∧ (Γ ⊢ t2 ∈: R)
  := by
  intro Γ t1 t2 T HT; cases HT; rename_i S _ _; exists S

theorem ty_rev_tru :
  ∀ Γ T, (Γ ⊢ tru ∈: T) → T = TBool
  := by
  intro Γ T HT; cases HT;
