import TaplLean.STLC.Env
import TaplLean.STLC.Internal

open Term
open Ty
open WellTyped

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
  intro Γ T HT; cases HT; rfl

theorem ty_rev_fls :
  ∀ Γ T, (Γ ⊢ fls ∈: T) → T = TBool
  := by
  intro Γ T HT; cases HT; rfl

theorem ty_rev_ite :
  ∀ Γ t1 t2 t3 T, (Γ ⊢ ite t1 t2 t3 ∈: T) →
    (Γ ⊢ t1 ∈: TBool) ∧ (Γ ⊢ t2 ∈: T) ∧ (Γ ⊢ t3 ∈: T)
  := by
  intro Γ t1 t2 t3 T HT; cases HT; rename_i HT1 HT2 HT3
  apply And.intro
  . assumption
  . apply And.intro <;> assumption

-- 演習9.3.2
-- x を変数として Γ ⊢ x x ∈: T となる Γ, T があるか
-- skip

-- 定理9.3.3 型の一意性
theorem uniqueness :
  ∀ {Γ t T1 T2},
  (Γ ⊢ t ∈: T1) → (Γ ⊢ t ∈: T2) → T1 = T2
  := by
  intro Γ t T1 T2 HT
  revert T1 T2 Γ
  induction t <;> intro Γ T1 T2 HT1 HT2
  -- tru
  . cases HT1; cases HT2; rfl
  . cases HT1; cases HT2; rfl
  . rename_i t1 t2 t3 _ IH2 _
    cases HT1; rename_i HT1_1 HT2_1 HT3_1;
    cases HT2; rename_i HT1_2 HT2_2 HT3_2;
    apply IH2 HT2_1 HT2_2
  . rename_i x; cases HT1; cases HT2; rename_i Eq1 Eq2
    rw [Eq1] at Eq2
    apply Option.some_inj.mp Eq2
  . rename_i x T t IH
    cases HT1; rename_i T1 HT1
    cases HT2; rename_i T2 HT2
    have HT_eq := IH HT1 HT2
    rw [HT_eq]
  . rename_i t1 t2 IH1 IH2
    cases HT1; rename_i T1' HT_t2_1 HT_t1_1
    cases HT2; rename_i T2' HT_t2_2 HT_t1_2
    have HT_eq1 := IH1 HT_t1_1 HT_t1_2
    have HT_eq2 := IH2 HT_t2_1 HT_t2_2
    rw [HT_eq2] at HT_eq1
    cases HT_eq1; rfl

-- 補題9.3.4 標準形
-- (1)
theorem bool_canonical :
  ∀ {v}, (Γ ⊢ v ∈: TBool) → Value v → v = tru ∨ v = fls
  := by
  intro v Ht Hv; cases Hv
  . apply Or.intro_left; rfl
  . apply Or.intro_right; rfl
  . cases Ht

-- (2)
theorem abs_canonical :
  ∀ {v T1 T2},
  (Γ ⊢ v ∈: T1 :-> T2) → Value v → ∃ x t2, v = λx:T1, t2
  := by
  intro v T1 T2 HT Hv; cases Hv <;> cases HT
  -- abs
  rename_i x t HT; exists x, t

-- 定理9.3.5 進行定理
-- 算術式とは違って閉じた (自由変数を持たない) 項でのみ成り立つ
theorem progress : ∀ {Γ t T},
  (Γ ⊢ t ∈: T) →
  Γ = empty →
  Value t ∨ ∃t', t -> t'
  := by
  intro Γ t T HT HE; induction HT
  -- wt_tru
  . apply Or.intro_left; apply Value.v_tru
  -- wt_fls
  . apply Or.intro_left; apply Value.v_fls
  -- wt_ite
  . apply Or.intro_right
    rename_i Γ' t1 t2 t3 _ HT_t1 _ _ IH1 _ _
    have IH1 := IH1 HE
    cases IH1
    . rename_i Hv
      have Hv_t1 := bool_canonical HT_t1 Hv
      cases Hv_t1 <;> rename_i Heq <;> rw [Heq]
      . exists t2; apply Step.st_if_tru
      . exists t3; apply Step.st_if_fls
    . rename_i Hst; cases Hst; rename_i t1' Hst
      exists ite t1' t2 t3
      apply Step.st_if Hst
  -- wt_var
  . rename_i _ _ _ Contra
    rw [HE] at Contra
    unfold empty at Contra
    cases Contra
  -- wt_abs
  . apply Or.intro_left
    apply Value.v_abs
  -- wt_app
  . apply Or.intro_right
    rename_i Γ t1 t2 T1 T2 HT_t1 _ IH1 IH2
    have IH1 := IH1 HE
    cases IH1 <;> rename_i Ht1
    . have IH2 := IH2 HE
      cases IH2 <;> rename_i Ht2
      . have Ht1_abs := abs_canonical HT_t1 Ht1
        cases Ht1_abs; rename_i y Ht1_abs
        cases Ht1_abs; rename_i t1' Ht1_abs; rw [Ht1_abs]
        exists ([y := t2] t1')
        apply Step.st_app_abs Ht2
      . cases Ht2; rename_i t2' Hst2
        exists app t1 t2'
        apply Step.st_app2 Ht1 Hst2
    . cases Ht1; rename_i t1' Hst1
      exists app t1' t2
      apply Step.st_app1 Hst1

-- 補題9.3.6 並べ替え
theorem ty_sorted : ∀ {Γ Δ t T},
  (Γ ⊢ t ∈: T) →
  sorted Γ Δ →
  (Δ ⊢ t ∈: T)
  := by
  intro Γ Δ t T HG Hs; induction HG
  . apply wt_tru
  . apply wt_fls
  . rename_i Γ' t1 t2 t3 T' _ _ _ IH1 IH2 IH3
    have HDT1 := IH1 Hs
    have HDT2 := IH2 Hs
    have HDT3 := IH3 Hs
    apply wt_ite HDT1 HDT2 HDT3
  . rename_i Γ x T HGx
    apply wt_var
    rw [← HGx]
    apply Eq.symm
    apply Hs
  . rename_i Γ x t1 T1 T2 HT_t1 IH
    have HT_t1 := wt_abs HT_t1
