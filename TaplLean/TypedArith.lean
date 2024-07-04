inductive Term where
  | tru
  | fls
  | ite : Term → Term → Term → Term
  | zero
  | succ : Term → Term
  | pred : Term → Term
  | iszero : Term → Term
  deriving DecidableEq

inductive Step : Term → Term → Prop where
  | st_if_tru : ∀ {t1 t2: Term}, Step (Term.ite tru t1 t2) t1
  | st_if_fls : ∀ {t1 t2: Term}, Step (Term.ite fls t1 t2) t2
  | st_if : ∀ {t1 t1' t2 t3: Term},
      Step t1 t1' → Step (Term.ite t1 t2 t3) (Term.ite t1' t2 t3)
  | st_succ : ∀ {t1 t1' : Term},
      Step t1 t1' → Step (Term.succ t1) (Term.succ t1')
  | st_pred_0 : Step (Term.pred zero) zero
  | st_pred_succ : ∀ {t : Term},
      Step (Term.pred (Term.succ t)) t
  | st_pred : ∀ {t1 t1' : Term},
      Step t1 t1' → Step (Term.pred t1) (Term.pred t1')
  | st_iszero_0 : Step (Term.iszero zero) tru
  | st_iszero_succ : ∀ {t : Term},
      Step (Term.iszero (Term.succ t)) fls
  | st_iszero : ∀ {t1 t1' : Term},
      Step t1 t1' → Step (Term.iszero t1) (Term.iszero t1')

infix:100 " -> " => Step

example : Term.iszero (Term.succ (Term.succ zero)) -> fls := by
  apply Step.st_iszero_succ


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
  ∀ {t : Term} {T T' : Ty},
    (⊢ t : T) → (⊢ t : T') → T = T'
  := by
  intro t; induction t <;> intro T T' h h'
  -- tru
  . cases h; cases h'; rfl
  -- fls
  . cases h; cases h'; rfl
  -- ite
  . rename_i t1 t2 t3 _ ih2 _
    cases h; rename_i ht2 ht3
    cases h'; rename_i ht2' ht3'
    have t_eq := ih2 ht2 ht2'; assumption
  -- zero
  . cases h; cases h'; rfl
  -- succ
  . cases h; cases h'; rfl
  -- pred
  . cases h; cases h'; rfl
  -- iszero
  . cases h; cases h'; rfl

inductive NV : Term → Prop where
  | nv_zero : NV zero
  | nv_succ : ∀ {t : Term}, NV t → NV (Term.succ t)

inductive BV : Term → Prop where
  | bv_tru : BV tru
  | bv_fls : BV fls

def Value (t : Term) : Prop := BV t ∨ NV t

-- 補題8.3.1 標準形
theorem bool_canonical :
  ∀ {t : Term}, (⊢ t : TBool) → Value t → BV t
  := by
  intro t ht hv
  cases hv <;> rename_i hv
  . assumption
  . cases hv <;> cases ht

theorem nat_canonical :
  ∀ {t : Term}, (⊢ t : TNat) → Value t → NV t
  := by
  intro t ht hv
  cases hv <;> rename_i hv
  . cases ht <;> cases hv
  . assumption

-- 8.3.2 進行定理
theorem progress :
  ∀ {t : Term} {T : Ty},
    (⊢ t : T) → Value t ∨ ∃ t', t -> t'
  := by
  intro t T ht; induction ht
  . have t_bv := BV.bv_tru
    apply Or.inl; unfold Value; apply Or.inl; assumption
  . have t_bv := BV.bv_fls
    apply Or.inl; unfold Value; apply Or.inl; assumption
  -- ite
  . rename_i t1 t2 t3 _ ht1 _ _ ih1 _ _
    cases ih1 <;> rename_i ih1 <;> apply Or.inr
    . have h := bool_canonical ht1 ih1
      cases h
      . exists t2; apply Step.st_if_tru
      . exists t3; apply Step.st_if_fls
    . cases ih1 with
      | intro t1' hs =>
          exists (ite t1' t2 t3); apply Step.st_if hs
  -- zero
  . have t_z := NV.nv_zero
    apply Or.inl; unfold Value; apply Or.inr; assumption
  . rename_i t' ht' ih; cases ih <;> rename_i ih
    . have hnv := nat_canonical ht' ih
      have hsnv := NV.nv_succ hnv
      apply Or.inl; unfold Value; apply Or.inr; assumption
    . cases ih with
      | intro t'' hs' =>
          apply Or.inr; exists t''.succ; apply Step.st_succ hs'
  . rename_i t' ht' ih; cases ih <;> rename_i ih <;> apply Or.inr
    . have hnv := nat_canonical ht' ih
      cases hnv
      . exists zero; apply Step.st_pred_0
      . rename_i t' _; exists t'; apply Step.st_pred_succ
    . cases ih with
      | intro u hs =>
          exists u.pred; apply Step.st_pred hs
  . rename_i t' ht' ih; cases ih <;> rename_i ih <;> apply Or.inr
    . have hnv := nat_canonical ht' ih
      cases hnv
      . exists tru; apply Step.st_iszero_0
      . exists fls; apply Step.st_iszero_succ
    . cases ih with
      | intro u hs =>
          exists u.iszero; apply Step.st_iszero hs
