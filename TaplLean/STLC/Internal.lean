import TaplLean.STLC.Env

inductive Ty : Type where
  | TBool
  | TArrow : Ty → Ty → Ty
  deriving DecidableEq

infixr:50 " :-> " => Ty.TArrow

abbrev TyEnv := Env Ty

inductive Term : Type where
  | tru
  | fls
  | ite : Term → Term → Term → Term
  | var : String → Term
  | abs : String → Ty → Term → Term
  | app : Term → Term → Term

notation:90 "λ" x " : " T " , " t => Term.abs x T t

inductive WellTyped : TyEnv → Term → Ty → Prop where
  | wt_tru : ∀ Γ, WellTyped Γ Term.tru Ty.TBool
  | wt_fls : ∀ Γ, WellTyped Γ Term.fls Ty.TBool
  | wt_ite : ∀ Γ t1 t2 t3 T,
      WellTyped Γ t1 Ty.TBool →
      WellTyped Γ t2 T →
      WellTyped Γ t3 T →
      WellTyped Γ (Term.ite t1 t2 t3) T
  | wt_var : ∀ Γ x T, Γ x = some T → WellTyped Γ (Term.var x) T
  | wt_abs : ∀ Γ x t1 T1 T2,
      WellTyped (x |→ T2; Γ) t1 T1 →
      WellTyped Γ (λ x : T2 , t1) (T2 :-> T1)
  | wt_app : ∀ Γ t1 t2 T1 T2,
      WellTyped Γ t1 (T2 :-> T1) →
      WellTyped Γ t2 T2 →
      WellTyped Γ (Term.app t1 t2) T1

notation:100 Γ " ⊢ " t " ∈: " T => WellTyped Γ t T

open WellTyped
example : empty ⊢ (Term.app (λ x : Ty.TBool, Term.var x) Term.tru) ∈: Ty.TBool
  := by
  apply wt_app empty (λ x : Ty.TBool, Term.var x) Term.tru
  . apply wt_abs empty x (Term.var x) Ty.TBool Ty.TBool
    apply wt_var; simp [update]
  . apply wt_tru
