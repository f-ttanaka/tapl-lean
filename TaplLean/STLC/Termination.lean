import Mathlib.Logic.Relation
import TaplLean.STLC.Env

inductive Type_ where
  | TBase : Type_
  | TArrow : Type_ → Type_ → Type_
open Type_

abbrev TyEnv := Env Type_

inductive Term_ where
  | var : String → Term_
  | abs : String → Type_ → Term_ → Term_
  | app : Term_ → Term_ → Term_
open Term_

infixr:50 " :-> " => Type_.TArrow
notation:90 "λ" x " : " T " , " t => Term_.abs x T t

def subst (x : String) (s : Term_) (t : Term_) :=
  match t with
  | var y       => if x = y then s else t
  | λ y : T, t' => if x = y then t else λ y : T, subst x s t'
  | app t1 t2   => app (subst x s t1) (subst x s t2)

inductive WellTyped : TyEnv → Term_ → Type_ → Prop where
  | wt_var : ∀ {Γ x T}, Γ x = some T → WellTyped Γ (var x) T
  | wt_abs : ∀ {Γ x t1 T1 T2},
      WellTyped (x |→ T2; Γ) t1 T1 →
      WellTyped Γ (λ x : T2 , t1) (T2 :-> T1)
  | wt_app : ∀ {Γ t1 t2 T1 T2},
      WellTyped Γ t1 (T2 :-> T1) →
      WellTyped Γ t2 T2 →
      WellTyped Γ (app t1 t2) T1
open WellTyped

notation:20 "[" x " := " s " ] " t => subst x s t
notation:100 Γ " ⊢ " t " ∈: " T => WellTyped Γ t T

theorem weakening : ∀ {Γ Γ' t T},
  includeIn Γ Γ' →
  (Γ ⊢ t ∈: T) → Γ' ⊢ t ∈: T
  := by
  intro Γ Γ' t T Hin HT
  revert Γ'
  induction HT
  case wt_var Δ x U HD =>
    intro Δ' Hin
    simp [includeIn] at Hin
    have Hin' := Hin x U HD
    apply wt_var Hin'
  case wt_abs Δ x t1 T1 T2 HT IH =>
    intro Δ' Hin
    have Hin_ext := update_includeIn x T2 Hin
    have HT_G' := IH Hin_ext
    apply wt_abs HT_G'
  case wt_app Δ t1 t2 T1 T2 HT_fun HT_arg IH_fun IH_arg =>
    intro Δ' Hin
    apply wt_app (IH_fun Hin) (IH_arg Hin)
  done

theorem weakening_empty : ∀ {t T} (Γ),
  (empty ⊢ t ∈: T) → Γ ⊢ t ∈: T
  := by
  intro t T Γ H
  have Hin := empty_min Γ
  apply weakening Hin H
  done

inductive Value : Term_ → Prop where
  | v_abs : ∀ {x T t}, Value (λx:T, t)

inductive Step : Term_ → Term_ → Prop where
  | st_app_abs : ∀ {x T2 t1 v2},
      Value v2 →
      Step (app (λx:T2,t1) v2) ([x := v2] t1)
  | st_app1 : ∀ {t1 t1' t2},
      Step t1 t1' →
      Step (app t1 t2) (app t1' t2)
  | st_app2 : ∀ {v1 t2 t2'},
      Value v1 →
      Step t2 t2' →
      Step (app v1 t2) (app v1 t2')
notation:40 t " -> " t' => Step t t'
open Step

def stepStar := Relation.ReflTransGen Step
notation:40 t " -*> " t' => stepStar t t'

def terminate (t : Term_) := ∃ t', (t -*> t') ∧ Value t'

-- inductive R : Type_ → Term_ → Prop where
--   | R_base : ∀ {T t},
--       (empty ⊢ t ∈: T) →
--       terminate t →
--       R T t
--   | R_arrow : ∀ {T1 T2 t},
--       (empty ⊢ t ∈: T1 :-> T2) →
--       terminate t →
--       (∀ s, R T1 s → R T2 (app t s)) →
--       R (T1 :-> T2) t

def R (T : Type_) (t : Term_) : Prop :=
  match T with
  | TBase => (empty ⊢ t ∈: T) ∧ terminate t
  | TArrow T1 T2 =>
      (empty ⊢ t ∈: T1 :-> T2) ∧
      terminate t ∧
      (∀ s, R T1 s → R T2 (app t s))

theorem R_term_is_terminate : ∀ {T t}, R T t → terminate t
  := by
  intro T t H_R
  cases T
  case TBase =>
    simp [R] at H_R
    apply H_R.right
  case TArrow T1 T2 =>
    simp [R] at H_R
    apply H_R.right.left
  done

-- 書換えにより危険対は生じない
theorem step_deterministic : ∀ {t t' t'' : Term_},
  (t -> t') → (t -> t'') → t' = t''
  := by
  intro t t' t'' H1 H2
  revert t''
  induction H1
  case st_app_abs x T2 t1 v2 H_v2 =>
    intro t'' H_st
    cases H_st
    case st_app_abs =>
      trivial
    case st_app1 _ Contra =>
      cases Contra
    case st_app2 _ _ Contra =>
      cases H_v2
      cases Contra
  case st_app1 t1 t1' t2 H_st1 IH =>
    intro t'' H_st_app
    cases H_st_app
    case st_app_abs =>
      cases H_st1
    case st_app1 t1'' H_t1 =>
      have H_eq' := IH H_t1
      rw [H_eq']
    case st_app2 t2' H_v1 H_st2 =>
      cases H_v1
      cases H_st1
  case st_app2 v1 t2 t2' H_v1 H_st2 IH =>
    intro u H
    cases H_v1
    cases H
    case st_app_abs _ _ _ H_v2 =>
      cases H_v2
      cases H_st2
    case st_app1 _ _ _ Contra =>
      cases Contra
    case st_app2 x T t t2'' HV_t H_st2' =>
      have H_eq2 := IH H_st2'
      rw [H_eq2]
  done

theorem step_preserve_termination : ∀ {t t' : Term_},
  (t -> t') → (terminate t ↔ terminate t')
  := by
  intro t t' H_st
  simp [terminate]
  apply Iff.intro
  . -- * → *
    intro H_t
    cases H_t; rename_i u H_u
    induction H_u.left using Relation.ReflTransGen.head_induction_on
    case refl =>
      cases H_u.right
      cases H_st
    case head a b Hst_ab Hmst IH =>
      have Heq := step_deterministic Hst_ab H_st
      rw [Heq] at Hmst
      exists u
      apply And.intro Hmst H_u.right
  . -- * ← *
    intro H_t'
    cases H_t'; rename_i u' H
    induction H.left using Relation.ReflTransGen.head_induction_on
    case refl =>
      exists u'
      apply And.intro (Relation.ReflTransGen.single H_st) H.right
    case head a _ _ _ _ =>
      have Hmst := Relation.ReflTransGen.head H_st H.left
      exists u'
      apply And.intro Hmst H.right
  done

theorem substitution_preserve_type : ∀ {Γ x S t T s},
  ((x |→ S; Γ) ⊢ t ∈: T) →
  (empty ⊢ s ∈: S) →
  Γ ⊢ ([x := s] t) ∈: T
  := by
  intro Γ x S t T s
  revert Γ T
  induction t <;> intro Γ T HT_t HT_s
  case var =>
    rename_i y
    simp [subst]
    cases String.decEq x y
    case isFalse Hneq =>
      unfold update at HT_t; cases HT_t; rename_i HT_t
      simp [Hneq] at HT_t
      simp [Hneq]
      apply wt_var HT_t
    case isTrue Heq =>
      unfold update at HT_t; cases HT_t; rename_i HT_t
      simp [Heq] at HT_t
      simp [Heq]
      have HT_s := weakening_empty Γ HT_s
      rw [← HT_t]
      assumption

theorem step_preserve_type : ∀ {t t' : Term_} {T : Type_},
  (t -> t') → (empty ⊢ t ∈: T) → (empty ⊢ t' ∈: T)
  := by
  intro t t' T Hst HT_t
  induction Hst
  case st_app_abs x T2 t1 v2 H_v2 =>
    apply wt_app

theorem step_preserve_R : ∀ {T t t'},
  (empty ⊢ t ∈: T) →
  (t -> t') →
  (R T t ↔ R T t')
  := by
  intro T t t' H_st HR
  induction T <;> apply Iff.intro
  case TBase =>
    simp [R]
