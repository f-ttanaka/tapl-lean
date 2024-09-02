import TaplLean.Env

inductive Ty : Type where
  | TyTop : Ty
  | TyBase : String → Ty
  | TyArr : Ty → Ty → Ty
  | TyRec : List (String × Ty) → Ty
open Ty
infixr:50 " :-> " => TyArr

abbrev TyEnv := Env Ty

inductive Term : Type where
  | TmVar : String → Term
  | TmVal : Term
  | TmAbs : String → Ty → Term → Term
  | TmApp : Term → Term → Term
  | TmRec : List (String × Term) → Term
  | TmProj : Term → String → Term
open Term
notation:90 "λ" x " : " T " , " t => Term.TmAbs x T t

inductive NF : Term → Prop where
  | nf_val : NF TmVal
  | nf_abs : ∀ {x T t}, NF (λx : T, t)
  | nf_rec : ∀ {ps}, NF (TmRec ps)
open NF

def subst (x : String) (s : Term) (t : Term) :=
  match t with
  | TmVar y       => if x = y then s else t
  | TmVal => TmVal
  | TmAbs y T t' => if x = y then t else λ y : T, subst x s t'
  | TmApp t1 t2   => TmApp (subst x s t1) (subst x s t2)
  | TmRec ls => TmRec (mapSubstRec ls)
  | TmProj tl l => TmProj (subst x s tl) l
  where
    mapSubstRec (ps : List (String × Term)) :=
      match ps with
      | [] => []
      | (l, tl) :: ps' => (l, subst x s tl) :: mapSubstRec ps'
notation:20 "[" x " := " s " ] " t => subst x s t

def tLookup (l : String) (t : Term) :=
  match t with
  | TmRec ps => List.lookup l ps
  | _ => Option.none

inductive Step : Term → Term → Prop where
  | st_app1 : ∀ {t1 t1' t2},
      Step t1 t1' → Step (TmApp t1 t2) (TmApp t1' t2)
  | st_app2 : ∀ {t1 t2 t2'},
      NF t1 → Step t2 t2' → Step (TmApp t1 t2) (TmApp t1 t2')
  | st_app_abs : ∀ {x T t u},
      NF u → Step (TmApp (λx : T, t) u) ([x := u] t)
  | st_proj_rec : ∀ {l t},
      tLookup l t = some v →
      Step (TmProj (TmRec ps) l) v
  | st_proj : ∀ {t t' l},
      Step t t' → Step (TmProj t l) (TmProj t' l)
  | st_rec_head : ∀ {l t t' ps},
      Step t t' →
      Step (TmRec ((l,t) :: ps)) (TmRec ((l,t') :: ps))
  | st_rec_tail : ∀ {l t t' ps},
      Step t t' →
      Step (TmRec (ps ++ [(l,t)])) (TmRec (ps ++ [(l,t')]))
infixr:50 " -> " => Step

inductive Subty : Ty → Ty → Prop where
| subty_top : ∀ {T}, Subty T TyTop
| subty_refl : ∀ {T}, Subty T T
| subty_trans : ∀ {S T U},
    Subty S T → Subty T U → Subty S U
| subty_arr : ∀ {S1 S2 T1 T2},
    Subty T1 S1 → Subty S2 T2 → Subty (S1 :-> S2) (T1 :-> T2)
| subty_rec_width : ∀ {l T Tr},
    Subty (TyRec ((l,T) :: Tr)) (TyRec [])
| subty_rec_depth : ∀ {l S T Sr Tr},
    Subty S T →
    Subty (TyRec Sr) (TyRec Tr) →
    Subty (TyRec ((l,S) :: Sr)) (TyRec ((l,T) :: Tr))
| subty_rec_perm : ∀ {l1 l2 T1 T2 Tr},
    l1 ≠ l2 →
    Subty (TyRec ((l1,T1) :: (l2,T2) :: Tr)) (TyRec ((l2,T2) :: (l1,T1) :: Tr))
infixr:50 " <: " => Subty

inductive WellTyped : TyEnv → Term → Ty → Prop where
| wt_var : ∀ {Γ x},
    Γ x = some T → WellTyped Γ (TmVar x) T
| wt_val : ∀ {Γ}, WellTyped Γ TmVal TBase
| wt_abs : ∀ {Γ x t T U},
    WellTyped (x |→ T; Γ) t U →
    WellTyped Γ (TmAbs x T t) (T :-> U)
| wt_app : ∀ {Γ t1 t2 T U},
    WellTyped Γ t1 (T :-> U) →
    WellTyped Γ t2 T →
    WellTyped Γ (TmApp t1 t2) U
| wt_rec : ∀ {Γ l t T tr Tr},
    WellTyped Γ t T →
    WellTyped Γ (TmRec tr) (TyRec Tr) →
    WellTyped Γ (TmRec ((l,t) :: tr)) (TyRec ((l,T) :: Tr))
notation:100 Γ " ⊢ " t " ∈: " T => WellTyped Γ t T
