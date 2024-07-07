inductive Ty : Type where
  | TBool
  | TArrow : Ty → Ty → Ty

infix:100 " T.-> " => Ty.TArrow

inductive Term : Type where
  | tru
  | fls
  | ite : Term → Term → Term → Term
  | var : String → Term
  | abs : String → Ty → Term
  | app : Term → Term → Term

inductive WellTyped : Term → Ty → Prop where
