inductive Term where
  | tru
  | fls
  | ite : Term → Term → Term → Term
  | zero
  | succ : Term → Term
  | pred : Term → Term
  | iszero : Term → Term

mutual
inductive Value : Term → Prop where
  | v_tru : Value tru
  | v_fls : Value fls
  | v_nv : ∀ t, NV t → Value t
inductive NV : Term → Prop where
  | nv_zero : NV zero
  | nv_succ : ∀ t, NV t → NV (Term.succ t)
end

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
