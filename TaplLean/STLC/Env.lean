abbrev Env (α : Type) := String → Option α

def empty {α : Type} : (Env α) := fun _ => none

def update {α : Type}
  (x : String) (v : α) (env : Env α) : Env α
  :=
  fun y => if x = y then some v else env y

notation:100 x " |→ " v " ; " τ => update x v τ
notation:100 x " |→ " v => update x v empty
