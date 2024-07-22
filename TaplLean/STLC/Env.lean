abbrev Env (α : Type) := String → Option α

def empty {α : Type} : (Env α) := fun _ => none

def update {α : Type}
  (x : String) (v : α) (env : Env α) : Env α
  :=
  fun y => if x = y then some v else env y

notation:100 x " |→ " v " ; " τ => update x v τ
notation:100 x " |→ " v => update x v empty

def sorted {α : Type} (Γ : Env α) (Γ' : Env α) : Prop :=
  ∀ x, Γ x = Γ' x

theorem sorted_update : ∀ {α : Type} {Γ Γ' : Env α} (x) (v : α),
  sorted Γ Γ' →
  sorted (x |→ v ; Γ) (x |→ v ; Γ')
  := by
  unfold sorted
  intro α Γ Γ' x v Hs y
  unfold update
  split
  . rfl
  . apply Hs

theorem sorted_swap : ∀ {α : Type} (Γ : Env α) (x y vx vy),
  x ≠ y →
  sorted (x |→ vx ; y |→ vy ; Γ) (y |→ vy ; x |→ vx ; Γ)
  := by
  unfold sorted; intro α Γ x y vx vy Hneq z; unfold update
  cases String.decEq x z <;> rename_i Hxz
  . cases String.decEq y z <;> rename_i Hyz
    . simp [Hxz]
    . simp [Hxz]
  . cases String.decEq y z <;> rename_i Hyz
    . simp [Hxz]; simp [Hyz]
    . exfalso; rw [← Hyz] at Hxz; apply Hneq Hxz

theorem sorted_extend_eq : ∀ {α : Type} (Γ : Env α) (x v w),
  sorted (x |→ v ; Γ) (x |→ v ; x |→ w ; Γ)
  := by
  intro α Γ x v w y; unfold update
  cases String.decEq x y <;> rename_i H <;> simp [H]
