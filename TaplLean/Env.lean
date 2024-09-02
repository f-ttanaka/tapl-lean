import Mathlib.Logic.Basic

abbrev Env (α : Type) := String → Option α

def empty {α : Type} : (Env α) := fun _ => none

def update {α : Type}
  (x : String) (v : α) (env : Env α) : Env α
  :=
  fun y => if x = y then some v else env y

notation:100 x " |→ " v " ; " τ => update x v τ
notation:100 x " |→ " v => update x v empty

theorem update_neq : ∀ {α : Type} {Γ : Env α} {x y v} (w),
  Γ x = some v →
  y ≠ x →
  (y |→ w; Γ) x = some v
  := by
  intro α Γ x y v w H Hneq
  unfold update
  simp [Hneq]
  assumption
  done

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

theorem eq_swap : ∀ {α : Type} (Γ : Env α) (x y vx vy),
  x ≠ y →
  (x |→ vx ; y |→ vy ; Γ) = (y |→ vy ; x |→ vx ; Γ)
  := by
  intro α Γ x y vx vy Hneq
  funext z
  unfold update
  cases String.decEq x z
  case isFalse Hneq_xz =>
    simp [Hneq_xz]
  case isTrue Heq_xz =>
    have Hneq_yz := ne_of_ne_of_eq (Ne.symm Hneq) Heq_xz
    simp [Heq_xz, Hneq_yz]
  done

theorem sorted_extend_eq : ∀ {α : Type} (Γ : Env α) (x v w),
  sorted (x |→ v ; Γ) (x |→ v ; x |→ w ; Γ)
  := by
  intro α Γ x v w y; unfold update
  cases String.decEq x y <;> rename_i H <;> simp [H]

theorem eq_extend_eq : ∀ {α : Type} (Γ : Env α) (x v w),
  (x |→ v ; Γ) = (x |→ v ; x |→ w ; Γ)
  := by
  intro α Γ x v w
  funext y
  unfold update
  cases String.decEq x y
  case isFalse Hneq =>
    simp [Hneq]
  case isTrue Heq =>
    simp [Heq]
  done

def includeIn {α : Type} (Γ : Env α) (Γ' : Env α) : Prop :=
  ∀ x v, (Γ x = some v → Γ' x = some v)

theorem empty_min : ∀ {α : Type} (Γ : Env α),
  includeIn empty Γ
  := by
  simp [includeIn]
  intro α Γ x v H
  cases H
  done

theorem update_includeIn : ∀ {α : Type} {Γ Γ' : Env α} (x v),
  includeIn Γ Γ' →
  includeIn (x |→ v; Γ) (x |→ v; Γ')
  := by
  intro α Γ Γ' x v H
  unfold includeIn
  unfold includeIn at H
  intro y w Hy
  unfold update at Hy
  cases String.decEq x y
  case isFalse Hneq =>
    simp [Hneq] at Hy
    have Hy' := H y w Hy
    apply update_neq v Hy' Hneq
  case isTrue Heq =>
    simp [Heq] at Hy
    unfold update; simp [Heq]; assumption
  done
