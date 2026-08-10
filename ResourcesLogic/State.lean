import Mathlib.Tactic

namespace ResourcesLogic

abbrev Ident := String

inductive Loc where
  | var : Ident → Loc
  | arr : Ident → Int → Loc
  deriving DecidableEq, Repr

abbrev State := Loc → Int

namespace State

def update (σ : State) (l : Loc) (v : Int) : State :=
  fun l' => if l' = l then v else σ l'

@[simp] theorem update_same (σ : State) (l : Loc) (v : Int) :
    update σ l v l = v := by
  simp [update]

@[simp] theorem update_other (σ : State) {l l' : Loc} (v : Int) (h : l' ≠ l) :
    update σ l v l' = σ l' := by
  simp [update, h]

theorem update_shadow (σ : State) (l : Loc) (v w : Int) :
    update (update σ l v) l w = update σ l w := by
  funext l'; by_cases h : l' = l <;> simp [update, h]

theorem update_swap (σ : State) {l₁ l₂ : Loc} (v₁ v₂ : Int) (h : l₁ ≠ l₂) :
    update (update σ l₁ v₁) l₂ v₂ = update (update σ l₂ v₂) l₁ v₁ := by
  funext l'
  by_cases h₁ : l' = l₁ <;> by_cases h₂ : l' = l₂ <;>
    simp_all [update]

theorem update_same_value (σ : State) (l : Loc) : update σ l (σ l) = σ := by
  funext l'; by_cases h : l' = l <;> simp [update, h]

end State

notation:max σ "[" l " ↦ " v "]" => State.update σ l v

end ResourcesLogic
