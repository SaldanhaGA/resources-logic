import ResourcesLogic.Assertions

/-!
# The `while` rule of Fig. 4.8 (Silva 2022, p. 23) is unsound

The rule, transcribed literally, is

    I ∧ b ⇒ f ≤ N      ∀k. {I ∧ b ∧ f = k} S {I ∧ f > k | t(k)}
    ─────────────────────────────────────────────────────────────────
    {I ∧ f ≥ 0} while b do S {I ∧ ¬b | ∑_{i=0}^{N-1} t(i) + (N+1) × 𝒯ℬ⟦b⟧}

(`f ≥ 0` is automatic since `f : State → ℕ`).  We exhibit an instance whose
premises are valid (even in the total-correctness reading) but whose
conclusion fails even in the partial-correctness reading of Definition 10:
with `N = 0` the side condition still admits one iteration, which the
conclusion does not pay for.
-/

namespace ResourcesLogic
namespace Counterexample

/-- `0 ≤ x ≤ 1` -/
def I : Assn := fun σ => 0 ≤ σ (.var "x") ∧ σ (.var "x") ≤ 1

def b : BExp := .lt (.var "x") (.num 1)

def S : Stmt := .assign "x" (.add (.var "x") (.num 1))

def f : State → Nat := fun σ => (σ (.var "x")).toNat

def N : Nat := 0

def t : Nat → Nat := fun _ => 4

theorem side_condition : ∀ σ, I σ → bval b σ = true → f σ ≤ N := by
  rintro σ ⟨h0, h1⟩ hb
  have hlt : σ (.var "x") < 1 := by simpa [b, bval, aval] using hb
  simp only [f, N]; omega

theorem body_valid : ∀ k, Valid unitModel (fun σ => I σ ∧ bval b σ = true ∧ f σ = k) S
    (fun σ => I σ ∧ k < f σ) (fun _ => t k) := by
  rintro k σ ⟨⟨h0, h1⟩, hb, hf⟩
  have hlt : σ (.var "x") < 1 := by simpa [b, bval, aval] using hb
  simp only [f] at hf
  exists σ[Loc.var "x" ↦ aval (.add (.var "x") (.num 1)) σ],
    tacost unitModel (.add (.var "x") (.num 1)) σ + unitModel.assignV
  constructor
  · apply Eval.assign
  constructor
  · constructor
    · simp only [I, aval, State.update_same]; omega
    · simp only [f, aval, State.update_same]; omega
  · simp [t, tacost, unitModel]

theorem conclusion_invalid :
    ¬ ValidPartial unitModel I (.while b S) (fun σ => I σ ∧ bval b σ = false)
      (fun σ => (∑ i ∈ Finset.range N, t i) + (N + 1) * tbcost unitModel b σ) := by
  intro h
  let σ₀ : State := fun _ => 0
  let σ₁ : State := σ₀[Loc.var "x" ↦ aval (.add (.var "x") (.num 1)) σ₀]
  have hb₀ : bval b σ₀ = true := by simp [σ₀, b, bval, aval]
  have hb₁ : bval b σ₁ = false := by simp [σ₁, σ₀, b, bval, aval]
  have hrun := Eval.whileT hb₀ (Eval.assign (C := unitModel)) (Eval.whileF (S := S) hb₁)
  have hI : I σ₀ := by simp [I, σ₀]
  have hcost := (h σ₀ σ₁ _ hI hrun).2
  simp [N, b, tbcost, tacost, unitModel] at hcost

/-- The literal Fig. 4.8 rule, read over our semantics, is unsound. -/
theorem while_thesis_literal_unsound :
    ¬ (∀ (I : Assn) (b : BExp) (S : Stmt) (f : State → Nat) (N : Nat) (t : Nat → Nat),
        (∀ σ, I σ → bval b σ = true → f σ ≤ N) →
        (∀ k, Valid unitModel (fun σ => I σ ∧ bval b σ = true ∧ f σ = k) S
                (fun σ => I σ ∧ k < f σ) (fun _ => t k)) →
        ValidPartial unitModel I (.while b S) (fun σ => I σ ∧ bval b σ = false)
          (fun σ => (∑ i ∈ Finset.range N, t i) + (N + 1) * tbcost unitModel b σ)) := by
  intro rule
  apply conclusion_invalid
  apply rule
  · apply side_condition
  · apply body_valid

end Counterexample
end ResourcesLogic
