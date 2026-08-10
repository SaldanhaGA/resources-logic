import ResourcesLogic.Semantics
import ResourcesLogic.Asymptotic

namespace ResourcesLogic

abbrev Assn := State → Prop

abbrev Cost := State → Nat

def Valid (C : CostModel) (P : Assn) (S : Stmt) (Q : Assn) (T : Cost) : Prop :=
  ∀ σ, P σ → ∃ σ' t, Eval C S σ t σ' ∧ Q σ' ∧ t ≤ T σ

def ValidPartial (C : CostModel) (P : Assn) (S : Stmt) (Q : Assn) (T : Cost) : Prop :=
  ∀ σ σ' t, P σ → Eval C S σ t σ' → Q σ' ∧ t ≤ T σ

theorem Valid.toPartial {C P S Q T} (h : Valid C P S Q T) : ValidPartial C P S Q T := by
  intro σ σ' t hP hev
  obtain ⟨σ'', t', hev', hQ, hle⟩ := h σ hP
  obtain ⟨rfl, rfl⟩ := Eval.deterministic hev' hev
  constructor <;> assumption

def ValidExact (C : CostModel) (P : Assn) (S : Stmt) (Q : Assn) (T : Cost) : Prop :=
  ∀ σ, P σ → ∃ σ', Eval C S σ (T σ) σ' ∧ Q σ'

theorem ValidExact.toValid {C P S Q T} (h : ValidExact C P S Q T) : Valid C P S Q T := by
  intro σ hP
  obtain ⟨σ', hev, hQ⟩ := h σ hP
  exists σ', T σ

theorem Valid.cost_congr {C P S Q T T'} (h : ∀ σ, P σ → T σ = T' σ)
    (hv : Valid C P S Q T) : Valid C P S Q T' := by
  intro σ hP
  obtain ⟨σ', t, hev, hQ, hle⟩ := hv σ hP
  have hc := h σ hP
  exists σ', t
  refine ⟨hev, hQ, ?_⟩
  omega

theorem ValidExact.cost_congr {C P S Q T T'} (h : ∀ σ, P σ → T σ = T' σ)
    (hv : ValidExact C P S Q T) : ValidExact C P S Q T' := by
  intro σ hP
  obtain ⟨σ', hev, hQ⟩ := hv σ hP
  rw [h σ hP] at hev
  exists σ'

def BigOValid (C : CostModel) (P : ℕ → Assn) (S : Stmt) (Q : ℕ → Assn)
    (g : ℕ → ℕ) : Prop :=
  ∃ T : ℕ → ℕ, T ∈ O(g) ∧ ∀ n, Valid C (P n) S (Q n) (fun _ => T n)

def ThetaExactValid (C : CostModel) (P : ℕ → Assn) (S : Stmt) (Q : ℕ → Assn)
    (g : ℕ → ℕ) : Prop :=
  ∃ T : ℕ → ℕ, T ∈ Θ(g) ∧ ∀ n, ValidExact C (P n) S (Q n) (fun _ => T n)

theorem ThetaExactValid.toBigO {C P S Q g} (h : ThetaExactValid C P S Q g) :
    BigOValid C P S Q g := by
  obtain ⟨T, hT, hv⟩ := h
  rcases hT with ⟨hO, _⟩
  exists T
  refine ⟨hO, fun n => (hv n).toValid⟩

def substA (P : Assn) (x : Ident) (a : AExp) : Assn :=
  fun σ => P (σ[Loc.var x ↦ aval a σ])

def substArr (P : Assn) (x : Ident) (a₁ a₂ : AExp) : Assn :=
  fun σ => P (σ[Loc.arr x (aval a₁ σ) ↦ aval a₂ σ])

theorem subst_lemma (P : Assn) (x : Ident) (a : AExp) (σ : State) :
    substA P x a σ ↔ P (σ[Loc.var x ↦ aval a σ]) := Iff.rfl

end ResourcesLogic
