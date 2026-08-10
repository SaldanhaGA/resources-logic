import ResourcesLogic.Hoare.Rules

namespace ResourcesLogic

open Finset

variable {C : CostModel}

def abudget (N a cb : Nat) (k φv : Nat) : Nat :=
  (N - k) * a + φv + (N + 1 - min k N) * cb

theorem abudget_ge (N a cb k φv : Nat) : cb ≤ abudget N a cb k φv := by
  have h : 1 ≤ N + 1 - min k N := by
    have : min k N ≤ N := min_le_right _ _
    omega
  have : 1 * cb ≤ (N + 1 - min k N) * cb := Nat.mul_le_mul_right _ h
  simp only [abudget]
  omega

theorem abudget_step {N a cb k k' c φv φv' : Nat}
    (hk : k < N) (hk' : k < k') (hpot : c + φv' ≤ a + φv) :
    cb + c + abudget N a cb k' φv' ≤ abudget N a cb k φv := by
  have hmin : min k N = k := min_eq_left (le_of_lt hk)
  have ha : (N - k') * a + a ≤ (N - k) * a := by
    have h : (N - k') + 1 ≤ N - k := by omega
    calc (N - k') * a + a = ((N - k') + 1) * a := by ring
      _ ≤ (N - k) * a := Nat.mul_le_mul_right _ h
  have hc : cb + (N + 1 - min k' N) * cb ≤ (N + 1 - min k N) * cb := by
    rw [hmin]
    have h : (N + 1 - min k' N) + 1 ≤ N + 1 - k := by
      have h1 : min k' N ≤ N := min_le_right _ _
      have h2 : k + 1 ≤ min k' N + 1 := by
        rcases le_total k' N with h' | h'
        · rw [min_eq_left h']; omega
        · rw [min_eq_right h']; omega
      omega
    calc cb + (N + 1 - min k' N) * cb = ((N + 1 - min k' N) + 1) * cb := by ring
      _ ≤ (N + 1 - k) * cb := Nat.mul_le_mul_right _ h
  simp only [abudget]
  omega

theorem abudget_le (N a cb k : Nat) : abudget N a cb k 0 ≤ N * a + (N + 1) * cb := by
  have h₁ : (N - k) * a ≤ N * a := Nat.mul_le_mul_right _ (by omega)
  have h₂ : (N + 1 - min k N) * cb ≤ (N + 1) * cb := Nat.mul_le_mul_right _ (by omega)
  simp only [abudget]
  omega

theorem valid_while_amortized {I : Assn} {b : BExp} {S : Stmt} {f : State → Nat}
    {φ Tb : Cost} {N a cb : Nat}
    (hcb : ∀ σ, I σ → tbcost C b σ = cb)
    (hN : ∀ σ, I σ → bval b σ = true → f σ < N)
    (hbody : ∀ k n c : Nat,
      Valid C (fun σ => I σ ∧ bval b σ = true ∧ f σ = k ∧ φ σ = n ∧ Tb σ = c) S
        (fun σ' => I σ' ∧ k < f σ' ∧ c + φ σ' ≤ a + n) Tb) :
    Valid C (fun σ => I σ ∧ φ σ = 0) (.while b S) (fun σ => I σ ∧ bval b σ = false)
      (fun _ => N * a + (N + 1) * cb) := by
  have key : ∀ m σ, N - f σ ≤ m → I σ →
      ∃ σ' t', Eval C (.while b S) σ t' σ' ∧ (I σ' ∧ bval b σ' = false) ∧
        t' ≤ abudget N a cb (f σ) (φ σ) := by
    intro m
    induction m with
    | zero =>
        intro σ hm hI
        cases hb : bval b σ with
        | false =>
            exists σ, tbcost C b σ
            refine ⟨Eval.whileF hb, ⟨hI, hb⟩, ?_⟩
            rw [hcb σ hI]
            apply abudget_ge
        | true => have := hN σ hI hb; omega
    | succ m ih =>
        intro σ hm hI
        cases hb : bval b σ with
        | false =>
            exists σ, tbcost C b σ
            refine ⟨Eval.whileF hb, ⟨hI, hb⟩, ?_⟩
            rw [hcb σ hI]
            apply abudget_ge
        | true =>
            have hlt : f σ < N := hN σ hI hb
            obtain ⟨σ₁, t₁, hev₁, ⟨hI₁, hf₁, hpot⟩, hle₁⟩ :=
              hbody (f σ) (φ σ) (Tb σ) σ ⟨hI, hb, rfl, rfl, rfl⟩
            obtain ⟨σ', t', hev', hpost, hle'⟩ := ih σ₁ (by omega) hI₁
            exists σ', tbcost C b σ + t₁ + t'
            refine ⟨Eval.whileT hb hev₁ hev', hpost, ?_⟩
            have hstep := abudget_step (N := N) (a := a) (cb := cb) hlt hf₁ hpot
            rw [hcb σ hI]
            omega
  intro σ ⟨hI, hφ⟩
  obtain ⟨σ', t', hev, hpost, hle⟩ := key (N - f σ) σ le_rfl hI
  exists σ', t'
  refine ⟨hev, hpost, ?_⟩
  rw [hφ] at hle
  refine le_trans hle ?_
  apply abudget_le

theorem Hoare.while_amortized {I : Assn} {b : BExp} {S : Stmt} {f : State → Nat}
    {φ Tb : Cost} {N a cb : Nat}
    (hcb : ∀ σ, I σ → tbcost C b σ = cb)
    (hN : ∀ σ, I σ → bval b σ = true → f σ < N)
    (hbody : ∀ k n c : Nat,
      Hoare C (fun σ => I σ ∧ bval b σ = true ∧ f σ = k ∧ φ σ = n ∧ Tb σ = c) S
        (fun σ' => I σ' ∧ k < f σ' ∧ c + φ σ' ≤ a + n) Tb) :
    Hoare C (fun σ => I σ ∧ φ σ = 0) (.while b S) (fun σ => I σ ∧ bval b σ = false)
      (fun _ => N * a + (N + 1) * cb) :=
  Hoare.complete (valid_while_amortized hcb hN (fun k n c => (hbody k n c).sound))

end ResourcesLogic
