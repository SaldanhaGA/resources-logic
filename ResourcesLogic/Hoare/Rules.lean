import ResourcesLogic.Hoare.Completeness

namespace ResourcesLogic

open Finset

variable {C : CostModel}

def budget (t : Nat → Nat) (N cb k : Nat) : Nat :=
  (∑ i ∈ Finset.Ico k N, t i) + (N + 1 - min k N) * cb

theorem budget_ge (t : Nat → Nat) (N cb k : Nat) : cb ≤ budget t N cb k := by
  have h : 1 ≤ N + 1 - min k N := by
    have : min k N ≤ N := min_le_right _ _
    omega
  calc cb = 1 * cb := (one_mul cb).symm
    _ ≤ (N + 1 - min k N) * cb := Nat.mul_le_mul_right _ h
    _ ≤ budget t N cb k := Nat.le_add_left _ _

theorem budget_step {t : Nat → Nat} {N cb k k' : Nat} (hk : k < N) (hk' : k < k') :
    cb + t k + budget t N cb k' ≤ budget t N cb k := by
  have hsplit : (∑ i ∈ Finset.Ico k N, t i) = t k + ∑ i ∈ Finset.Ico (k + 1) N, t i :=
    Finset.sum_eq_sum_Ico_succ_bot hk _
  have hmono : (∑ i ∈ Finset.Ico k' N, t i) ≤ ∑ i ∈ Finset.Ico (k + 1) N, t i :=
    Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (by omega) le_rfl)
  have hmin : min k N = k := min_eq_left (le_of_lt hk)
  have hmin' : k + 1 ≤ min k' N + 1 := by
    rcases le_total k' N with h | h
    · rw [min_eq_left h]; omega
    · rw [min_eq_right h]; omega
  have hcb : cb + (N + 1 - min k' N) * cb ≤ (N + 1 - min k N) * cb := by
    rw [hmin]
    have h1 : (N + 1 - min k' N) + 1 ≤ N + 1 - k := by
      have : min k' N ≤ N := min_le_right _ _
      omega
    calc cb + (N + 1 - min k' N) * cb
        = ((N + 1 - min k' N) + 1) * cb := by ring
      _ ≤ (N + 1 - k) * cb := Nat.mul_le_mul_right _ h1
  simp only [budget, hsplit]
  omega

theorem budget_le_total (t : Nat → Nat) (N cb k : Nat) :
    budget t N cb k ≤ (∑ i ∈ Finset.range N, t i) + (N + 1) * cb := by
  have h₁ : (∑ i ∈ Finset.Ico k N, t i) ≤ ∑ i ∈ Finset.range N, t i := by
    rw [← Nat.Ico_zero_eq_range]
    apply Finset.sum_le_sum_of_subset
    apply Finset.Ico_subset_Ico <;> omega
  have h₂ : (N + 1 - min k N) * cb ≤ (N + 1) * cb :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [budget]
  omega

theorem valid_while_thesis {I : Assn} {b : BExp} {S : Stmt} {f : State → Nat}
    {N cb : Nat} {t : Nat → Nat}
    (hcb : ∀ σ, I σ → tbcost C b σ = cb)
    (hN : ∀ σ, I σ → bval b σ = true → f σ < N)
    (hbody : ∀ k, Valid C (fun σ => I σ ∧ bval b σ = true ∧ f σ = k) S
                    (fun σ' => I σ' ∧ k < f σ') (fun _ => t k)) :
    Valid C I (.while b S) (fun σ => I σ ∧ bval b σ = false)
      (fun _ => (∑ i ∈ Finset.range N, t i) + (N + 1) * cb) := by

  have key : ∀ m σ, N - f σ ≤ m → I σ →
      ∃ σ' t', Eval C (.while b S) σ t' σ' ∧ (I σ' ∧ bval b σ' = false) ∧
        t' ≤ budget t N cb (f σ) := by
    intro m
    induction m with
    | zero =>
        intro σ hm hI

        cases hb : bval b σ with
        | false =>
            exists σ, tbcost C b σ
            refine ⟨Eval.whileF hb, ⟨hI, hb⟩, ?_⟩
            rw [hcb σ hI]
            apply budget_ge
        | true =>
            have := hN σ hI hb
            omega
    | succ m ih =>
        intro σ hm hI
        cases hb : bval b σ with
        | false =>
            exists σ, tbcost C b σ
            refine ⟨Eval.whileF hb, ⟨hI, hb⟩, ?_⟩
            rw [hcb σ hI]
            apply budget_ge
        | true =>
            have hlt : f σ < N := hN σ hI hb
            obtain ⟨σ₁, t₁, hev₁, ⟨hI₁, hf₁⟩, hle₁⟩ :=
              hbody (f σ) σ ⟨hI, hb, rfl⟩
            obtain ⟨σ', t', hev', hpost, hle'⟩ := ih σ₁ (by omega) hI₁
            exists σ', tbcost C b σ + t₁ + t'
            refine ⟨Eval.whileT hb hev₁ hev', hpost, ?_⟩
            have hstep := budget_step (t := t) (N := N) (cb := cb) hlt hf₁
            have hle₁' : t₁ ≤ t (f σ) := hle₁
            rw [hcb σ hI]
            omega
  intro σ hI
  obtain ⟨σ', t', hev, hpost, hle⟩ := key (N - f σ) σ le_rfl hI
  exists σ', t'
  refine ⟨hev, hpost, ?_⟩
  refine le_trans hle ?_
  apply budget_le_total

theorem Hoare.while_thesis {I : Assn} {b : BExp} {S : Stmt} {f : State → Nat}
    {N cb : Nat} {t : Nat → Nat}
    (hcb : ∀ σ, I σ → tbcost C b σ = cb)
    (hN : ∀ σ, I σ → bval b σ = true → f σ < N)
    (hbody : ∀ k, Hoare C (fun σ => I σ ∧ bval b σ = true ∧ f σ = k) S
                    (fun σ' => I σ' ∧ k < f σ') (fun _ => t k)) :
    Hoare C I (.while b S) (fun σ => I σ ∧ bval b σ = false)
      (fun _ => (∑ i ∈ Finset.range N, t i) + (N + 1) * cb) :=
  Hoare.complete (valid_while_thesis hcb hN (fun k => (hbody k).sound))

theorem Hoare.seq_const {P Q R : Assn} {S₁ S₂ : Stmt} {t₁ t₂ : Nat}
    (h₁ : Hoare C P S₁ Q (fun _ => t₁)) (h₂ : Hoare C Q S₂ R (fun _ => t₂)) :
    Hoare C P (.seq S₁ S₂) R (fun _ => t₁ + t₂) :=
  Hoare.seq t₂ (Hoare.weaken h₁ (fun _ hq => ⟨hq, le_refl _⟩)) h₂

theorem Hoare.weak {P P' Q Q' : Assn} {S : Stmt} {T T' : Cost}
    (h : Hoare C P' S Q' T') (hP : ∀ σ, P σ → P' σ) (hQ : ∀ σ, Q' σ → Q σ)
    (hT : ∀ σ, T' σ ≤ T σ) : Hoare C P S Q T :=
  Hoare.conseq h hP hQ (fun σ _ => hT σ)

end ResourcesLogic
