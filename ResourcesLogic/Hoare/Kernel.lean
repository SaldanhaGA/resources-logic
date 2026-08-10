import ResourcesLogic.Assertions

namespace ResourcesLogic

inductive Hoare (C : CostModel) : Assn → Stmt → Assn → Cost → Prop where
  | skip {P} : Hoare C P .skip P (fun _ => C.skip)
  | assign {Q x a} :
      Hoare C (substA Q x a) (.assign x a) Q (fun σ => tacost C a σ + C.assignV)
  | arrAssign {Q x a₁ a₂} :
      Hoare C (substArr Q x a₁ a₂) (.arrAssign x a₁ a₂) Q
        (fun σ => tacost C a₁ σ + tacost C a₂ σ + C.assignA)
  | seq {P Q R S₁ S₂ T₁ T₂} (n : Nat)
      (h₁ : Hoare C P S₁ (fun σ => Q σ ∧ T₂ σ ≤ n) T₁)
      (h₂ : Hoare C Q S₂ R T₂) :
      Hoare C P (.seq S₁ S₂) R (fun σ => T₁ σ + n)
  | ite {P Q b S₁ S₂ T₁ T₂}
      (h₁ : Hoare C (fun σ => P σ ∧ bval b σ = true) S₁ Q T₁)
      (h₂ : Hoare C (fun σ => P σ ∧ bval b σ = false) S₂ Q T₂) :
      Hoare C P (.ite b S₁ S₂) Q (fun σ => max (T₁ σ) (T₂ σ) + tbcost C b σ)
  | while {I : Assn} {b S} {T : Cost} (E : Cost) (f : State → Nat)
      (hbody : ∀ k n c : Nat,
        Hoare C
          (fun σ => I σ ∧ bval b σ = true ∧ f σ = k ∧ E σ = n ∧ tbcost C b σ + T σ = c)
          S
          (fun σ' => I σ' ∧ f σ' < k ∧ E σ' + c ≤ n) T)
      (hexit : ∀ σ, I σ → bval b σ = false → tbcost C b σ ≤ E σ) :
      Hoare C I (.while b S) (fun σ => I σ ∧ bval b σ = false) E
  | conseq {P P' Q Q' S T T'}
      (h : Hoare C P' S Q' T')
      (hP : ∀ σ, P σ → P' σ) (hQ : ∀ σ, Q' σ → Q σ) (hT : ∀ σ, P σ → T' σ ≤ T σ) :
      Hoare C P S Q T
  | exists_pre {ι : Type} {P : ι → Assn} {S Q T}
      (h : ∀ i, Hoare C (P i) S Q T) :
      Hoare C (fun σ => ∃ i, P i σ) S Q T

namespace Hoare

variable {C : CostModel}

theorem false_pre {S Q T} : Hoare C (fun _ => False) S Q T := by
  have h : Hoare C (fun σ => ∃ _ : Empty, (False : Prop)) S Q T :=
    Hoare.exists_pre (P := fun (_ : Empty) _ => False) (fun i => i.elim)
  apply Hoare.conseq <;> first | assumption | (intro σ h; aesop)

theorem strengthen {P P' S Q T} (h : Hoare C P' S Q T) (hP : ∀ σ, P σ → P' σ) :
    Hoare C P S Q T :=
  Hoare.conseq h hP (fun _ hq => hq) (fun _ _ => le_refl _)

theorem weaken {P S Q Q' T} (h : Hoare C P S Q' T) (hQ : ∀ σ, Q' σ → Q σ) :
    Hoare C P S Q T :=
  Hoare.conseq h (fun _ hp => hp) hQ (fun _ _ => le_refl _)

theorem weakenCost {P S Q T T'} (h : Hoare C P S Q T') (hT : ∀ σ, P σ → T' σ ≤ T σ) :
    Hoare C P S Q T :=
  Hoare.conseq h (fun _ hp => hp) (fun _ hq => hq) hT

theorem of_pointwise {P S Q T}
    (h : ∀ σ₀, P σ₀ → Hoare C (fun σ => σ = σ₀) S Q T) : Hoare C P S Q T := by
  have key : ∀ σ₀ : State, Hoare C (fun σ => σ = σ₀ ∧ P σ₀) S Q T := by
    intro σ₀
    by_cases hp : P σ₀
    · have hh := h σ₀ hp
      apply strengthen <;> first | assumption | (intro σ hσ; aesop)
    · apply strengthen <;> first | assumption | apply false_pre | (intro σ hσ; aesop)
  have hep := Hoare.exists_pre (ι := State) key
  apply Hoare.conseq <;>
    first | assumption | (intro σ hP; exists σ) | (intro σ h; aesop)

theorem sound {P S Q T} (h : Hoare C P S Q T) : Valid C P S Q T := by
  induction h with
  | skip => intro σ hP; exists σ, C.skip; refine ⟨Eval.skip, hP, le_refl _⟩
  | @assign Q x a =>
      intro σ hP
      exists σ[Loc.var x ↦ aval a σ], tacost C a σ + C.assignV
      refine ⟨Eval.assign, hP, le_refl _⟩
  | @arrAssign Q x a₁ a₂ =>
      intro σ hP
      exists σ[Loc.arr x (aval a₁ σ) ↦ aval a₂ σ],
        tacost C a₁ σ + tacost C a₂ σ + C.assignA
      refine ⟨Eval.arrAssign, hP, le_refl _⟩
  | @seq P Q R S₁ S₂ T₁ T₂ n _ _ ih₁ ih₂ =>
      intro σ hP
      obtain ⟨σ₁, t₁, hev₁, ⟨hQ, hbound⟩, hle₁⟩ := ih₁ σ hP
      obtain ⟨σ₂, t₂, hev₂, hR, hle₂⟩ := ih₂ σ₁ hQ
      refine ⟨σ₂, t₁ + t₂, Eval.seq hev₁ hev₂, hR, ?_⟩
      show t₁ + t₂ ≤ T₁ σ + n
      omega
  | @ite P Q b S₁ S₂ T₁ T₂ _ _ ih₁ ih₂ =>
      intro σ hP
      cases hb : bval b σ with
      | true =>
          obtain ⟨σ', t, hev, hQ, hle⟩ := ih₁ σ ⟨hP, hb⟩
          refine ⟨σ', tbcost C b σ + t, Eval.iteT hb hev, hQ, ?_⟩
          show tbcost C b σ + t ≤ max (T₁ σ) (T₂ σ) + tbcost C b σ
          have : t ≤ max (T₁ σ) (T₂ σ) := le_trans hle (le_max_left _ _)
          omega
      | false =>
          obtain ⟨σ', t, hev, hQ, hle⟩ := ih₂ σ ⟨hP, hb⟩
          refine ⟨σ', tbcost C b σ + t, Eval.iteF hb hev, hQ, ?_⟩
          show tbcost C b σ + t ≤ max (T₁ σ) (T₂ σ) + tbcost C b σ
          have : t ≤ max (T₁ σ) (T₂ σ) := le_trans hle (le_max_right _ _)
          omega
  | @«while» I b S T E f _ hexit ihbody =>

      intro σ hI
      generalize hk : f σ = k
      induction k using Nat.strong_induction_on generalizing σ with
      | _ k ih =>
        cases hb : bval b σ with
        | false =>
            exists σ, tbcost C b σ
            refine ⟨Eval.whileF hb, ⟨hI, hb⟩, hexit σ hI hb⟩
        | true =>
            obtain ⟨σ₁, t, hev, ⟨hI₁, hlt, hbudget⟩, hle⟩ :=
              ihbody k (E σ) (tbcost C b σ + T σ) σ ⟨hI, hb, hk, rfl, rfl⟩
            obtain ⟨σ', t', hev', hpost, hle'⟩ := ih (f σ₁) (hk ▸ hlt) σ₁ hI₁ rfl
            refine ⟨σ', tbcost C b σ + t + t', Eval.whileT hb hev hev', hpost, ?_⟩
            omega
  | conseq _ hP hQ hT ih =>
      intro σ hp
      obtain ⟨σ', t, hev, hq, hle⟩ := ih σ (hP σ hp)
      exists σ', t
      refine ⟨hev, ?_, ?_⟩
      · apply hQ; assumption
      · apply le_trans hle; apply hT; assumption
  | exists_pre _ ih =>
      intro σ hp
      obtain ⟨i, hi⟩ := hp
      apply ih <;> assumption

end Hoare

end ResourcesLogic
