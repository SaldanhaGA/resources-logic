import ResourcesLogic.Exact.Hoare
import ResourcesLogic.VCG.Classic

namespace ResourcesLogic

variable {C : CostModel}

inductive AComE where
  | skip : AComE
  | assign : Ident → AExp → AComE
  | arrAssign : Ident → AExp → AExp → AComE
  | seq : AComE → AComE → AComE
  | ite : BExp → AComE → AComE → AComE

  | «for» : Ident → AExp → AExp → Assn → Nat → Nat → AComE → AComE

namespace AComE

def strip : AComE → Stmt
  | .skip => .skip
  | .assign x a => .assign x a
  | .arrAssign x a₁ a₂ => .arrAssign x a₁ a₂
  | .seq c₁ c₂ => .seq c₁.strip c₂.strip
  | .ite b c₁ c₂ => .ite b c₁.strip c₂.strip
  | .«for» i a bE _ _ _ c => Stmt.for i a bE c.strip

end AComE

def wpcE (C : CostModel) : AComE → Assn → Assn × Cost
  | .skip, Q => (Q, fun _ => C.skip)
  | .assign x a, Q => (substA Q x a, fun σ => tacost C a σ + C.assignV)
  | .arrAssign x a₁ a₂, Q =>
      (substArr Q x a₁ a₂, fun σ => tacost C a₁ σ + tacost C a₂ σ + C.assignA)
  | .seq c₁ c₂, Q =>
      ((wpcE C c₁ (wpcE C c₂ Q).1).1,
       fun σ => (wpcE C c₁ (wpcE C c₂ Q).1).2 σ + (wpcE C c₂ Q).2 σ)

  | .ite b c₁ c₂, Q =>
      (fun σ => ((bval b σ = true → (wpcE C c₁ Q).1 σ) ∧
                 (bval b σ = false → (wpcE C c₂ Q).1 σ)) ∧
                (wpcE C c₁ Q).2 σ = (wpcE C c₂ Q).2 σ,
       fun σ => (wpcE C c₁ Q).2 σ + tbcost C b σ)
  | .«for» i a bE P ts cb _, _ =>
      (substA P i a,
       fun σ => (tacost C a σ + C.assignV) +
         (aval bE σ - aval a σ).toNat * (cb + ts + incCost C) + cb)

def VCE (C : CostModel) : AComE → Assn → Prop
  | .skip, _ => True
  | .assign _ _, _ => True
  | .arrAssign _ _ _, _ => True
  | .seq c₁ c₂, Q =>
      VCE C c₁ (wpcE C c₂ Q).1 ∧ VCE C c₂ Q ∧

      (∀ σ₀ : State, VCE C c₁ (fun σ' => (wpcE C c₂ Q).2 σ' = (wpcE C c₂ Q).2 σ₀)) ∧
      (∀ σ₀ : State, (wpcE C c₁ (wpcE C c₂ Q).1).1 σ₀ →
        (wpcE C c₁ (fun σ' => (wpcE C c₂ Q).2 σ' = (wpcE C c₂ Q).2 σ₀)).1 σ₀)
  | .ite _ c₁ c₂, Q => VCE C c₁ Q ∧ VCE C c₂ Q
  | .«for» i a bE P ts cb c, Q =>

      (∀ σ v, aval a (σ[Loc.var i ↦ v]) = aval a σ) ∧
      (∀ σ v, aval bE (σ[Loc.var i ↦ v]) = aval bE σ) ∧
      (∀ σ, tbcost C (.lt (.var i) bE) σ = cb) ∧
      (∀ σ, substA P i a σ → aval a σ ≤ aval bE σ) ∧

      (∀ k av bv : Int, ∀ σ, P σ → σ (Loc.var i) = k → aval a σ = av →
        aval bE σ = bv → av ≤ k → k < bv →
        (wpcE C c (fun σ' => substA P i (.add (.var i) (.num 1)) σ' ∧
                             σ' (Loc.var i) = k ∧ aval a σ' = av ∧ aval bE σ' = bv)).1 σ ∧
        (wpcE C c (fun σ' => substA P i (.add (.var i) (.num 1)) σ' ∧
                             σ' (Loc.var i) = k ∧ aval a σ' = av ∧
                             aval bE σ' = bv)).2 σ = ts) ∧

      (∀ σ, P σ → σ (Loc.var i) = aval bE σ → Q σ) ∧

      (∀ k av bv : Int, VCE C c (fun σ' => substA P i (.add (.var i) (.num 1)) σ' ∧
                             σ' (Loc.var i) = k ∧ aval a σ' = av ∧ aval bE σ' = bv))

def VCGE (C : CostModel) (P : Assn) (c : AComE) (Q : Assn) (T : Cost) : Prop :=
  (∀ σ, P σ → (wpcE C c Q).1 σ) ∧ VCE C c Q ∧ (∀ σ, P σ → (wpcE C c Q).2 σ = T σ)

theorem wpcE_cost_indep (c : AComE) (Q Q' : Assn) (σ : State) :
    (wpcE C c Q).2 σ = (wpcE C c Q').2 σ := by
  induction c generalizing Q Q' σ with
  | skip => rfl
  | assign => rfl
  | arrAssign => rfl
  | seq c₁ c₂ ih₁ ih₂ =>
      show (wpcE C c₁ (wpcE C c₂ Q).1).2 σ + (wpcE C c₂ Q).2 σ
          = (wpcE C c₁ (wpcE C c₂ Q').1).2 σ + (wpcE C c₂ Q').2 σ
      rw [ih₁ (wpcE C c₂ Q).1 (wpcE C c₂ Q').1 σ, ih₂ Q Q' σ]
  | ite b c₁ c₂ ih₁ _ =>
      show (wpcE C c₁ Q).2 σ + tbcost C b σ = (wpcE C c₁ Q').2 σ + tbcost C b σ
      rw [ih₁ Q Q' σ]
  | «for» => rfl

theorem wpcE_sound (c : AComE) :
    ∀ Q : Assn, VCE C c Q → HoareE C (wpcE C c Q).1 (c.strip) Q (wpcE C c Q).2 := by
  induction c with
  | skip => intro Q _; apply HoareE.skip
  | assign x a => intro Q _; apply HoareE.assign
  | arrAssign x a₁ a₂ => intro Q _; apply HoareE.arrAssign
  | seq c₁ c₂ ih₁ ih₂ =>
      intro Q hvc
      obtain ⟨hvc₁, hvc₂, hvcpres, hpres⟩ := hvc
      have h₂ := ih₂ Q hvc₂
      show HoareE C (wpcE C c₁ (wpcE C c₂ Q).1).1 (.seq c₁.strip c₂.strip) Q
        (fun σ => (wpcE C c₁ (wpcE C c₂ Q).1).2 σ + (wpcE C c₂ Q).2 σ)
      refine HoareE.of_pointwise (fun σ₀ hσ₀ => ?_)

      have hA := ih₁ (wpcE C c₂ Q).1 hvc₁
      have hB := ih₁ (fun σ' => (wpcE C c₂ Q).2 σ' = (wpcE C c₂ Q).2 σ₀) (hvcpres σ₀)
      have hA' : HoareE C (fun σ => σ = σ₀) c₁.strip (wpcE C c₂ Q).1
          (wpcE C c₁ (wpcE C c₂ Q).1).2 :=
        HoareE.strengthen hA (fun σ hσ => by subst hσ; assumption)
      have hB' : HoareE C (fun σ => σ = σ₀) c₁.strip
          (fun σ' => (wpcE C c₂ Q).2 σ' = (wpcE C c₂ Q).2 σ₀)
          (wpcE C c₁ (wpcE C c₂ Q).1).2 := by
        refine HoareE.conseq hB (fun σ hσ => by rw [hσ]; have h' := hpres σ₀ hσ₀; assumption)
          (fun _ h => h) (fun σ hσ => ?_)

        apply wpcE_cost_indep
      have hconj := HoareE.conj hA' hB'
      refine HoareE.conseq (HoareE.seq ((wpcE C c₂ Q).2 σ₀) hconj h₂)
        (fun _ h => h) (fun _ h => h) (fun σ hσ => ?_)
      subst hσ
      rfl
  | ite b c₁ c₂ ih₁ ih₂ =>
      intro Q hvc
      obtain ⟨hvc₁, hvc₂⟩ := hvc
      have h₁ := ih₁ Q hvc₁
      have h₂ := ih₂ Q hvc₂
      show HoareE C _ (.ite b c₁.strip c₂.strip) Q
        (fun σ => (wpcE C c₁ Q).2 σ + tbcost C b σ)
      refine HoareE.ite (T := (wpcE C c₁ Q).2)
        (HoareE.strengthen h₁ (fun σ hσ => by
          rcases hσ with ⟨⟨⟨x11, _⟩, _⟩, y⟩; apply x11; assumption)) ?_
      refine HoareE.conseq h₂ (fun σ hσ => by
        rcases hσ with ⟨⟨⟨_, x12⟩, _⟩, y⟩; apply x12; assumption)
        (fun _ h => h) (fun σ hσ => ?_)
      rcases hσ with ⟨⟨⟨_, _⟩, x2⟩, _⟩
      apply x2.symm
  | «for» i a bE P ts cb c ih =>
      intro Q hvc
      obtain ⟨hai, hbi, hcb, hle, hbody, hexit, hvcbody⟩ := hvc
      show HoareE C (substA P i a) (Stmt.for i a bE c.strip) Q
        (fun σ => (tacost C a σ + C.assignV) +
          (aval bE σ - aval a σ).toNat * (cb + ts + incCost C) + cb)
      refine HoareE.conseq
        (HoareE.«for» (P := P) (i := i) (a := a) (bE := bE) (S := c.strip)
          (ts := ts) (cb := cb) hai hbi hcb hle (fun k av bv => ?_))
        (fun _ h => h) (fun σ hσ => by rcases hσ with ⟨h1, h2⟩; apply hexit <;> assumption)
        (fun _ _ => rfl)
      have hk := ih _ (hvcbody k av bv)
      refine HoareE.conseq hk (fun σ hσ => ?_) (fun _ h => h) (fun σ hσ => ?_)
      · obtain ⟨hP, hik, hav, hbv, havk, hkbv⟩ := hσ
        obtain ⟨hwp, _⟩ := hbody k av bv σ hP hik hav hbv havk hkbv
        assumption
      · obtain ⟨hP, hik, hav, hbv, havk, hkbv⟩ := hσ
        obtain ⟨_, hcost⟩ := hbody k av bv σ hP hik hav hbv havk hkbv
        assumption

theorem vcgE_sound {P : Assn} {c : AComE} {Q : Assn} {T : Cost}
    (h : VCGE C P c Q T) : HoareE C P (c.strip) Q T := by
  obtain ⟨hpre, hvc, hcost⟩ := h
  have hws := wpcE_sound c Q hvc
  apply HoareE.conseq <;> first | assumption | (intro σ h; aesop)

theorem vcgE_valid {P : Assn} {c : AComE} {Q : Assn} {T : Cost}
    (h : VCGE C P c Q T) : ValidExact C P (c.strip) Q T :=
  (vcgE_sound h).sound

end ResourcesLogic
