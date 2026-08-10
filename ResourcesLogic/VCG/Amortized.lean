import ResourcesLogic.VCG.Classic
import ResourcesLogic.Hoare.Amortized

namespace ResourcesLogic

open Finset

variable {C : CostModel}

inductive AComA where
  | skip : AComA
  | assign : Ident → AExp → AComA
  | arrAssign : Ident → AExp → AExp → AComA
  | seq : AComA → AComA → AComA
  | ite : BExp → AComA → AComA → AComA

  | «while» : BExp → Assn → (State → Nat) → Nat → Nat → Cost → Nat → AComA → AComA

namespace AComA

def strip : AComA → Stmt
  | .skip => .skip
  | .assign x a => .assign x a
  | .arrAssign x a₁ a₂ => .arrAssign x a₁ a₂
  | .seq c₁ c₂ => .seq c₁.strip c₂.strip
  | .ite b c₁ c₂ => .ite b c₁.strip c₂.strip
  | .«while» b _ _ _ _ _ _ c => .while b c.strip

def toClassic : AComA → ACom
  | .skip => .skip
  | .assign x a => .assign x a
  | .arrAssign x a₁ a₂ => .arrAssign x a₁ a₂
  | .seq c₁ c₂ => .seq c₁.toClassic c₂.toClassic
  | .ite b c₁ c₂ => .ite b c₁.toClassic c₂.toClassic
  | .«while» b I f N a _ cb c => .«while» b I f N (fun _ => a) cb c.toClassic

@[simp] theorem strip_toClassic (c : AComA) : c.toClassic.strip = c.strip := by
  induction c with
  | skip => rfl
  | assign => rfl
  | arrAssign => rfl
  | seq _ _ ih₁ ih₂ => simp [toClassic, ACom.strip, strip, ih₁, ih₂]
  | ite _ _ _ ih₁ ih₂ => simp [toClassic, ACom.strip, strip, ih₁, ih₂]
  | «while» _ _ _ _ _ _ _ _ ih => simp [toClassic, ACom.strip, strip, ih]

inductive SigmaFree : AComA → Prop where
  | skip : SigmaFree .skip
  | assign {x : Ident} {a : AExp} : a.SigmaFree → SigmaFree (.assign x a)
  | arrAssign {x : Ident} {a₁ a₂ : AExp} :
      a₁.SigmaFree → a₂.SigmaFree → SigmaFree (.arrAssign x a₁ a₂)
  | seq {c₁ c₂ : AComA} : SigmaFree c₁ → SigmaFree c₂ → SigmaFree (.seq c₁ c₂)
  | ite {b : BExp} {c₁ c₂ : AComA} :
      b.SigmaFree → SigmaFree c₁ → SigmaFree c₂ → SigmaFree (.ite b c₁ c₂)
  | «while» {b : BExp} {I : Assn} {f : State → Nat} {N a : Nat} {φ : Cost}
      {cb : Nat} {c : AComA} :
      b.SigmaFree → SigmaFree c → SigmaFree (.«while» b I f N a φ cb c)

theorem sigmaFree_toClassic {c : AComA} (h : c.SigmaFree) : c.toClassic.SigmaFree := by
  induction h with
  | skip => apply ACom.SigmaFree.skip
  | assign ha => apply ACom.SigmaFree.assign <;> assumption
  | arrAssign h₁ h₂ => apply ACom.SigmaFree.arrAssign <;> assumption
  | seq _ _ ih₁ ih₂ => apply ACom.SigmaFree.seq <;> assumption
  | ite hb _ _ ih₁ ih₂ => apply ACom.SigmaFree.ite <;> assumption
  | «while» hb _ ih => apply ACom.SigmaFree.«while» <;> assumption

end AComA

def bodyCost (C : CostModel) (c : ACom) : Nat := (wpc C c (fun _ => True)).2 default

def wpcA (C : CostModel) : AComA → Assn → Assn × Cost
  | .skip, Q => (Q, fun _ => C.skip)
  | .assign x a, Q => (substA Q x a, fun σ => tacost C a σ + C.assignV)
  | .arrAssign x a₁ a₂, Q =>
      (substArr Q x a₁ a₂, fun σ => tacost C a₁ σ + tacost C a₂ σ + C.assignA)
  | .seq c₁ c₂, Q =>
      ((wpcA C c₁ (wpcA C c₂ Q).1).1,
       fun σ => (wpcA C c₁ (wpcA C c₂ Q).1).2 σ + (wpcA C c₂ Q).2 σ)
  | .ite b c₁ c₂, Q =>
      (fun σ => (bval b σ = true → (wpcA C c₁ Q).1 σ) ∧
                (bval b σ = false → (wpcA C c₂ Q).1 σ),
       fun σ => max ((wpcA C c₁ Q).2 σ) ((wpcA C c₂ Q).2 σ) + tbcost C b σ)

  | .«while» _ I _ N a φ cb _, _ =>
      (fun σ => I σ ∧ φ σ = 0, fun _ => N * a + (N + 1) * cb)

def VCA (C : CostModel) : AComA → Assn → Prop
  | .skip, _ => True
  | .assign _ _, _ => True
  | .arrAssign _ _ _, _ => True
  | .seq c₁ c₂, Q => VCA C c₁ (wpcA C c₂ Q).1 ∧ VCA C c₂ Q
  | .ite _ c₁ c₂, Q => VCA C c₁ Q ∧ VCA C c₂ Q
  | .«while» b I f N a φ cb c, Q =>

      (∀ k n : Nat, ∀ σ, I σ → bval b σ = true → f σ = k → φ σ = n →
        (wpcA C c (fun σ' => I σ' ∧ k < f σ' ∧
                    bodyCost C c.toClassic + φ σ' ≤ a + n)).1 σ) ∧
      (∀ σ, I σ → bval b σ = false → Q σ) ∧
      (∀ σ, I σ → bval b σ = true → f σ < N) ∧
      (∀ σ, I σ → tbcost C b σ = cb) ∧
      (∀ k n : Nat, VCA C c (fun σ' => I σ' ∧ k < f σ' ∧
                    bodyCost C c.toClassic + φ σ' ≤ a + n))

def VCGA (C : CostModel) (P : Assn) (c : AComA) (Q : Assn) (T : Cost) : Prop :=
  (∀ σ, P σ → (wpcA C c Q).1 σ) ∧ VCA C c Q ∧ (∀ σ, P σ → (wpcA C c Q).2 σ ≤ T σ)

theorem wpcA_cost_eq {c : AComA} (hsf : c.SigmaFree) (Q : Assn) (Q' : Assn) (σ : State) :
    (wpcA C c Q).2 σ = (wpc C c.toClassic Q').2 σ := by
  induction hsf generalizing Q Q' with
  | skip => rfl
  | assign _ => rfl
  | arrAssign _ _ => rfl
  | @seq c₁ c₂ _ _ ih₁ ih₂ =>
      show (wpcA C c₁ _).2 σ + (wpcA C c₂ Q).2 σ
          = (wpc C c₁.toClassic _).2 σ + (wpc C c₂.toClassic Q').2 σ
      rw [ih₁ (wpcA C c₂ Q).1 (wpc C c₂.toClassic Q').1, ih₂ Q Q']
  | @ite b c₁ c₂ _ _ _ ih₁ ih₂ =>
      show max ((wpcA C c₁ Q).2 σ) ((wpcA C c₂ Q).2 σ) + tbcost C b σ
          = max ((wpc C c₁.toClassic Q').2 σ) ((wpc C c₂.toClassic Q').2 σ) + tbcost C b σ
      rw [ih₁ Q Q', ih₂ Q Q']
  | @«while» b I f N a φ cb c _ _ _ =>
      show N * a + (N + 1) * cb = (∑ _i ∈ Finset.range N, a) + (N + 1) * cb
      simp [Finset.sum_const, mul_comm]

theorem wpcA_cost_const {c : AComA} (hsf : c.SigmaFree) (Q : Assn) (σ σ' : State) :
    (wpcA C c Q).2 σ = (wpcA C c Q).2 σ' := by
  rw [wpcA_cost_eq hsf Q (fun _ => True) σ, wpcA_cost_eq hsf Q (fun _ => True) σ']
  apply wpc_cost_const
  apply AComA.sigmaFree_toClassic <;> assumption

theorem wpcA_cost_bodyCost {c : AComA} (hsf : c.SigmaFree) (Q : Assn) (σ : State) :
    (wpcA C c Q).2 σ = bodyCost C c.toClassic := by
  rw [wpcA_cost_eq hsf Q (fun _ => True) σ]
  apply wpc_cost_const
  apply AComA.sigmaFree_toClassic <;> assumption

theorem wpcA_sound {c : AComA} (hsf : c.SigmaFree) :
    ∀ Q : Assn, VCA C c Q → Hoare C (wpcA C c Q).1 (c.strip) Q (wpcA C c Q).2 := by
  induction hsf with
  | skip => intro Q _; apply Hoare.skip
  | assign _ => intro Q _; apply Hoare.assign
  | arrAssign _ _ => intro Q _; apply Hoare.arrAssign
  | @seq c₁ c₂ hsf₁ hsf₂ ih₁ ih₂ =>
      intro Q hvc
      obtain ⟨hvc₁, hvc₂⟩ := hvc
      have h₂ := ih₂ Q hvc₂
      have h₁ := ih₁ (wpcA C c₂ Q).1 hvc₁
      have hconst := wpcA_cost_const (C := C) hsf₂ Q
      show Hoare C (wpcA C c₁ (wpcA C c₂ Q).1).1 (.seq c₁.strip c₂.strip) Q
        (fun σ => (wpcA C c₁ (wpcA C c₂ Q).1).2 σ + (wpcA C c₂ Q).2 σ)
      refine Hoare.conseq (Hoare.seq ((wpcA C c₂ Q).2 default)
        (Hoare.weaken h₁ (fun σ hq => ⟨hq, le_of_eq (hconst σ default)⟩)) h₂)
        (fun _ h => h) (fun _ h => h) (fun σ _ => ?_)
      show (wpcA C c₁ (wpcA C c₂ Q).1).2 σ + (wpcA C c₂ Q).2 default
          ≤ (wpcA C c₁ (wpcA C c₂ Q).1).2 σ + (wpcA C c₂ Q).2 σ
      rw [hconst default σ]
  | @ite b c₁ c₂ _ _ _ ih₁ ih₂ =>
      intro Q hvc
      obtain ⟨hvc₁, hvc₂⟩ := hvc
      have h₁ := ih₁ Q hvc₁
      have h₂ := ih₂ Q hvc₂
      apply Hoare.ite
      · apply Hoare.strengthen <;>
          first | assumption | (intro σ hσ; obtain ⟨⟨h, _⟩, hb⟩ := hσ; apply h; assumption)
      · apply Hoare.strengthen <;>
          first | assumption | (intro σ hσ; obtain ⟨⟨_, h⟩, hb⟩ := hσ; apply h; assumption)
  | @«while» b I f N a φ cb c hb hsfc ih =>
      intro Q hvc
      obtain ⟨hbody, hexit, hvar, hcb, hvcbody⟩ := hvc
      have hrule :
          Hoare C (fun σ => I σ ∧ φ σ = 0) (.while b c.strip)
            (fun σ => I σ ∧ bval b σ = false) (fun _ => N * a + (N + 1) * cb) := by
        refine Hoare.while_amortized (φ := φ) (Tb := fun _ => bodyCost C c.toClassic)
          hcb hvar (fun k n cc => ?_)
        by_cases hcc : cc = bodyCost C c.toClassic
        ·
          have hk := ih (fun σ' => I σ' ∧ k < f σ' ∧
            bodyCost C c.toClassic + φ σ' ≤ a + n) (hvcbody k n)
          refine Hoare.conseq hk ?_ ?_ (fun σ _ => ?_)
          · intro σ hσ
            rcases hσ with ⟨h1, h2, h3, h4, h5⟩
            apply hbody <;> assumption
          · intro σ' hσ'
            rcases hσ' with ⟨p1, p2, p3⟩
            refine ⟨p1, p2, ?_⟩
            rw [hcc]; apply p3
          have hbc := wpcA_cost_bodyCost (C := C) hsfc
            (fun σ' => I σ' ∧ k < f σ' ∧ bodyCost C c.toClassic + φ σ' ≤ a + n) σ
          show (wpcA C c _).2 σ ≤ bodyCost C c.toClassic
          omega
        ·
          apply Hoare.strengthen <;> first | apply Hoare.false_pre | (intro σ hσ; aesop)
      show Hoare C (fun σ => I σ ∧ φ σ = 0) (.while b c.strip) Q
        (fun _ => N * a + (N + 1) * cb)
      apply Hoare.weaken <;> first | assumption | (intro σ hσ; aesop)

theorem vcgA_sound {P : Assn} {c : AComA} {Q : Assn} {T : Cost}
    (hsf : c.SigmaFree) (h : VCGA C P c Q T) : Hoare C P (c.strip) Q T := by
  obtain ⟨hpre, hvc, hcost⟩ := h
  have hws := wpcA_sound hsf Q hvc
  apply Hoare.conseq <;> first | assumption | (intro σ h; aesop)

theorem vcgA_valid {P : Assn} {c : AComA} {Q : Assn} {T : Cost}
    (hsf : c.SigmaFree) (h : VCGA C P c Q T) : Valid C P (c.strip) Q T :=
  (vcgA_sound hsf h).sound

end ResourcesLogic
