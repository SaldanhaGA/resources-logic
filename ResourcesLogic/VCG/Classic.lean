import ResourcesLogic.Hoare.Rules

namespace ResourcesLogic

open Finset

variable {C : CostModel}

inductive AExp.SigmaFree : AExp → Prop where
  | num {n : Int} : AExp.SigmaFree (.num n)
  | var {x : Ident} : AExp.SigmaFree (.var x)
  | arr {x : Ident} {a : AExp} : AExp.SigmaFree a → AExp.SigmaFree (.arr x a)
  | add {a₁ a₂ : AExp} : AExp.SigmaFree a₁ → AExp.SigmaFree a₂ → AExp.SigmaFree (.add a₁ a₂)
  | sub {a₁ a₂ : AExp} : AExp.SigmaFree a₁ → AExp.SigmaFree a₂ → AExp.SigmaFree (.sub a₁ a₂)
  | mul {a₁ a₂ : AExp} : AExp.SigmaFree a₁ → AExp.SigmaFree a₂ → AExp.SigmaFree (.mul a₁ a₂)
  | div {a₁ a₂ : AExp} : AExp.SigmaFree a₁ → AExp.SigmaFree a₂ → AExp.SigmaFree (.div a₁ a₂)
  | pow {a₁ a₂ : AExp} : AExp.SigmaFree a₁ → AExp.SigmaFree a₂ → AExp.SigmaFree (.pow a₁ a₂)

inductive BExp.SigmaFree : BExp → Prop where
  | tt : BExp.SigmaFree .tt
  | ff : BExp.SigmaFree .ff
  | eq {a₁ a₂ : AExp} : AExp.SigmaFree a₁ → AExp.SigmaFree a₂ → BExp.SigmaFree (.eq a₁ a₂)
  | ne {a₁ a₂ : AExp} : AExp.SigmaFree a₁ → AExp.SigmaFree a₂ → BExp.SigmaFree (.ne a₁ a₂)
  | lt {a₁ a₂ : AExp} : AExp.SigmaFree a₁ → AExp.SigmaFree a₂ → BExp.SigmaFree (.lt a₁ a₂)
  | gt {a₁ a₂ : AExp} : AExp.SigmaFree a₁ → AExp.SigmaFree a₂ → BExp.SigmaFree (.gt a₁ a₂)
  | le {a₁ a₂ : AExp} : AExp.SigmaFree a₁ → AExp.SigmaFree a₂ → BExp.SigmaFree (.le a₁ a₂)
  | ge {a₁ a₂ : AExp} : AExp.SigmaFree a₁ → AExp.SigmaFree a₂ → BExp.SigmaFree (.ge a₁ a₂)
  | neg {b : BExp} : BExp.SigmaFree b → BExp.SigmaFree (.neg b)
  | and {b₁ b₂ : BExp} : BExp.SigmaFree b₁ → BExp.SigmaFree b₂ → BExp.SigmaFree (.and b₁ b₂)
  | or {b₁ b₂ : BExp} : BExp.SigmaFree b₁ → BExp.SigmaFree b₂ → BExp.SigmaFree (.or b₁ b₂)

theorem tacost_const {a : AExp} (h : a.SigmaFree) (σ σ' : State) :
    tacost C a σ = tacost C a σ' := by
  induction h with
  | num => rfl
  | var => rfl
  | arr _ ih => simp [tacost, ih]
  | add _ _ ih₁ ih₂ => simp [tacost, ih₁, ih₂]
  | sub _ _ ih₁ ih₂ => simp [tacost, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp [tacost, ih₁, ih₂]
  | div _ _ ih₁ ih₂ => simp [tacost, ih₁, ih₂]
  | pow _ _ ih₁ ih₂ => simp [tacost, ih₁, ih₂]

theorem tbcost_const {b : BExp} (h : b.SigmaFree) (σ σ' : State) :
    tbcost C b σ = tbcost C b σ' := by
  induction h with
  | tt => rfl
  | ff => rfl
  | eq h₁ h₂ => simp [tbcost, tacost_const h₁ σ σ', tacost_const h₂ σ σ']
  | ne h₁ h₂ => simp [tbcost, tacost_const h₁ σ σ', tacost_const h₂ σ σ']
  | lt h₁ h₂ => simp [tbcost, tacost_const h₁ σ σ', tacost_const h₂ σ σ']
  | gt h₁ h₂ => simp [tbcost, tacost_const h₁ σ σ', tacost_const h₂ σ σ']
  | le h₁ h₂ => simp [tbcost, tacost_const h₁ σ σ', tacost_const h₂ σ σ']
  | ge h₁ h₂ => simp [tbcost, tacost_const h₁ σ σ', tacost_const h₂ σ σ']
  | neg _ ih => simp [tbcost, ih]
  | and _ _ ih₁ ih₂ => simp [tbcost, ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp [tbcost, ih₁, ih₂]

inductive ACom where
  | skip : ACom
  | assign : Ident → AExp → ACom
  | arrAssign : Ident → AExp → AExp → ACom
  | seq : ACom → ACom → ACom
  | ite : BExp → ACom → ACom → ACom

  | «while» : BExp → Assn → (State → Nat) → Nat → (Nat → Nat) → Nat → ACom → ACom

namespace ACom

def strip : ACom → Stmt
  | .skip => .skip
  | .assign x a => .assign x a
  | .arrAssign x a₁ a₂ => .arrAssign x a₁ a₂
  | .seq c₁ c₂ => .seq c₁.strip c₂.strip
  | .ite b c₁ c₂ => .ite b c₁.strip c₂.strip
  | .«while» b _ _ _ _ _ c => .while b c.strip

inductive SigmaFree : ACom → Prop where
  | skip : SigmaFree .skip
  | assign {x : Ident} {a : AExp} : a.SigmaFree → SigmaFree (.assign x a)
  | arrAssign {x : Ident} {a₁ a₂ : AExp} :
      a₁.SigmaFree → a₂.SigmaFree → SigmaFree (.arrAssign x a₁ a₂)
  | seq {c₁ c₂ : ACom} : SigmaFree c₁ → SigmaFree c₂ → SigmaFree (.seq c₁ c₂)
  | ite {b : BExp} {c₁ c₂ : ACom} :
      b.SigmaFree → SigmaFree c₁ → SigmaFree c₂ → SigmaFree (.ite b c₁ c₂)
  | «while» {b : BExp} {I : Assn} {f : State → Nat} {N : Nat} {t : Nat → Nat}
      {cb : Nat} {c : ACom} :
      b.SigmaFree → SigmaFree c → SigmaFree (.«while» b I f N t cb c)

end ACom

def wpc (C : CostModel) : ACom → Assn → Assn × Cost
  | .skip, Q => (Q, fun _ => C.skip)
  | .assign x a, Q => (substA Q x a, fun σ => tacost C a σ + C.assignV)
  | .arrAssign x a₁ a₂, Q =>
      (substArr Q x a₁ a₂, fun σ => tacost C a₁ σ + tacost C a₂ σ + C.assignA)
  | .seq c₁ c₂, Q =>
      ((wpc C c₁ (wpc C c₂ Q).1).1,
       fun σ => (wpc C c₁ (wpc C c₂ Q).1).2 σ + (wpc C c₂ Q).2 σ)
  | .ite b c₁ c₂, Q =>
      (fun σ => (bval b σ = true → (wpc C c₁ Q).1 σ) ∧
                (bval b σ = false → (wpc C c₂ Q).1 σ),
       fun σ => max ((wpc C c₁ Q).2 σ) ((wpc C c₂ Q).2 σ) + tbcost C b σ)
  | .«while» _ I _ N t cb _, _ =>
      (I, fun _ => (∑ i ∈ Finset.range N, t i) + (N + 1) * cb)

def VC (C : CostModel) : ACom → Assn → Prop
  | .skip, _ => True
  | .assign _ _, _ => True
  | .arrAssign _ _ _, _ => True
  | .seq c₁ c₂, Q => VC C c₁ (wpc C c₂ Q).1 ∧ VC C c₂ Q
  | .ite _ c₁ c₂, Q => VC C c₁ Q ∧ VC C c₂ Q
  | .«while» b I f N t cb c, Q =>

      (∀ k : Nat, ∀ σ, I σ → bval b σ = true → f σ = k →
        (wpc C c (fun σ' => I σ' ∧ k < f σ')).1 σ ∧
        (wpc C c (fun σ' => I σ' ∧ k < f σ')).2 σ ≤ t k) ∧

      (∀ σ, I σ → bval b σ = false → Q σ) ∧

      (∀ σ, I σ → bval b σ = true → f σ < N) ∧

      (∀ σ, I σ → tbcost C b σ = cb) ∧

      (∀ k : Nat, VC C c (fun σ' => I σ' ∧ k < f σ'))

def VCG (C : CostModel) (P : Assn) (c : ACom) (Q : Assn) (T : Cost) : Prop :=
  (∀ σ, P σ → (wpc C c Q).1 σ) ∧ VC C c Q ∧ (∀ σ, P σ → (wpc C c Q).2 σ ≤ T σ)

theorem wpc_cost_const {c : ACom} (hsf : c.SigmaFree) (Q : Assn) (σ σ' : State) :
    (wpc C c Q).2 σ = (wpc C c Q).2 σ' := by
  induction hsf generalizing Q with
  | skip => rfl
  | assign ha => simp [wpc, tacost_const ha σ σ']
  | arrAssign ha₁ ha₂ => simp [wpc, tacost_const ha₁ σ σ', tacost_const ha₂ σ σ']
  | @seq c₁ c₂ _ _ ih₁ ih₂ =>
      show (wpc C c₁ (wpc C c₂ Q).1).2 σ + (wpc C c₂ Q).2 σ
          = (wpc C c₁ (wpc C c₂ Q).1).2 σ' + (wpc C c₂ Q).2 σ'
      rw [ih₁ (wpc C c₂ Q).1, ih₂ Q]
  | @ite b c₁ c₂ hb _ _ ih₁ ih₂ =>
      show max ((wpc C c₁ Q).2 σ) ((wpc C c₂ Q).2 σ) + tbcost C b σ
          = max ((wpc C c₁ Q).2 σ') ((wpc C c₂ Q).2 σ') + tbcost C b σ'
      rw [ih₁ Q, ih₂ Q, tbcost_const hb σ σ']
  | «while» _ _ => rfl

theorem wpc_sound {c : ACom} (hsf : c.SigmaFree) :
    ∀ Q : Assn, VC C c Q → Hoare C (wpc C c Q).1 (c.strip) Q (wpc C c Q).2 := by
  induction hsf with
  | skip => intro Q _; apply Hoare.skip
  | assign _ => intro Q _; apply Hoare.assign
  | arrAssign _ _ => intro Q _; apply Hoare.arrAssign
  | @seq c₁ c₂ hsf₁ hsf₂ ih₁ ih₂ =>
      intro Q hvc
      obtain ⟨hvc₁, hvc₂⟩ := hvc
      have h₂ := ih₂ Q hvc₂
      have h₁ := ih₁ (wpc C c₂ Q).1 hvc₁

      have hconst : ∀ σ σ', (wpc C c₂ Q).2 σ = (wpc C c₂ Q).2 σ' :=
        wpc_cost_const hsf₂ Q
      show Hoare C (wpc C c₁ (wpc C c₂ Q).1).1 (.seq c₁.strip c₂.strip) Q
        (fun σ => (wpc C c₁ (wpc C c₂ Q).1).2 σ + (wpc C c₂ Q).2 σ)
      refine Hoare.conseq (Hoare.seq ((wpc C c₂ Q).2 default)
        (Hoare.weaken h₁ (fun σ hq => ⟨hq, le_of_eq (hconst σ default)⟩)) h₂)
        (fun _ h => h) (fun _ h => h) (fun σ _ => ?_)
      show (wpc C c₁ (wpc C c₂ Q).1).2 σ + (wpc C c₂ Q).2 default
          ≤ (wpc C c₁ (wpc C c₂ Q).1).2 σ + (wpc C c₂ Q).2 σ
      rw [hconst default σ]
  | @ite b c₁ c₂ hb hsf₁ hsf₂ ih₁ ih₂ =>
      intro Q hvc
      obtain ⟨hvc₁, hvc₂⟩ := hvc
      have h₁ := ih₁ Q hvc₁
      have h₂ := ih₂ Q hvc₂
      apply Hoare.ite
      · apply Hoare.strengthen <;>
          first | assumption | (intro σ hσ; obtain ⟨⟨h, _⟩, hb⟩ := hσ; apply h; assumption)
      · apply Hoare.strengthen <;>
          first | assumption | (intro σ hσ; obtain ⟨⟨_, h⟩, hb⟩ := hσ; apply h; assumption)
  | @«while» b I f N t cb c hb hsfc ih =>
      intro Q hvc
      obtain ⟨hbody, hexit, hvar, hcb, hvcbody⟩ := hvc
      have hrule :
          Hoare C I (.while b c.strip) (fun σ => I σ ∧ bval b σ = false)
            (fun _ => (∑ i ∈ Finset.range N, t i) + (N + 1) * cb) := by
        refine Hoare.while_thesis hcb hvar (fun k => ?_)
        have hk := ih (fun σ' => I σ' ∧ k < f σ') (hvcbody k)
        refine Hoare.conseq hk ?_ (fun _ h => h) ?_
        · intro σ hσ
          rcases hσ with ⟨h1, h2, h3⟩
          rcases hbody k σ h1 h2 h3 with ⟨hw, _⟩
          assumption
        · intro σ hσ
          rcases hσ with ⟨h1, h2, h3⟩
          rcases hbody k σ h1 h2 h3 with ⟨_, hc⟩
          assumption
      apply Hoare.weaken <;> first | assumption | (intro σ hσ; aesop)

theorem vcg_sound {P : Assn} {c : ACom} {Q : Assn} {T : Cost}
    (hsf : c.SigmaFree) (h : VCG C P c Q T) : Hoare C P (c.strip) Q T := by
  obtain ⟨hpre, hvc, hcost⟩ := h
  have hws := wpc_sound hsf Q hvc
  apply Hoare.conseq <;> first | assumption | (intro σ h; aesop)

theorem vcg_valid {P : Assn} {c : ACom} {Q : Assn} {T : Cost}
    (hsf : c.SigmaFree) (h : VCG C P c Q T) : Valid C P (c.strip) Q T :=
  (vcg_sound hsf h).sound

end ResourcesLogic
