import ResourcesLogic.Syntax
import ResourcesLogic.CostModel

namespace ResourcesLogic

def sumAux (f : Int → Int) : Int → Nat → Int
  | _, 0 => 0
  | lo, n + 1 => f lo + sumAux f (lo + 1) n

def sumRange (f : Int → Int) (lo hi : Int) : Int :=
  sumAux f lo (hi + 1 - lo).toNat

def aval : AExp → State → Int
  | .num n, _ => n
  | .var x, σ => σ (.var x)
  | .arr x a, σ => σ (.arr x (aval a σ))
  | .add a₁ a₂, σ => aval a₁ σ + aval a₂ σ
  | .sub a₁ a₂, σ => aval a₁ σ - aval a₂ σ
  | .mul a₁ a₂, σ => aval a₁ σ * aval a₂ σ
  | .div a₁ a₂, σ => aval a₁ σ / aval a₂ σ
  | .pow a₁ a₂, σ => aval a₁ σ ^ (aval a₂ σ).toNat
  | .sum x lo hi body, σ =>
      sumRange (fun v => aval body (σ[Loc.var x ↦ v])) (aval lo σ) (aval hi σ)

def bval : BExp → State → Bool
  | .tt, _ => true
  | .ff, _ => false
  | .eq a₁ a₂, σ => aval a₁ σ = aval a₂ σ
  | .ne a₁ a₂, σ => aval a₁ σ ≠ aval a₂ σ
  | .lt a₁ a₂, σ => aval a₁ σ < aval a₂ σ
  | .gt a₁ a₂, σ => aval a₁ σ > aval a₂ σ
  | .le a₁ a₂, σ => aval a₁ σ ≤ aval a₂ σ
  | .ge a₁ a₂, σ => aval a₁ σ ≥ aval a₂ σ
  | .neg b, σ => !bval b σ
  | .and b₁ b₂, σ => bval b₁ σ && bval b₂ σ
  | .or b₁ b₂, σ => bval b₁ σ || bval b₂ σ

variable (C : CostModel)

def tacost : AExp → State → Nat
  | .num _, _ => C.cst
  | .var _, _ => C.var
  | .arr _ a, σ => tacost a σ + C.array
  | .add a₁ a₂, σ => tacost a₁ σ + tacost a₂ σ + C.add
  | .sub a₁ a₂, σ => tacost a₁ σ + tacost a₂ σ + C.sub
  | .mul a₁ a₂, σ => tacost a₁ σ + tacost a₂ σ + C.mul
  | .div a₁ a₂, σ => tacost a₁ σ + tacost a₂ σ + C.div
  | .pow a₁ a₂, σ => tacost a₁ σ + tacost a₂ σ + C.pow
  | .sum _ lo hi body, σ => (aval hi σ - aval lo σ).toNat * tacost body σ

def tbcost : BExp → State → Nat
  | .tt, _ => C.bool
  | .ff, _ => C.bool
  | .eq a₁ a₂, σ => tacost C a₁ σ + tacost C a₂ σ + C.eq
  | .ne a₁ a₂, σ => tacost C a₁ σ + tacost C a₂ σ + C.ne
  | .lt a₁ a₂, σ => tacost C a₁ σ + tacost C a₂ σ + C.lt
  | .gt a₁ a₂, σ => tacost C a₁ σ + tacost C a₂ σ + C.gt
  | .le a₁ a₂, σ => tacost C a₁ σ + tacost C a₂ σ + C.le
  | .ge a₁ a₂, σ => tacost C a₁ σ + tacost C a₂ σ + C.ge
  | .neg b, σ => tbcost b σ + C.neg
  | .and b₁ b₂, σ => tbcost b₁ σ + tbcost b₂ σ + C.and
  | .or b₁ b₂, σ => tbcost b₁ σ + tbcost b₂ σ + C.or

inductive Eval (C : CostModel) : Stmt → State → Nat → State → Prop where
  | skip {σ} : Eval C .skip σ C.skip σ
  | assign {σ x a} :
      Eval C (.assign x a) σ (tacost C a σ + C.assignV) (σ[Loc.var x ↦ aval a σ])
  | arrAssign {σ x a₁ a₂} :
      Eval C (.arrAssign x a₁ a₂) σ (tacost C a₁ σ + tacost C a₂ σ + C.assignA)
        (σ[Loc.arr x (aval a₁ σ) ↦ aval a₂ σ])
  | seq {σ σ' σ'' S₁ S₂ t₁ t₂} :
      Eval C S₁ σ t₁ σ' → Eval C S₂ σ' t₂ σ'' → Eval C (.seq S₁ S₂) σ (t₁ + t₂) σ''
  | iteT {σ σ' b S₁ S₂ t} :
      bval b σ = true → Eval C S₁ σ t σ' → Eval C (.ite b S₁ S₂) σ (tbcost C b σ + t) σ'
  | iteF {σ σ' b S₁ S₂ t} :
      bval b σ = false → Eval C S₂ σ t σ' → Eval C (.ite b S₁ S₂) σ (tbcost C b σ + t) σ'
  | whileT {σ σ' σ'' b S t t'} :
      bval b σ = true → Eval C S σ t σ'' → Eval C (.while b S) σ'' t' σ' →
      Eval C (.while b S) σ (tbcost C b σ + t + t') σ'
  | whileF {σ b S} :
      bval b σ = false → Eval C (.while b S) σ (tbcost C b σ) σ

namespace Eval

theorem deterministic {C : CostModel} {S : Stmt} {σ σ₁ σ₂ : State} {t₁ t₂ : Nat}
    (h₁ : Eval C S σ t₁ σ₁) (h₂ : Eval C S σ t₂ σ₂) : t₁ = t₂ ∧ σ₁ = σ₂ := by
  induction h₁ generalizing t₂ σ₂ with
  | skip => cases h₂; constructor <;> rfl
  | assign => cases h₂; constructor <;> rfl
  | arrAssign => cases h₂; constructor <;> rfl
  | seq _ _ ih₁ ih₂ =>
      cases h₂ with
      | seq h₁' h₂' =>
          obtain ⟨rfl, rfl⟩ := ih₁ h₁'
          obtain ⟨rfl, rfl⟩ := ih₂ h₂'
          constructor <;> rfl
  | iteT hb _ ih =>
      cases h₂ with
      | iteT _ h' => obtain ⟨rfl, rfl⟩ := ih h'; constructor <;> rfl
      | iteF hb' _ => simp_all
  | iteF hb _ ih =>
      cases h₂ with
      | iteT hb' _ => simp_all
      | iteF _ h' => obtain ⟨rfl, rfl⟩ := ih h'; constructor <;> rfl
  | whileT hb _ _ ihS ihW =>
      cases h₂ with
      | whileT _ hS' hW' =>
          obtain ⟨rfl, rfl⟩ := ihS hS'
          obtain ⟨rfl, rfl⟩ := ihW hW'
          constructor <;> rfl
      | whileF hb' => simp_all
  | whileF hb =>
      cases h₂ with
      | whileT hb' _ _ => simp_all
      | whileF _ => constructor <;> rfl

theorem cost_unique {C : CostModel} {S : Stmt} {σ σ₁ σ₂ : State} {t₁ t₂ : Nat}
    (h₁ : Eval C S σ t₁ σ₁) (h₂ : Eval C S σ t₂ σ₂) : t₁ = t₂ := by
  rcases deterministic h₁ h₂ with ⟨h, _⟩
  assumption

theorem state_unique {C : CostModel} {S : Stmt} {σ σ₁ σ₂ : State} {t₁ t₂ : Nat}
    (h₁ : Eval C S σ t₁ σ₁) (h₂ : Eval C S σ t₂ σ₂) : σ₁ = σ₂ := by
  rcases deterministic h₁ h₂ with ⟨_, h⟩
  assumption

end Eval

end ResourcesLogic
