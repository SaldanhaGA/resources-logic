import Mathlib.Tactic

namespace ResourcesLogic

def IsBigO (f g : ℕ → ℕ) : Prop :=
  ∃ c n₀ : ℕ, 0 < c ∧ ∀ n, n₀ ≤ n → f n ≤ c * g n

def IsBigOmega (f g : ℕ → ℕ) : Prop := IsBigO g f

def IsBigTheta (f g : ℕ → ℕ) : Prop := IsBigO f g ∧ IsBigOmega f g

def bigO (g : ℕ → ℕ) : Set (ℕ → ℕ) := { f | IsBigO f g }

def bigΩ (g : ℕ → ℕ) : Set (ℕ → ℕ) := { f | IsBigOmega f g }

def bigΘ (g : ℕ → ℕ) : Set (ℕ → ℕ) := { f | IsBigTheta f g }

scoped notation:max "O(" g ")" => bigO g
scoped notation:max "Ω(" g ")" => bigΩ g
scoped notation:max "Θ(" g ")" => bigΘ g

@[simp] theorem mem_bigO {f g : ℕ → ℕ} : f ∈ O(g) ↔ IsBigO f g := Iff.rfl

@[simp] theorem mem_bigΩ {f g : ℕ → ℕ} : f ∈ Ω(g) ↔ IsBigOmega f g := Iff.rfl

@[simp] theorem mem_bigΘ {f g : ℕ → ℕ} : f ∈ Θ(g) ↔ IsBigTheta f g := Iff.rfl

theorem IsBigO.trans {f g h : ℕ → ℕ} (hfg : IsBigO f g) (hgh : IsBigO g h) :
    IsBigO f h := by
  obtain ⟨c₁, n₁, hc₁, h₁⟩ := hfg
  obtain ⟨c₂, n₂, hc₂, h₂⟩ := hgh
  refine ⟨c₁ * c₂, max n₁ n₂, by positivity, fun n hn => ?_⟩
  have hn₁ : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : n₂ ≤ n := le_trans (le_max_right _ _) hn
  calc f n ≤ c₁ * g n := h₁ n hn₁
    _ ≤ c₁ * (c₂ * h n) := Nat.mul_le_mul_left c₁ (h₂ n hn₂)
    _ = c₁ * c₂ * h n := by ring

theorem IsBigTheta.symm {f g : ℕ → ℕ} (h : IsBigTheta f g) : IsBigTheta g f := by
  rcases h with ⟨hO, hΩ⟩
  refine ⟨hΩ, hO⟩

theorem isBigO_linear {a b : ℕ} (ha : 0 < a) :
    IsBigO (fun n => a * n + b) (fun n => n) := by
  refine ⟨a + b, 1, by omega, fun n hn => ?_⟩
  have hb : b ≤ b * n := Nat.le_mul_of_pos_right b (by omega)
  calc a * n + b ≤ a * n + b * n := by omega
    _ = (a + b) * n := by ring

theorem isBigTheta_linear {a b : ℕ} (ha : 0 < a) :
    IsBigTheta (fun n => a * n + b) (fun n => n) := by
  refine ⟨isBigO_linear ha, ?_⟩

  refine ⟨1, 0, one_pos, fun n _ => ?_⟩
  have : n ≤ a * n := Nat.le_mul_of_pos_left n ha
  show n ≤ 1 * (a * n + b)
  omega

theorem isBigO_quadratic {a b c : ℕ} (ha : 0 < a) :
    IsBigO (fun n => a * n ^ 2 + b * n + c) (fun n => n ^ 2) := by
  refine ⟨a + b + c, 1, by omega, fun n hn => ?_⟩
  have h1 : n ≤ n ^ 2 := by nlinarith [hn]
  have h2 : 1 ≤ n ^ 2 := by nlinarith [hn]
  show a * n ^ 2 + b * n + c ≤ (a + b + c) * n ^ 2
  nlinarith [h1, h2, Nat.zero_le b, Nat.zero_le c]

theorem isBigTheta_quadratic {a b c : ℕ} (ha : 0 < a) :
    IsBigTheta (fun n => a * n ^ 2 + b * n + c) (fun n => n ^ 2) := by
  refine ⟨isBigO_quadratic ha, ?_⟩

  refine ⟨1, 0, one_pos, fun n _ => ?_⟩
  show n ^ 2 ≤ 1 * (a * n ^ 2 + b * n + c)
  nlinarith [ha, Nat.zero_le b, Nat.zero_le c, Nat.zero_le (n ^ 2)]

theorem isBigO_log {a b : ℕ} (ha : 0 < a) :
    IsBigO (fun n => a * Nat.log 2 n + b) (fun n => Nat.log 2 n) := by
  refine ⟨a + b, 2, by omega, fun n hn => ?_⟩
  have hlog : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  show a * Nat.log 2 n + b ≤ (a + b) * Nat.log 2 n
  nlinarith [hlog, Nat.zero_le a, Nat.zero_le b]

theorem isBigTheta_log {a b : ℕ} (ha : 0 < a) :
    IsBigTheta (fun n => a * Nat.log 2 n + b) (fun n => Nat.log 2 n) := by
  refine ⟨isBigO_log ha, ?_⟩

  refine ⟨1, 0, one_pos, fun n _ => ?_⟩
  have : Nat.log 2 n ≤ a * Nat.log 2 n := Nat.le_mul_of_pos_left _ ha
  show Nat.log 2 n ≤ 1 * (a * Nat.log 2 n + b)
  omega

theorem log_two_half (n : ℕ) : Nat.log 2 (n / 2) = Nat.log 2 n - 1 :=
  Nat.log_div_base 2 n

end ResourcesLogic
