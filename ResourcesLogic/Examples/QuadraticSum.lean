import ResourcesLogic.VCG.Exact

namespace ResourcesLogic
namespace Examples
namespace QuadraticSum

def body : AComE :=
  .assign "s" (.add (.var "s") (.sum "k" (.num 0) (.var "n") (.num 1)))

variable (N : Int)

def inv : Assn := fun σ => σ (.var "n") = N ∧ 0 ≤ σ (.var "i") ∧ 0 ≤ N

def prog : AComE :=
  .seq (.assign "s" (.num 0))
    (.«for» "i" (.num 0) (.var "n") (inv N) (N.toNat + 3) 3 body)

def pre : Assn := fun σ => σ (.var "n") = N ∧ 0 ≤ N

def post : Assn := fun σ => σ (.var "i") = σ (.var "n") ∧ σ (.var "n") = N

def cost : Cost := fun σ => (σ (.var "n")).toNat ^ 2 + 10 * (σ (.var "n")).toNat + 7

theorem prog_strip : (prog N).strip =
    .seq (.assign "s" (.num 0))
      (Stmt.for "i" (.num 0) (.var "n") body.strip) := rfl

theorem vcg_holds : VCGE unitModel (pre N) (prog N) (post N) cost := by
  refine ⟨?_, ⟨trivial, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  ·
    rintro σ ⟨hn, hN⟩
    refine ⟨?_, ?_, hN⟩ <;> simp [aval, State.update, hn]
  ·
    intro σ v; rfl
  ·
    intro σ v; simp [aval, State.update]
  ·
    intro σ; simp [tbcost, tacost, unitModel]
  ·
    rintro σ hσ
    obtain ⟨hn, hi, hN⟩ : inv N (σ[Loc.var "i" ↦ aval (.num 0) σ]) := hσ
    simp only [aval] at hn ⊢
    simp [State.update] at hn
    omega
  ·
    rintro k av bv σ ⟨hn, hi, hN⟩ hik hav hbv hle hlt
    simp only [aval] at hav hbv
    subst hav
    subst hbv
    constructor
    · refine ⟨⟨?_, ?_, hN⟩, ?_, ?_, ?_⟩ <;>
        simp [aval, State.update, hn, hik] <;> omega
    · simp [wpcE, body, tacost, aval, unitModel, hn] <;> omega
  ·
    rintro σ ⟨hn, hi, hN⟩ hexit
    constructor
    · simpa [aval] using hexit
    · assumption
  ·
    intro k av bv
    trivial
  ·
    intro σ₀
    trivial
  ·
    intro σ₀ _
    simp [wpcE, substA, aval, State.update, tacost]
  ·
    rintro σ ⟨hn, hN⟩
    simp only [prog, wpcE, cost, aval, tacost, unitModel, incCost, hn]
    have hm : (N - 0).toNat = N.toNat := by simp
    rw [hm]
    ring

theorem quadratic_exact :
    ValidExact unitModel (pre N) ((prog N).strip) (post N) cost :=
  vcgE_valid (vcg_holds N)

theorem quadratic_hoareE :
    HoareE unitModel (pre N) ((prog N).strip) (post N) cost :=
  vcgE_sound (vcg_holds N)

def preFam (n : ℕ) : Assn := pre (n : Int)

def postFam (n : ℕ) : Assn := post (n : Int)

theorem quadratic_theta :
    ThetaExactValid unitModel preFam ((prog 0).strip) postFam (fun n => n ^ 2) := by
  refine ⟨fun n => 1 * n ^ 2 + 10 * n + 7, isBigTheta_quadratic (by norm_num), fun n => ?_⟩
  have h := quadratic_exact (n : Int)
  rw [prog_strip] at h ⊢
  refine h.cost_congr ?_
  intro σ hσ
  obtain ⟨hn, -⟩ := hσ
  simp only [cost]
  rw [hn, Int.toNat_natCast]
  ring

theorem quadratic_bigO :
    BigOValid unitModel preFam ((prog 0).strip) postFam (fun n => n ^ 2) :=
  quadratic_theta.toBigO

end QuadraticSum
end Examples
end ResourcesLogic
