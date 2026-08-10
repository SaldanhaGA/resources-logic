import ResourcesLogic.VCG.Exact

namespace ResourcesLogic
namespace Examples
namespace RangeFilter

def cond : BExp :=
  .and (.le (.var "l") (.arr "a" (.var "i"))) (.le (.arr "a" (.var "i")) (.var "u"))

def body : AComE :=
  .ite cond
    (.seq (.arrAssign "b" (.var "j") (.arr "a" (.var "i")))
          (.assign "j" (.add (.var "j") (.num 1))))
    (.seq (.arrAssign "b" (.var "j") (.arr "b" (.var "j")))
          (.assign "j" (.add (.var "j") (.num 0))))

variable (N : Int)

def inv : Assn := fun σ => σ (.var "n") = N ∧ 0 ≤ σ (.var "i") ∧ 0 ≤ N

def prog : AComE :=
  .seq (.assign "j" (.num 0))
    (.«for» "i" (.num 0) (.var "n") (inv N) 17 3 body)

def pre : Assn := fun σ => σ (.var "n") = N ∧ 0 ≤ N

def post : Assn := fun σ => σ (.var "i") = σ (.var "n") ∧ σ (.var "n") = N

def cost : Cost := fun σ => 24 * (σ (.var "n")).toNat + 7

theorem prog_strip : (prog N).strip =
    .seq (.assign "j" (.num 0))
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
    · refine ⟨⟨fun _ => ?_, fun _ => ?_⟩, ?_⟩
      · refine ⟨⟨?_, ?_, hN⟩, ?_, ?_, ?_⟩ <;>
          simp [substA, substArr, aval, State.update, inv, hn, hik] <;> omega
      · refine ⟨⟨?_, ?_, hN⟩, ?_, ?_, ?_⟩ <;>
          simp [substA, substArr, aval, State.update, inv, hn, hik] <;> omega
      · simp [wpcE, body, cond, tacost, tbcost, unitModel]
    · simp [wpcE, body, cond, tacost, tbcost, unitModel]
  ·
    rintro σ ⟨hn, hi, hN⟩ hexit
    constructor
    · simpa [aval] using hexit
    · assumption
  ·
    intro k av bv
    refine ⟨⟨trivial, trivial, fun _ => trivial, fun σ₀ _ => ?_⟩,
            ⟨trivial, trivial, fun _ => trivial, fun σ₀ _ => ?_⟩⟩ <;>
      simp [wpcE, substA, substArr, aval, State.update, tacost]
  ·
    intro σ₀
    trivial
  ·
    intro σ₀ _
    simp [wpcE, substA, aval, State.update, tacost]
  ·
    rintro σ ⟨hn, hN⟩
    simp only [prog, wpcE, cost, aval, tacost, unitModel, incCost]
    omega

theorem rangeFilter_exact :
    ValidExact unitModel (pre N) ((prog N).strip) (post N) cost :=
  vcgE_valid (vcg_holds N)

theorem rangeFilter_hoareE :
    HoareE unitModel (pre N) ((prog N).strip) (post N) cost :=
  vcgE_sound (vcg_holds N)

def preFam (n : ℕ) : Assn := pre (n : Int)

def postFam (n : ℕ) : Assn := post (n : Int)

theorem rangeFilter_theta :
    ThetaExactValid unitModel preFam ((prog 0).strip) postFam (fun n => n) := by
  refine ⟨fun n => 24 * n + 7, isBigTheta_linear (by norm_num), fun n => ?_⟩
  have h := rangeFilter_exact (n : Int)
  rw [prog_strip] at h ⊢
  refine h.cost_congr ?_
  intro σ hσ
  obtain ⟨hn, -⟩ := hσ
  simp only [cost]
  rw [hn, Int.toNat_natCast]

theorem rangeFilter_bigO :
    BigOValid unitModel preFam ((prog 0).strip) postFam (fun n => n) :=
  rangeFilter_theta.toBigO

end RangeFilter
end Examples
end ResourcesLogic
