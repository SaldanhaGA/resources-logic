import ResourcesLogic.VCG.Classic

namespace ResourcesLogic
namespace Examples
namespace Division

open Finset

def body : ACom :=
  .seq (.assign "r" (.sub (.var "r") (.var "m")))
       (.assign "q" (.add (.var "q") (.num 1)))

variable (N : Int)

def I : Assn := fun σ =>
  σ (.var "n") = σ (.var "q") * σ (.var "m") + σ (.var "r") ∧
  σ (.var "m") > 0 ∧ σ (.var "r") ≥ 0 ∧ σ (.var "q") ≥ 0 ∧ σ (.var "n") = N

def f : State → Nat := fun σ => (N - σ (.var "r")).toNat

def prog : ACom :=
  .«while» (.le (.var "m") (.var "r")) (I N) (f N) N.toNat (fun _ => 10) 3 body

def pre : Assn := fun σ =>
  σ (.var "r") = σ (.var "n") ∧ σ (.var "q") = 0 ∧ σ (.var "m") > 0 ∧
  σ (.var "n") = N ∧ N ≥ 0

def post : Assn := fun σ =>
  σ (.var "n") = σ (.var "r") + σ (.var "m") * σ (.var "q") ∧
  σ (.var "r") < σ (.var "m")

theorem prog_strip : (prog N).strip =
    .while (.le (.var "m") (.var "r"))
      (.seq (.assign "r" (.sub (.var "r") (.var "m")))
            (.assign "q" (.add (.var "q") (.num 1)))) := rfl

theorem prog_sigmaFree : (prog N).SigmaFree :=
  ACom.SigmaFree.«while» (.le .var .var)
    (ACom.SigmaFree.seq (.assign (.sub .var .var)) (.assign (.add .var .num)))

theorem vcg_holds :
    VCG unitModel (pre N) (prog N) post (fun _ => 20 * N.toNat + 5) := by
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    rintro σ ⟨hr, hq, hm, hn, hN⟩
    refine ⟨?_, hm, ?_, ?_, hn⟩
    · rw [hq]; simp [hr]
    · rw [hr, hn]; assumption
    · omega
  ·
    rintro k σ ⟨hinv, hm, hr, hq, hn⟩ hb hf
    have hle : σ (.var "m") ≤ σ (.var "r") := by simpa [bval, aval] using hb
    have hqm : 0 ≤ σ (.var "q") * σ (.var "m") := mul_nonneg hq (le_of_lt hm)
    have hmul : (σ (.var "q") + 1) * σ (.var "m")
        = σ (.var "q") * σ (.var "m") + σ (.var "m") := by ring
    have hfk : (N - σ (.var "r")).toNat = k := hf
    constructor
    · simp only [wpc, body, substA, aval]
      simp [State.update, I, f]
      omega
    · simp [wpc, body, tacost, unitModel]
  ·
    rintro σ ⟨hinv, hm, hr, hq, hn⟩ hb
    have hlt : σ (.var "r") < σ (.var "m") := by simpa [bval, aval] using hb
    constructor
    · rw [hinv]; ring
    · assumption
  ·
    rintro σ ⟨hinv, hm, hr, hq, hn⟩ hb
    have hle : σ (.var "m") ≤ σ (.var "r") := by simpa [bval, aval] using hb
    have hqm : 0 ≤ σ (.var "q") * σ (.var "m") := mul_nonneg hq (le_of_lt hm)
    simp only [f]
    omega
  ·
    intro σ _
    simp [tbcost, tacost, unitModel]
  ·
    intro k
    constructor <;> trivial
  ·
    rintro σ ⟨hr, hq, hm, hn, hN⟩
    simp only [prog, wpc, Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega

theorem division_valid :
    Valid unitModel (pre N) ((prog N).strip) post (fun _ => 20 * N.toNat + 5) :=
  vcg_valid (prog_sigmaFree N) (vcg_holds N)

theorem division_hoare :
    Hoare unitModel (pre N) ((prog N).strip) post (fun _ => 20 * N.toNat + 5) :=
  vcg_sound (prog_sigmaFree N) (vcg_holds N)

def preFam (n : ℕ) : Assn := pre (n : Int)

def postFam (_ : ℕ) : Assn := post

theorem division_bigO :
    BigOValid unitModel preFam ((prog 0).strip) postFam (fun n => n) := by
  refine ⟨fun n => 20 * n + 5, isBigO_linear (by norm_num), fun n => ?_⟩
  have h := division_valid (n : Int)
  rw [prog_strip] at h ⊢
  simpa [preFam, postFam, Int.toNat_natCast] using h

end Division
end Examples
end ResourcesLogic
