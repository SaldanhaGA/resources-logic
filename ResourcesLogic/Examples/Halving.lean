import ResourcesLogic.VCG.Classic

namespace ResourcesLogic
namespace Examples
namespace Halving

variable (N : Int)

def inv : Assn := fun σ => 0 ≤ σ (.var "m") ∧ σ (.var "m") ≤ N ∧ 0 ≤ N

def f : State → Nat := fun σ => Nat.log 2 N.toNat - Nat.log 2 (σ (.var "m")).toNat

def prog : ACom :=
  .«while» (.gt (.var "m") (.num 1)) (inv N) (f N) (Nat.log 2 N.toNat) (fun _ => 4) 3
    (.assign "m" (.div (.var "m") (.num 2)))

def pre : Assn := fun σ => σ (.var "m") = N ∧ 0 ≤ N

def post : Assn := fun σ => σ (.var "m") ≤ 1

def cost : Cost := fun _ => 7 * Nat.log 2 N.toNat + 5

theorem prog_strip : (prog N).strip =
    .while (.gt (.var "m") (.num 1))
      (.assign "m" (.div (.var "m") (.num 2))) := rfl

theorem prog_sigmaFree : (prog N).SigmaFree :=
  ACom.SigmaFree.«while» (.gt .var .num) (.assign (.div .var .num))

theorem vcg_holds :
    VCG unitModel (pre N) (prog N) post (cost N) := by
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    rintro σ ⟨hm, hN⟩
    refine ⟨?_, ?_, ?_⟩ <;> omega
  ·
    rintro k σ ⟨hm0, hmN, hN⟩ hb hf
    have hgt : (1 : Int) < σ (.var "m") := by simpa [bval, aval] using hb
    have h2 : 2 ≤ (σ (.var "m")).toNat := by omega
    have hle : (σ (.var "m")).toNat ≤ N.toNat := by omega
    have hlogpos : 1 ≤ Nat.log 2 (σ (.var "m")).toNat := Nat.log_pos (by norm_num) h2
    have hlogmono : Nat.log 2 (σ (.var "m")).toNat ≤ Nat.log 2 N.toNat :=
      Nat.log_mono_right hle
    have hdiv : (σ (.var "m") / 2).toNat = (σ (.var "m")).toNat / 2 := by omega
    have hlogdiv : Nat.log 2 ((σ (.var "m")).toNat / 2)
        = Nat.log 2 (σ (.var "m")).toNat - 1 := Nat.log_div_base 2 _
    simp only [f] at hf
    constructor
    ·
      simp only [wpc, substA, aval, inv, f, State.update_same]
      refine ⟨⟨by omega, by omega, hN⟩, ?_⟩
      rw [hdiv, hlogdiv]
      omega
    ·
      simp [wpc, tacost, unitModel]
  ·
    rintro σ ⟨hm0, hmN, hN⟩ hb
    have : ¬ (1 : Int) < σ (.var "m") := by simpa [bval, aval] using hb
    simp only [post]; omega
  ·
    rintro σ ⟨hm0, hmN, hN⟩ hb
    have hgt : (1 : Int) < σ (.var "m") := by simpa [bval, aval] using hb
    have h2 : 2 ≤ (σ (.var "m")).toNat := by omega
    have hle : (σ (.var "m")).toNat ≤ N.toNat := by omega
    have hlogpos : 1 ≤ Nat.log 2 (σ (.var "m")).toNat := Nat.log_pos (by norm_num) h2
    have hlogmono : Nat.log 2 (σ (.var "m")).toNat ≤ Nat.log 2 N.toNat :=
      Nat.log_mono_right hle
    have hNpos : 1 ≤ Nat.log 2 N.toNat := le_trans hlogpos hlogmono
    simp only [f]
    omega
  ·
    intro σ _
    simp [tbcost, tacost, unitModel]
  ·
    intro k
    trivial
  ·
    rintro σ ⟨hm, hN⟩
    simp only [prog, wpc, cost, Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega

theorem halving_valid :
    Valid unitModel (pre N) ((prog N).strip) post (cost N) :=
  vcg_valid (prog_sigmaFree N) (vcg_holds N)

theorem halving_hoare :
    Hoare unitModel (pre N) ((prog N).strip) post (cost N) :=
  vcg_sound (prog_sigmaFree N) (vcg_holds N)

def preFam (n : ℕ) : Assn := pre (n : Int)

def postFam (_ : ℕ) : Assn := post

theorem halving_bigO :
    BigOValid unitModel preFam ((prog 0).strip) postFam (fun n => Nat.log 2 n) := by
  refine ⟨fun n => 7 * Nat.log 2 n + 5, isBigO_log (by norm_num), fun n => ?_⟩
  have h := halving_valid (n : Int)
  rw [prog_strip] at h ⊢
  have : cost (n : Int) = fun _ : State => 7 * Nat.log 2 n + 5 := by
    funext σ; simp only [cost, Int.toNat_natCast]
  rw [this] at h
  simpa [preFam, postFam] using h

end Halving
end Examples
end ResourcesLogic
