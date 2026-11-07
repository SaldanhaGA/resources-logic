import ResourcesLogic.VCG.Classic

namespace ResourcesLogic
namespace Examples
namespace Sequential

variable (N : Int)

def inv₁ : Assn := fun σ =>
  σ (.var "n") = N ∧ 0 ≤ σ (.var "i") ∧ σ (.var "i") ≤ N

def inv₂ : Assn := fun σ =>
  σ (.var "n") = N ∧ σ (.var "i") = N ∧ 0 ≤ σ (.var "j") ∧ σ (.var "j") ≤ N

def f₁ : State → Nat := fun σ => (σ (.var "i")).toNat

def f₂ : State → Nat := fun σ => (σ (.var "j")).toNat

def loop₁ : ACom :=
  .«while» (.lt (.var "i") (.var "n")) (inv₁ N) f₁ N.toNat (fun _ => 4) 3
    (.assign "i" (.add (.var "i") (.num 1)))

def loop₂ : ACom :=
  .«while» (.lt (.var "j") (.var "n")) (inv₂ N) f₂ N.toNat (fun _ => 4) 3
    (.assign "j" (.add (.var "j") (.num 1)))

def prog : ACom :=
  .seq (.assign "i" (.num 0))
    (.seq (loop₁ N) (.seq (.assign "j" (.num 0)) (loop₂ N)))

def pre : Assn := fun σ => σ (.var "n") = N ∧ 0 ≤ N

def post : Assn := fun σ => σ (.var "i") = N ∧ σ (.var "j") = N

def cost : Cost := fun _ => 14 * N.toNat + 10

theorem prog_strip : (prog N).strip =
    .seq (.assign "i" (.num 0))
      (.seq (.while (.lt (.var "i") (.var "n")) (.assign "i" (.add (.var "i") (.num 1))))
        (.seq (.assign "j" (.num 0))
          (.while (.lt (.var "j") (.var "n")) (.assign "j" (.add (.var "j") (.num 1)))))) :=
  rfl

theorem prog_sigmaFree : (prog N).SigmaFree :=
  .seq (.assign .num)
    (.seq (.«while» (.lt .var .var) (.assign (.add .var .num)))
      (.seq (.assign .num) (.«while» (.lt .var .var) (.assign (.add .var .num)))))

theorem vcg_holds : VCG unitModel (pre N) (prog N) (post N) (cost N) := by
  unfold VCG
  and_intros
  · -- precondition entails the first invariant after `i := 0`
    rintro σ ⟨hn, hN⟩
    simp only [prog, loop₁, wpc, substA, aval, inv₁]
    simp [State.update, hn]; omega
  · trivial
  · -- body of the first loop
    rintro k σ ⟨hn, hi0, hiN⟩ hb hf
    have hlt : σ (.var "i") < σ (.var "n") := by simpa [bval, aval] using hb
    simp only [f₁] at hf
    constructor
    · simp only [wpc, substA, aval, inv₁, f₁]
      simp [State.update, hn]; omega
    · simp [wpc, tacost, unitModel]
  · -- exit of the first loop establishes the second invariant after `j := 0`
    rintro σ ⟨hn, hi0, hiN⟩ hb
    have hge : ¬ σ (.var "i") < σ (.var "n") := by simpa [bval, aval] using hb
    simp only [loop₂, wpc, substA, aval, inv₂]
    simp [State.update, hn]; omega
  · rintro σ ⟨hn, hi0, hiN⟩ hb
    have hlt : σ (.var "i") < σ (.var "n") := by simpa [bval, aval] using hb
    simp only [f₁]; omega
  · intro σ _; simp [tbcost, tacost, unitModel]
  · intro k; trivial
  · trivial
  · -- body of the second loop
    rintro k σ ⟨hn, hi, hj0, hjN⟩ hb hf
    have hlt : σ (.var "j") < σ (.var "n") := by simpa [bval, aval] using hb
    simp only [f₂] at hf
    constructor
    · simp only [wpc, substA, aval, inv₂, f₂]
      simp [State.update, hn, hi]; omega
    · simp [wpc, tacost, unitModel]
  · rintro σ ⟨hn, hi, hj0, hjN⟩ hb
    have hge : ¬ σ (.var "j") < σ (.var "n") := by simpa [bval, aval] using hb
    constructor
    · assumption
    · omega
  · rintro σ ⟨hn, hi, hj0, hjN⟩ hb
    have hlt : σ (.var "j") < σ (.var "n") := by simpa [bval, aval] using hb
    simp only [f₂]; omega
  · intro σ _; simp [tbcost, tacost, unitModel]
  · intro k; trivial
  · -- the two loop costs add up
    rintro σ ⟨hn, hN⟩
    simp only [prog, loop₁, loop₂, wpc, cost, tacost, unitModel,
      Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega

theorem sequential_valid :
    Valid unitModel (pre N) ((prog N).strip) (post N) (cost N) :=
  vcg_valid (prog_sigmaFree N) (vcg_holds N)

def preFam (n : ℕ) : Assn := pre (n : Int)

def postFam (n : ℕ) : Assn := post (n : Int)

theorem sequential_bigO :
    BigOValid unitModel preFam ((prog 0).strip) postFam (fun n => n) := by
  exists fun n => 14 * n + 10
  constructor
  · apply isBigO_linear; norm_num
  intro n
  have h := sequential_valid (n : Int)
  rw [prog_strip] at h ⊢
  have : cost (n : Int) = fun _ : State => 14 * n + 10 := by
    funext σ; simp only [cost, Int.toNat_natCast]
  rw [this] at h
  simpa [preFam, postFam] using h

end Sequential
end Examples
end ResourcesLogic
