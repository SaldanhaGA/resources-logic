import ResourcesLogic.VCG.Classic

namespace ResourcesLogic
namespace Examples
namespace Nested

open Finset

variable (N : Int)

/-- Outer invariant. -/
def inv : Assn := fun σ =>
  σ (.var "n") = N ∧ 0 ≤ σ (.var "i") ∧ σ (.var "i") ≤ N

/-- Inner invariant: it pins the outer counter to the outer iteration index `k`. -/
def innerInv (k : Nat) : Assn := fun σ =>
  σ (.var "n") = N ∧ σ (.var "i") = k ∧ σ (.var "i") < N ∧
  0 ≤ σ (.var "j") ∧ σ (.var "j") ≤ N

def f : State → Nat := fun σ => (σ (.var "i")).toNat

def g : State → Nat := fun σ => (σ (.var "j")).toNat

def inner (k : Nat) : ACom :=
  .«while» (.lt (.var "j") (.var "n")) (innerInv N k) g N.toNat (fun _ => 4) 3
    (.assign "j" (.add (.var "j") (.num 1)))

/-- Outer body, indexed by the outer iteration `k`. -/
def body (k : Nat) : ACom :=
  .seq (.assign "j" (.num 0)) (.seq (inner N k) (.assign "i" (.add (.var "i") (.num 1))))

def innerStmt : Stmt :=
  .while (.lt (.var "j") (.var "n")) (.assign "j" (.add (.var "j") (.num 1)))

def bodyStmt : Stmt :=
  .seq (.assign "j" (.num 0)) (.seq innerStmt (.assign "i" (.add (.var "i") (.num 1))))

def prog : Stmt :=
  .seq (.assign "i" (.num 0)) (.while (.lt (.var "i") (.var "n")) bodyStmt)

def pre : Assn := fun σ => σ (.var "n") = N ∧ 0 ≤ N

def post : Assn := fun σ => σ (.var "i") = N

/-- Cost of one outer iteration: `j := 0`, the inner loop, and `i := i + 1`. -/
def iterCost : Nat := 7 * N.toNat + 9

def cost : Cost := fun _ => 7 * N.toNat ^ 2 + 12 * N.toNat + 5

theorem body_strip (k : Nat) : (body N k).strip = bodyStmt := rfl

theorem body_sigmaFree (k : Nat) : (body N k).SigmaFree :=
  .seq (.assign .num)
    (.seq (.«while» (.lt .var .var) (.assign (.add .var .num))) (.assign (.add .var .num)))

theorem outer_hoare :
    Hoare unitModel (inv N) (.while (.lt (.var "i") (.var "n")) bodyStmt)
      (fun σ => inv N σ ∧ bval (.lt (.var "i") (.var "n")) σ = false)
      (fun _ => (∑ _i ∈ range N.toNat, iterCost N) + (N.toNat + 1) * 3) := by
  apply vcg_while_indexed (f := f) (c := body N) (body_strip N) (body_sigmaFree N)
  · -- one outer iteration: establish the inner invariant and charge `iterCost`
    rintro k σ ⟨hn, hi0, hiN⟩ hb hf
    have hlt : σ (.var "i") < σ (.var "n") := by simpa [bval, aval] using hb
    simp only [f] at hf
    constructor
    · simp only [body, inner, wpc, substA, aval, innerInv]
      simp [State.update, hn]; omega
    · simp [body, inner, wpc, tacost, unitModel, iterCost,
        Finset.sum_const, Finset.card_range]
      ring_nf; omega
  · -- the inner loop's own conditions, for every outer index `k`
    intro k
    and_intros
    · trivial
    · rintro k' σ ⟨hn, hi, hiN, hj0, hjN⟩ hb hf
      have hlt : σ (.var "j") < σ (.var "n") := by simpa [bval, aval] using hb
      simp only [g] at hf
      constructor
      · simp only [wpc, substA, aval, innerInv, g]
        simp [State.update, hn, hi]; omega
      · simp [wpc, tacost, unitModel]
    · rintro σ ⟨hn, hi, hiN, hj0, hjN⟩ hb
      simp only [wpc, substA, aval, inv, f]
      simp [State.update, hn, hi]; omega
    · rintro σ ⟨hn, hi, hiN, hj0, hjN⟩ hb
      have hlt : σ (.var "j") < σ (.var "n") := by simpa [bval, aval] using hb
      simp only [g]; omega
    · intro σ _; simp [tbcost, tacost, unitModel]
    · intro k'; trivial
    · trivial
  · rintro σ ⟨hn, hi0, hiN⟩ hb
    have hlt : σ (.var "i") < σ (.var "n") := by simpa [bval, aval] using hb
    simp only [f]; omega
  · intro σ _; simp [tbcost, tacost, unitModel]

theorem nested_hoare : Hoare unitModel (pre N) (prog) (post N) (cost N) := by
  have hinit : Hoare unitModel (pre N) (.assign "i" (.num 0)) (inv N) (fun _ => 2) := by
    apply Hoare.conseq (Hoare.assign (Q := inv N))
    · rintro σ ⟨hn, hN⟩
      simp only [substA, aval, inv]
      simp [State.update, hn]; omega
    · intro _ h; assumption
    · intro σ _; simp [tacost, unitModel]
  apply Hoare.conseq (Hoare.seq_const hinit (outer_hoare N))
  · intro _ h; assumption
  · rintro σ ⟨⟨hn, hi0, hiN⟩, hb⟩
    have hge : ¬ σ (.var "i") < σ (.var "n") := by simpa [bval, aval] using hb
    simp only [post]; omega
  · intro σ _
    simp only [cost, iterCost, Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring_nf; omega

theorem nested_valid : Valid unitModel (pre N) prog (post N) (cost N) :=
  (nested_hoare N).sound

def preFam (n : ℕ) : Assn := pre (n : Int)

def postFam (n : ℕ) : Assn := post (n : Int)

theorem nested_bigO :
    BigOValid unitModel preFam prog postFam (fun n => n ^ 2) := by
  exists fun n => 7 * n ^ 2 + 12 * n + 5
  constructor
  · apply isBigO_quadratic; norm_num
  intro n
  have h := nested_valid (n : Int)
  have : cost (n : Int) = fun _ : State => 7 * n ^ 2 + 12 * n + 5 := by
    funext σ; simp only [cost, Int.toNat_natCast]
  rw [this] at h
  simpa [preFam, postFam] using h

end Nested
end Examples
end ResourcesLogic
