import ResourcesLogic.VCG.Classic

namespace ResourcesLogic
namespace Examples
namespace NLogN

open Finset

variable (N : Int)

/-- Outer invariant. -/
def inv : Assn := fun σ =>
  σ (.var "n") = N ∧ 0 ≤ σ (.var "i") ∧ σ (.var "i") ≤ N

/-- Invariant of the inner halving loop, pinning the outer counter to `k`. -/
def innerInv (k : Nat) : Assn := fun σ =>
  σ (.var "n") = N ∧ σ (.var "i") = k ∧ σ (.var "i") < N ∧
  0 ≤ σ (.var "m") ∧ σ (.var "m") ≤ N

def f : State → Nat := fun σ => (σ (.var "i")).toNat

def g : State → Nat := fun σ => Nat.log 2 N.toNat - Nat.log 2 (σ (.var "m")).toNat

def inner (k : Nat) : ACom :=
  .«while» (.gt (.var "m") (.num 1)) (innerInv N k) (g N) (Nat.log 2 N.toNat)
    (fun _ => 4) 3 (.assign "m" (.div (.var "m") (.num 2)))

/-- Outer body, indexed by the outer iteration `k`. -/
def body (k : Nat) : ACom :=
  .seq (.assign "m" (.var "n")) (.seq (inner N k) (.assign "i" (.add (.var "i") (.num 1))))

def innerStmt : Stmt :=
  .while (.gt (.var "m") (.num 1)) (.assign "m" (.div (.var "m") (.num 2)))

def bodyStmt : Stmt :=
  .seq (.assign "m" (.var "n")) (.seq innerStmt (.assign "i" (.add (.var "i") (.num 1))))

def prog : Stmt :=
  .seq (.assign "i" (.num 0)) (.while (.lt (.var "i") (.var "n")) bodyStmt)

def pre : Assn := fun σ => σ (.var "n") = N ∧ 0 ≤ N

def post : Assn := fun σ => σ (.var "i") = N

/-- Cost of one outer iteration: `m := n`, the halving loop, and `i := i + 1`. -/
def iterCost : Nat := 7 * Nat.log 2 N.toNat + 9

def cost : Cost := fun _ =>
  7 * (N.toNat * Nat.log 2 N.toNat) + 12 * N.toNat + 5

theorem body_strip (k : Nat) : (body N k).strip = bodyStmt := rfl

theorem body_sigmaFree (k : Nat) : (body N k).SigmaFree :=
  .seq (.assign .var)
    (.seq (.«while» (.gt .var .num) (.assign (.div .var .num))) (.assign (.add .var .num)))

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
  · -- the halving loop's own conditions, for every outer index `k`
    intro k
    and_intros
    · trivial
    · rintro k' σ ⟨hn, hi, hiN, hm0, hmN⟩ hb hf
      have hgt : (1 : Int) < σ (.var "m") := by simpa [bval, aval] using hb
      have h2 : 2 ≤ (σ (.var "m")).toNat := by omega
      have hle : (σ (.var "m")).toNat ≤ N.toNat := by omega
      have hlogpos : 1 ≤ Nat.log 2 (σ (.var "m")).toNat := Nat.log_pos (by norm_num) h2
      have hlogmono : Nat.log 2 (σ (.var "m")).toNat ≤ Nat.log 2 N.toNat :=
        Nat.log_mono_right hle
      have hdiv : (σ (.var "m") / 2).toNat = (σ (.var "m")).toNat / 2 := by omega
      have hlogdiv : Nat.log 2 ((σ (.var "m")).toNat / 2)
          = Nat.log 2 (σ (.var "m")).toNat - 1 := Nat.log_div_base 2 _
      simp only [g] at hf
      constructor
      · simp only [wpc, substA, aval, innerInv, g]
        simp only [State.update, hn, hi]
        simp
        constructor
        · omega
        · rw [hdiv, hlogdiv]; omega
      · simp [wpc, tacost, unitModel]
    · rintro σ ⟨hn, hi, hiN, hm0, hmN⟩ hb
      simp only [wpc, substA, aval, inv, f]
      simp [State.update, hn, hi]; omega
    · rintro σ ⟨hn, hi, hiN, hm0, hmN⟩ hb
      have hgt : (1 : Int) < σ (.var "m") := by simpa [bval, aval] using hb
      have h2 : 2 ≤ (σ (.var "m")).toNat := by omega
      have hle : (σ (.var "m")).toNat ≤ N.toNat := by omega
      have hlogpos : 1 ≤ Nat.log 2 (σ (.var "m")).toNat := Nat.log_pos (by norm_num) h2
      have hlogmono : Nat.log 2 (σ (.var "m")).toNat ≤ Nat.log 2 N.toNat :=
        Nat.log_mono_right hle
      have hNpos : 1 ≤ Nat.log 2 N.toNat := le_trans hlogpos hlogmono
      simp only [g]; omega
    · intro σ _; simp [tbcost, tacost, unitModel]
    · intro k'; trivial
    · trivial
  · rintro σ ⟨hn, hi0, hiN⟩ hb
    have hlt : σ (.var "i") < σ (.var "n") := by simpa [bval, aval] using hb
    simp only [f]; omega
  · intro σ _; simp [tbcost, tacost, unitModel]

theorem nlogn_hoare : Hoare unitModel (pre N) prog (post N) (cost N) := by
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

theorem nlogn_valid : Valid unitModel (pre N) prog (post N) (cost N) :=
  (nlogn_hoare N).sound

def preFam (n : ℕ) : Assn := pre (n : Int)

def postFam (n : ℕ) : Assn := post (n : Int)

theorem nlogn_bigO :
    BigOValid unitModel preFam prog postFam (fun n => n * Nat.log 2 n) := by
  exists fun n => 7 * (n * Nat.log 2 n) + 12 * n + 5
  constructor
  · apply isBigO_nlog; norm_num
  intro n
  have h := nlogn_valid (n : Int)
  have : cost (n : Int) = fun _ : State => 7 * (n * Nat.log 2 n) + 12 * n + 5 := by
    funext σ; simp only [cost, Int.toNat_natCast]
  rw [this] at h
  simpa [preFam, postFam] using h

end NLogN
end Examples
end ResourcesLogic
