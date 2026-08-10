import ResourcesLogic.Hoare.Completeness

namespace ResourcesLogic

variable {C : CostModel}

def incCost (C : CostModel) : Nat := C.var + C.cst + C.add + C.assignV

theorem tacost_inc (C : CostModel) (i : Ident) (σ : State) :
    tacost C (.add (.var i) (.num 1)) σ + C.assignV = incCost C := by
  simp [tacost, incCost]

inductive HoareE (C : CostModel) : Assn → Stmt → Assn → Cost → Prop where
  | skip {P} : HoareE C P .skip P (fun _ => C.skip)
  | assign {Q x a} :
      HoareE C (substA Q x a) (.assign x a) Q (fun σ => tacost C a σ + C.assignV)
  | arrAssign {Q x a₁ a₂} :
      HoareE C (substArr Q x a₁ a₂) (.arrAssign x a₁ a₂) Q
        (fun σ => tacost C a₁ σ + tacost C a₂ σ + C.assignA)
  | seq {P Q R S₁ S₂ T₁ T₂} (n : Nat)
      (h₁ : HoareE C P S₁ (fun σ => Q σ ∧ T₂ σ = n) T₁)
      (h₂ : HoareE C Q S₂ R T₂) :
      HoareE C P (.seq S₁ S₂) R (fun σ => T₁ σ + n)

  | ite {P Q b S₁ S₂ T}
      (h₁ : HoareE C (fun σ => P σ ∧ bval b σ = true) S₁ Q T)
      (h₂ : HoareE C (fun σ => P σ ∧ bval b σ = false) S₂ Q T) :
      HoareE C P (.ite b S₁ S₂) Q (fun σ => T σ + tbcost C b σ)

  | «for» {P : Assn} {i : Ident} {a bE : AExp} {S : Stmt} {ts cb : Nat}
      (hai : ∀ σ v, aval a (σ[Loc.var i ↦ v]) = aval a σ)
      (hbi : ∀ σ v, aval bE (σ[Loc.var i ↦ v]) = aval bE σ)
      (hcb : ∀ σ, tbcost C (.lt (.var i) bE) σ = cb)
      (hle : ∀ σ, substA P i a σ → aval a σ ≤ aval bE σ)
      (hbody : ∀ k av bv : Int,
        HoareE C
          (fun σ => P σ ∧ σ (Loc.var i) = k ∧ aval a σ = av ∧ aval bE σ = bv ∧
                    av ≤ k ∧ k < bv)
          S
          (fun σ' => substA P i (.add (.var i) (.num 1)) σ' ∧ σ' (Loc.var i) = k ∧
                     aval a σ' = av ∧ aval bE σ' = bv)
          (fun _ => ts)) :
      HoareE C (substA P i a) (Stmt.for i a bE S)
        (fun σ => P σ ∧ σ (Loc.var i) = aval bE σ)
        (fun σ => (tacost C a σ + C.assignV) +
          (aval bE σ - aval a σ).toNat * (cb + ts + incCost C) + cb)
  | conseq {P P' Q Q' S T T'}
      (h : HoareE C P' S Q' T')
      (hP : ∀ σ, P σ → P' σ) (hQ : ∀ σ, Q' σ → Q σ) (hT : ∀ σ, P σ → T' σ = T σ) :
      HoareE C P S Q T
  | exists_pre {ι : Type} {P : ι → Assn} {S Q T}
      (h : ∀ i, HoareE C (P i) S Q T) :
      HoareE C (fun σ => ∃ i, P i σ) S Q T

  | conj {P S Q₁ Q₂ T}
      (h₁ : HoareE C P S Q₁ T) (h₂ : HoareE C P S Q₂ T) :
      HoareE C P S (fun σ => Q₁ σ ∧ Q₂ σ) T

inductive Stmt.LoopFree : Stmt → Prop where
  | skip : Stmt.LoopFree .skip
  | assign {x : Ident} {a : AExp} : Stmt.LoopFree (.assign x a)
  | arrAssign {x : Ident} {a₁ a₂ : AExp} : Stmt.LoopFree (.arrAssign x a₁ a₂)
  | seq {S₁ S₂ : Stmt} : Stmt.LoopFree S₁ → Stmt.LoopFree S₂ → Stmt.LoopFree (.seq S₁ S₂)
  | ite {S₁ S₂ : Stmt} {b : BExp} :
      Stmt.LoopFree S₁ → Stmt.LoopFree S₂ → Stmt.LoopFree (.ite b S₁ S₂)

namespace HoareE

theorem false_pre {S Q T} : HoareE C (fun _ => False) S Q T := by
  have h : HoareE C (fun σ => ∃ _ : Empty, (False : Prop)) S Q T :=
    HoareE.exists_pre (P := fun (_ : Empty) _ => False) (fun i => i.elim)
  apply HoareE.conseq <;> first | assumption | (intro σ h; aesop)

theorem strengthen {P P' S Q T} (h : HoareE C P' S Q T) (hP : ∀ σ, P σ → P' σ) :
    HoareE C P S Q T :=
  HoareE.conseq h hP (fun _ hq => hq) (fun _ _ => rfl)

theorem of_pointwise {P S Q T}
    (h : ∀ σ₀, P σ₀ → HoareE C (fun σ => σ = σ₀) S Q T) : HoareE C P S Q T := by
  have key : ∀ σ₀ : State, HoareE C (fun σ => σ = σ₀ ∧ P σ₀) S Q T := by
    intro σ₀
    by_cases hp : P σ₀
    · have hh := h σ₀ hp
      apply strengthen <;> first | assumption | (intro σ hσ; aesop)
    · apply strengthen <;> first | assumption | apply false_pre | (intro σ hσ; aesop)
  have hep := HoareE.exists_pre (ι := State) key
  apply HoareE.conseq <;>
    first | assumption | (intro σ hP; exists σ) | (intro σ h; aesop)

theorem valid_for_loop {P : Assn} {i : Ident} {a bE : AExp} {S : Stmt} {ts cb : Nat}
    (hbi : ∀ σ v, aval bE (σ[Loc.var i ↦ v]) = aval bE σ)
    (hcb : ∀ σ, tbcost C (.lt (.var i) bE) σ = cb)
    (hbody : ∀ k av bv : Int,
      ValidExact C
        (fun σ => P σ ∧ σ (Loc.var i) = k ∧ aval a σ = av ∧ aval bE σ = bv ∧ av ≤ k ∧ k < bv)
        S
        (fun σ' => substA P i (.add (.var i) (.num 1)) σ' ∧ σ' (Loc.var i) = k ∧
                   aval a σ' = av ∧ aval bE σ' = bv)
        (fun _ => ts))
    (hai : ∀ σ v, aval a (σ[Loc.var i ↦ v]) = aval a σ) :
    ∀ (n : Nat) (σ : State) (av bv k : Int),
      P σ → σ (Loc.var i) = k → aval a σ = av → aval bE σ = bv →
      av ≤ k → k ≤ bv → (bv - k).toNat = n →
      ∃ σ', Eval C
        (.while (.lt (.var i) bE) (.seq S (.assign i (.add (.var i) (.num 1))))) σ
        (n * (cb + ts + incCost C) + cb) σ' ∧ P σ' ∧ σ' (Loc.var i) = bv ∧
        aval bE σ' = bv := by
  intro n
  induction n with
  | zero =>
      intro σ av bv k hP hi ha hb hav hkb hn
      have hk : k = bv := by omega
      have hcond : bval (.lt (.var i) bE) σ = false := by
        simp [bval, aval, hi, hb, hk]
      refine ⟨σ, ?_, hP, by rw [hi, hk], hb⟩
      have := Eval.whileF (C := C)
        (b := (.lt (.var i) bE)) (S := .seq S (.assign i (.add (.var i) (.num 1)))) hcond
      rw [hcb σ] at this
      simpa using this
  | succ n ih =>
      intro σ av bv k hP hi ha hb hav hkb hn
      have hklt : k < bv := by omega
      have hcond : bval (.lt (.var i) bE) σ = true := by
        simp [bval, aval, hi, hb, hklt]

      obtain ⟨σ₁, hev₁, hP₁, hi₁, ha₁, hb₁⟩ :=
        hbody k av bv σ ⟨hP, hi, ha, hb, hav, hklt⟩

      set σ₂ : State := σ₁[Loc.var i ↦ aval (.add (.var i) (.num 1)) σ₁] with hσ₂
      have hincEv : Eval C (.assign i (.add (.var i) (.num 1))) σ₁
          (tacost C (.add (.var i) (.num 1)) σ₁ + C.assignV) σ₂ := Eval.assign
      have hival : aval (.add (.var i) (.num 1)) σ₁ = k + 1 := by
        simp [aval, hi₁]
      have hP₂ : P σ₂ := by
        have := hP₁
        simpa [substA, hσ₂] using this
      have hi₂ : σ₂ (Loc.var i) = k + 1 := by
        rw [hσ₂, State.update_same, hival]
      have ha₂ : aval a σ₂ = av := by rw [hσ₂, hai, ha₁]
      have hb₂ : aval bE σ₂ = bv := by rw [hσ₂, hbi, hb₁]
      obtain ⟨σ', hev', hP', hi', hb'⟩ :=
        ih σ₂ av bv (k + 1) hP₂ hi₂ ha₂ hb₂ (by omega) (by omega) (by omega)
      refine ⟨σ', ?_, hP', hi', hb'⟩
      have hbodyEv : Eval C (.seq S (.assign i (.add (.var i) (.num 1)))) σ
          (ts + incCost C) σ₂ := by
        have := Eval.seq hev₁ hincEv
        rwa [tacost_inc C i σ₁] at this
      have hloop := Eval.whileT hcond hbodyEv hev'
      rw [hcb σ] at hloop
      have harith : cb + (ts + incCost C) + (n * (cb + ts + incCost C) + cb)
          = (n + 1) * (cb + ts + incCost C) + cb := by ring
      rwa [harith] at hloop

theorem sound {P S Q T} (h : HoareE C P S Q T) : ValidExact C P S Q T := by
  induction h with
  | skip => intro σ hP; exists σ; refine ⟨Eval.skip, hP⟩
  | @assign Q x a =>
      intro σ hP
      exists σ[Loc.var x ↦ aval a σ]
      refine ⟨Eval.assign, hP⟩
  | @arrAssign Q x a₁ a₂ =>
      intro σ hP
      exists σ[Loc.arr x (aval a₁ σ) ↦ aval a₂ σ]
      refine ⟨Eval.arrAssign, hP⟩
  | @seq P Q R S₁ S₂ T₁ T₂ n _ _ ih₁ ih₂ =>
      intro σ hP
      obtain ⟨σ₁, hev₁, hQ, hcost⟩ := ih₁ σ hP
      obtain ⟨σ₂, hev₂, hR⟩ := ih₂ σ₁ hQ
      refine ⟨σ₂, ?_, hR⟩
      have := Eval.seq hev₁ hev₂
      rwa [hcost] at this
  | @ite P Q b S₁ S₂ T _ _ ih₁ ih₂ =>
      intro σ hP
      cases hb : bval b σ with
      | true =>
          obtain ⟨σ', hev, hQ⟩ := ih₁ σ ⟨hP, hb⟩
          refine ⟨σ', ?_, hQ⟩
          have hstep := Eval.iteT (S₂ := S₂) hb hev
          show Eval C (.ite b S₁ S₂) σ (T σ + tbcost C b σ) σ'
          rwa [Nat.add_comm] at hstep
      | false =>
          obtain ⟨σ', hev, hQ⟩ := ih₂ σ ⟨hP, hb⟩
          refine ⟨σ', ?_, hQ⟩
          have hstep := Eval.iteF (S₁ := S₁) hb hev
          show Eval C (.ite b S₁ S₂) σ (T σ + tbcost C b σ) σ'
          rwa [Nat.add_comm] at hstep
  | @«for» P i a bE S ts cb hai hbi hcb hle _ ihbody =>
      intro σ hPre
      set σ₀ : State := σ[Loc.var i ↦ aval a σ] with hσ₀
      have hev₀ : Eval C (.assign i a) σ (tacost C a σ + C.assignV) σ₀ := Eval.assign
      have hP₀ : P σ₀ := hPre
      have hi₀ : σ₀ (Loc.var i) = aval a σ := by rw [hσ₀, State.update_same]
      have ha₀ : aval a σ₀ = aval a σ := by rw [hσ₀, hai]
      have hb₀ : aval bE σ₀ = aval bE σ := by rw [hσ₀, hbi]
      have hlev : aval a σ ≤ aval bE σ := hle σ hPre
      obtain ⟨σ', hloop, hP', hi', hb'⟩ :=
        valid_for_loop (C := C) (P := P) (i := i) (a := a) (bE := bE) (S := S)
          (ts := ts) (cb := cb) hbi hcb ihbody hai
          ((aval bE σ - aval a σ).toNat) σ₀ (aval a σ) (aval bE σ) (aval a σ)
          hP₀ hi₀ ha₀ hb₀ (le_refl _) hlev rfl
      refine ⟨σ', ?_, hP', by rw [hi', hb']⟩
      have hseq := Eval.seq hev₀ hloop
      have harith :
          tacost C a σ + C.assignV +
              ((aval bE σ - aval a σ).toNat * (cb + ts + incCost C) + cb)
            = tacost C a σ + C.assignV +
              (aval bE σ - aval a σ).toNat * (cb + ts + incCost C) + cb := by ring
      rwa [harith] at hseq
  | conseq _ hP hQ hT ih =>
      intro σ hp
      obtain ⟨σ', hev, hq⟩ := ih σ (hP σ hp)
      refine ⟨σ', ?_, hQ σ' hq⟩
      rwa [hT σ hp] at hev
  | exists_pre _ ih =>
      intro σ hp
      obtain ⟨i, hi⟩ := hp
      apply ih <;> assumption
  | conj _ _ ih₁ ih₂ =>
      intro σ hp
      obtain ⟨σ₁, hev₁, hQ₁⟩ := ih₁ σ hp
      obtain ⟨σ₂, hev₂, hQ₂⟩ := ih₂ σ hp
      obtain ⟨_, rfl⟩ := Eval.deterministic hev₁ hev₂
      exists σ₁

theorem complete_singleton {S : Stmt} (hlf : S.LoopFree) :
    ∀ (Q : Assn) (σ₀ σ' : State) (t : Nat), Eval C S σ₀ t σ' → Q σ' →
      HoareE C (fun σ => σ = σ₀) S Q (fun _ => t) := by
  induction hlf with
  | skip =>
      intro Q σ₀ σ' t hev hQ
      cases hev
      refine HoareE.conseq HoareE.skip (fun σ hσ => ?_) (fun _ h => h) (fun _ _ => rfl)
      subst hσ; assumption
  | assign =>
      intro Q σ₀ σ' t hev hQ
      cases hev
      refine HoareE.conseq HoareE.assign (fun σ hσ => ?_) (fun _ h => h) (fun σ hσ => ?_)
      · subst hσ; assumption
      · subst hσ; rfl
  | arrAssign =>
      intro Q σ₀ σ' t hev hQ
      cases hev
      refine HoareE.conseq HoareE.arrAssign (fun σ hσ => ?_) (fun _ h => h) (fun σ hσ => ?_)
      · subst hσ; assumption
      · subst hσ; rfl
  | seq _ _ ih₁ ih₂ =>
      intro Q σ₀ σ' t hev hQ
      cases hev with
      | @seq _ σ₁ _ _ _ t₁ t₂ hev₁ hev₂ =>
          have h₂ := ih₂ Q σ₁ σ' t₂ hev₂ hQ
          have h₁ := ih₁ (fun σ => (σ = σ₁) ∧ (fun _ : State => t₂) σ = t₂) σ₀ σ₁ t₁ hev₁
            ⟨rfl, rfl⟩
          refine HoareE.seq t₂ h₁ h₂
  | @ite S₁ S₂ b _ _ ih₁ ih₂ =>
      intro Q σ₀ σ' t hev hQ
      cases hev with
      | @iteT _ _ _ _ _ t₀ hb hev' =>
          have h₁ : HoareE C (fun σ => (σ = σ₀) ∧ bval b σ = true) S₁ Q (fun _ => t₀) :=
            HoareE.strengthen (ih₁ Q σ₀ σ' t₀ hev' hQ) (fun σ hσ => by rcases hσ with ⟨h, _⟩; assumption)
          have h₂ : HoareE C (fun σ => (σ = σ₀) ∧ bval b σ = false) S₂ Q (fun _ => t₀) :=
            HoareE.strengthen HoareE.false_pre (fun σ hσ => by
              obtain ⟨rfl, hf⟩ := hσ
              simp_all)
          refine HoareE.conseq (HoareE.ite h₁ h₂) (fun _ h => h) (fun _ h => h)
            (fun σ hσ => ?_)
          subst hσ
          show t₀ + tbcost C b σ = tbcost C b σ + t₀
          omega
      | @iteF _ _ _ _ _ t₀ hb hev' =>
          have h₁ : HoareE C (fun σ => (σ = σ₀) ∧ bval b σ = true) S₁ Q (fun _ => t₀) :=
            HoareE.strengthen HoareE.false_pre (fun σ hσ => by
              obtain ⟨rfl, hf⟩ := hσ
              simp_all)
          have h₂ : HoareE C (fun σ => (σ = σ₀) ∧ bval b σ = false) S₂ Q (fun _ => t₀) :=
            HoareE.strengthen (ih₂ Q σ₀ σ' t₀ hev' hQ) (fun σ hσ => by rcases hσ with ⟨h, _⟩; assumption)
          refine HoareE.conseq (HoareE.ite h₁ h₂) (fun _ h => h) (fun _ h => h)
            (fun σ hσ => ?_)
          subst hσ
          show t₀ + tbcost C b σ = tbcost C b σ + t₀
          omega

theorem complete_loopFree {P : Assn} {S : Stmt} {Q : Assn} {T : Cost}
    (hlf : S.LoopFree) (h : ValidExact C P S Q T) : HoareE C P S Q T := by
  refine HoareE.of_pointwise (fun σ₀ hP => ?_)
  obtain ⟨σ', hev, hQ⟩ := h σ₀ hP
  refine HoareE.conseq (complete_singleton hlf Q σ₀ σ' (T σ₀) hev hQ)
    (fun _ h => h) (fun _ h => h) (fun σ hσ => ?_)
  subst hσ
  rfl

end HoareE

end ResourcesLogic
