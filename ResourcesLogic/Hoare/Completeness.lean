import ResourcesLogic.Hoare.Kernel

namespace ResourcesLogic

open Classical

noncomputable def runCost (C : CostModel) (S : Stmt) (σ : State) : Nat :=
  if h : ∃ p : Nat × State, Eval C S σ p.1 p.2 then h.choose.1 else 0

theorem runCost_eq {C : CostModel} {S : Stmt} {σ σ' : State} {t : Nat}
    (h : Eval C S σ t σ') : runCost C S σ = t := by
  have hex : ∃ p : Nat × State, Eval C S σ p.1 p.2 := ⟨(t, σ'), h⟩
  rw [runCost, dif_pos hex]
  have hc := hex.choose_spec
  apply Eval.cost_unique <;> assumption

inductive WhileSteps (C : CostModel) (b : BExp) (S : Stmt) : State → Nat → Prop where
  | zero {σ} : bval b σ = false → WhileSteps C b S σ 0
  | succ {σ σ'' t n} : bval b σ = true → Eval C S σ t σ'' →
      WhileSteps C b S σ'' n → WhileSteps C b S σ (n + 1)

theorem whileSteps_of_eval {C : CostModel} {b : BExp} {S : Stmt} :
    ∀ {W : Stmt} {σ t σ'}, Eval C W σ t σ' → W = .while b S →
      ∃ n, WhileSteps C b S σ n := by
  intro W σ t σ' h
  induction h with
  | skip => intro hW; simp_all
  | assign => intro hW; simp_all
  | arrAssign => intro hW; simp_all
  | seq _ _ _ _ => intro hW; simp_all
  | iteT _ _ _ => intro hW; simp_all
  | iteF _ _ _ => intro hW; simp_all
  | whileT hb hbody _ _ ihloop =>
      intro hW
      simp only [Stmt.while.injEq] at hW
      obtain ⟨rfl, rfl⟩ := hW
      obtain ⟨n, hn⟩ := ihloop rfl
      exists n + 1
      apply WhileSteps.succ <;> assumption
  | whileF hb =>
      intro hW
      simp only [Stmt.while.injEq] at hW
      obtain ⟨rfl, rfl⟩ := hW
      exists 0
      apply WhileSteps.zero <;> assumption

theorem WhileSteps.unique {C : CostModel} {b : BExp} {S : Stmt} {σ : State} {n m : Nat}
    (h₁ : WhileSteps C b S σ n) (h₂ : WhileSteps C b S σ m) : n = m := by
  induction h₁ generalizing m with
  | zero hb =>
      cases h₂ with
      | zero => rfl
      | succ hb' _ _ => simp_all
  | succ hb hev _ ih =>
      cases h₂ with
      | zero hb' => simp_all
      | succ _ hev' hsteps' =>
          obtain ⟨_, rfl⟩ := Eval.deterministic hev hev'
          have := ih hsteps'; omega

noncomputable def steps (C : CostModel) (b : BExp) (S : Stmt) (σ : State) : Nat :=
  if h : ∃ n, WhileSteps C b S σ n then h.choose else 0

theorem steps_eq {C : CostModel} {b : BExp} {S : Stmt} {σ : State} {n : Nat}
    (h : WhileSteps C b S σ n) : steps C b S σ = n := by
  have hex : ∃ n, WhileSteps C b S σ n := ⟨n, h⟩
  rw [steps, dif_pos hex]
  have hc := hex.choose_spec
  apply WhileSteps.unique <;> assumption

theorem Hoare.complete_singleton {C : CostModel} (S : Stmt) :
    ∀ (Q : Assn) (σ₀ σ' : State) (t : Nat), Eval C S σ₀ t σ' → Q σ' →
      Hoare C (fun σ => σ = σ₀) S Q (fun _ => t) := by
  induction S with
  | skip =>
      intro Q σ₀ σ' t hev hQ
      cases hev
      refine Hoare.conseq Hoare.skip (fun σ hσ => ?_) (fun _ h => h) (fun _ _ => le_refl _)
      subst hσ; assumption
  | assign x a =>
      intro Q σ₀ σ' t hev hQ
      cases hev
      refine Hoare.conseq Hoare.assign (fun σ hσ => ?_) (fun _ h => h) (fun σ hσ => ?_)
      · subst hσ; assumption
      · subst hσ; apply le_refl
  | arrAssign x a₁ a₂ =>
      intro Q σ₀ σ' t hev hQ
      cases hev
      refine Hoare.conseq Hoare.arrAssign (fun σ hσ => ?_) (fun _ h => h) (fun σ hσ => ?_)
      · subst hσ; assumption
      · subst hσ; apply le_refl
  | seq S₁ S₂ ih₁ ih₂ =>
      intro Q σ₀ σ' t hev hQ
      cases hev with
      | @seq _ σ₁ _ _ _ t₁ t₂ hev₁ hev₂ =>
          have h₂ : Hoare C (fun σ => σ = σ₁) S₂ Q (fun _ => t₂) :=
            ih₂ Q σ₁ σ' t₂ hev₂ hQ
          have h₁ : Hoare C (fun σ => σ = σ₀) S₁
              (fun σ => (σ = σ₁) ∧ (fun _ : State => t₂) σ ≤ t₂) (fun _ => t₁) :=
            ih₁ _ σ₀ σ₁ t₁ hev₁ ⟨rfl, le_refl _⟩
          refine Hoare.seq t₂ h₁ h₂
  | ite b S₁ S₂ ih₁ ih₂ =>
      intro Q σ₀ σ' t hev hQ
      cases hev with
      | @iteT _ _ _ _ _ t₀ hb hev' =>
          have h₁ : Hoare C (fun σ => (σ = σ₀) ∧ bval b σ = true) S₁ Q (fun _ => t₀) :=
            Hoare.strengthen (ih₁ Q σ₀ σ' t₀ hev' hQ) (fun σ hσ => by rcases hσ with ⟨h, _⟩; assumption)
          have h₂ : Hoare C (fun σ => (σ = σ₀) ∧ bval b σ = false) S₂ Q (fun _ => 0) :=
            Hoare.strengthen Hoare.false_pre (fun σ hσ => by
              obtain ⟨rfl, hf⟩ := hσ
              simp_all)
          refine Hoare.conseq (Hoare.ite h₁ h₂) (fun _ h => h) (fun _ h => h) (fun σ hσ => ?_)
          subst hσ
          show max t₀ 0 + tbcost C b σ ≤ tbcost C b σ + t₀
          omega
      | @iteF _ _ _ _ _ t₀ hb hev' =>
          have h₁ : Hoare C (fun σ => (σ = σ₀) ∧ bval b σ = true) S₁ Q (fun _ => 0) :=
            Hoare.strengthen Hoare.false_pre (fun σ hσ => by
              obtain ⟨rfl, hf⟩ := hσ
              simp_all)
          have h₂ : Hoare C (fun σ => (σ = σ₀) ∧ bval b σ = false) S₂ Q (fun _ => t₀) :=
            Hoare.strengthen (ih₂ Q σ₀ σ' t₀ hev' hQ) (fun σ hσ => by rcases hσ with ⟨h, _⟩; assumption)
          refine Hoare.conseq (Hoare.ite h₁ h₂) (fun _ h => h) (fun _ h => h) (fun σ hσ => ?_)
          subst hσ
          show max 0 t₀ + tbcost C b σ ≤ tbcost C b σ + t₀
          omega
  | «while» b S ihS =>
      intro Q σ₀ σ' t hev hQ

      set I : Assn := fun σ => ∃ tt σf, Eval C (.while b S) σ tt σf ∧ Q σf with hI_def
      set E : Cost := fun σ => runCost C (.while b S) σ with hE_def
      set f : State → Nat := fun σ => steps C b S σ with hf_def
      set T : Cost := fun σ => runCost C S σ with hT_def
      have hexit : ∀ σ, I σ → bval b σ = false → tbcost C b σ ≤ E σ := by
        intro σ _ hb
        have h : E σ = tbcost C b σ := runCost_eq (Eval.whileF hb)
        omega
      have hbody : ∀ k n c : Nat,
          Hoare C
            (fun σ => I σ ∧ bval b σ = true ∧ f σ = k ∧ E σ = n ∧ tbcost C b σ + T σ = c)
            S (fun σ' => I σ' ∧ f σ' < k ∧ E σ' + c ≤ n) T := by
        intro k n c
        refine Hoare.of_pointwise (fun σ₁ hpre => ?_)
        obtain ⟨hI₁, hb₁, hfk, hEn, hc⟩ := hpre
        obtain ⟨tt, σf, hloop, hQf⟩ := hI₁
        cases hloop with
        | whileF hb' => simp_all
        | @whileT _ _ σ₂ _ _ tb t' _ hbodyEv hloopEv =>
            have hTb : T σ₁ = tb := runCost_eq hbodyEv
            have hE₂ : E σ₂ = t' := runCost_eq hloopEv
            have hEσ₁ : E σ₁ = tbcost C b σ₁ + tb + t' :=
              runCost_eq (Eval.whileT hb₁ hbodyEv hloopEv)
            obtain ⟨m, hm⟩ := whileSteps_of_eval hloopEv rfl
            have hf₂ : f σ₂ = m := steps_eq hm
            have hf₁ : f σ₁ = m + 1 := steps_eq (WhileSteps.succ hb₁ hbodyEv hm)
            have hpost : I σ₂ ∧ f σ₂ < k ∧ E σ₂ + c ≤ n := by
              refine ⟨⟨t', σf, hloopEv, hQf⟩, by omega, by omega⟩
            refine Hoare.conseq (ihS _ σ₁ σ₂ tb hbodyEv hpost) (fun _ h => h)
              (fun _ h => h) (fun σ hσ => ?_)
            subst hσ
            omega
      have hmain : Hoare C I (.while b S) (fun σ => I σ ∧ bval b σ = false) E :=
        Hoare.while E f hbody hexit
      refine Hoare.conseq hmain (fun σ hσ => ?_) (fun σ hσ => ?_) (fun σ hσ => ?_)
      · subst hσ; exists t, σ'
      · obtain ⟨⟨tt, σf, hloop, hQf⟩, hb⟩ := hσ
        cases hloop with
        | whileF _ => assumption
        | whileT hb' _ _ => simp_all
      · subst hσ
        have h : E σ = t := runCost_eq hev
        omega

theorem Hoare.complete {C : CostModel} {P : Assn} {S : Stmt} {Q : Assn} {T : Cost}
    (h : Valid C P S Q T) : Hoare C P S Q T := by
  refine Hoare.of_pointwise (fun σ₀ hP => ?_)
  obtain ⟨σ', t, hev, hQ, hle⟩ := h σ₀ hP
  refine Hoare.weakenCost (Hoare.complete_singleton S Q σ₀ σ' t hev hQ) (fun σ hσ => ?_)
  subst hσ
  assumption

theorem Hoare.iff_valid {C : CostModel} {P : Assn} {S : Stmt} {Q : Assn} {T : Cost} :
    Hoare C P S Q T ↔ Valid C P S Q T :=
  ⟨Hoare.sound, Hoare.complete⟩

end ResourcesLogic
