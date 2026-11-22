import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0172
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorFirstCommutesHeisenbergDerivativeSec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DerivComm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem exists_biBound (hψ : IsStdChar D ψ (-1)) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (h : IsBiTheta ψ A S A' C) : ∃ B : ℝ, ∀ u v, ‖C u v‖ ≤ B := by
  obtain ⟨B, hB⟩ := GlobalTheory.WeilVacMove.exists_bound hψ
    (GlobalTheory.BiTransfer.isThetaFunO_join (GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')) h)
  refine ⟨B, fun u v => ?_⟩
  have := hB (GlobalTheory.BiTransfer.inlH (GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')) S u +
    GlobalTheory.BiTransfer.inrH (GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')) S v)
  rwa [GlobalTheory.BiTransfer.join_inl_inr] at this

theorem om_dLine_right : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS χS' χA' : (AE D)ˣ →* Circle) (oma : Om A S) (omb : Om S A'), IsWeilDatumO ψ A S χA χS oma → IsWeilDatumO ψ S A' χS' χA' omb → BiAct D → ∀ G : WO A S → WO S A' → ℂ, IsBiTheta ψ A S A' G → ∀ M' : ℝ →+ WO S A', Continuous M' → (∀ s, (M' s).map (finPart D) = 0) → ∀ p u v, oma p (fun u' => GlobalTheory.WeilVacMove.dLine ψ S A' M' (G u') v) u = GlobalTheory.WeilVacMove.dLine ψ S A' M' (fun v' => oma p (fun u' => G u' v') u) v := by
  intro D ψ A S A' χA χS χS' χA' oma omb hA hB hBi G hG M' hM hM0 p u v
  have hψ : IsStdChar D ψ (-1) := hA.std
  set G' : WO A S → WO S A' → ℂ := fun u v => GlobalTheory.WeilVacMove.dLine ψ S A' M' (G u) v with hG'def
  have hG' : IsBiTheta ψ A S A' G' := (GlobalTheory.T.isJointlySmoothBiTheta_heisenbergDeriv D ψ hψ A S A' G hG).2 M' hM hM0
  set H : WO A S → WO S A' → ℂ := fun u v => oma p (fun u' => G u' v) u with hHdef
  have hH : IsBiTheta ψ A S A' H := (hBi ψ A S A' χA χS χS' χA' oma omb hA hB G hG).1 p
  set H' : WO A S → WO S A' → ℂ := fun u v => oma p (fun u' => G' u' v) u with hH'def
  have hH' : IsBiTheta ψ A S A' H' := (hBi ψ A S A' χA χS χS' χA' oma omb hA hB G' hG').1 p

  set c : ℝ → ℂ := fun s => ψ (symplOH S A' v (M' s)) with hcdef
  have hc : Continuous c := hψ.1.1.comp (GlobalTheory.WeilVacMove.continuous_symplOH S A' continuous_const hM)
  have hc1 : ∀ s, ‖c s‖ = 1 := fun s => hψ.1.2.1 _
  have hheis : ∀ (f : WO S A' → ℂ) s, heisO ψ S A' (M' s) f v = c s * f (v + M' s) := fun f s => rfl
  have hvm : Continuous fun s => v + M' s := continuous_const.add hM
  have hG'c : Continuous fun q : ℝ × WO A S => G' q.2 (v + M' q.1) :=
    hG'.cont.comp (f := fun q : ℝ × WO A S => (q.2, v + M' q.1)) (continuous_snd.prodMk (hvm.comp continuous_fst))
  have hH'c : Continuous fun q : ℝ × WO A S => H' q.2 (v + M' q.1) :=
    hH'.cont.comp (f := fun q : ℝ × WO A S => (q.2, v + M' q.1)) (continuous_snd.prodMk (hvm.comp continuous_fst))
  have hF0 : Continuous fun q : ℝ × WO A S => c q.1 * G' q.2 (v + M' q.1) := (hc.comp continuous_fst).mul hG'c
  have hoF0 : Continuous fun q : ℝ × WO A S => c q.1 * H' q.2 (v + M' q.1) := (hc.comp continuous_fst).mul hH'c

  set F : ℝ → WO A S → ℂ := fun s u' => c s * G' u' (v + M' s) with hFdef
  have hFth : ∀ s, IsThetaFunO ψ A S (F s) := fun s =>
    GlobalTheory.WeilVacMove.isTheta_smul (c s) (GlobalTheory.FrComb.slice_left hG' (v + M' s))
  have hFc : Continuous fun q : ℝ × WO A S => F q.1 q.2 := hF0
  obtain ⟨B1, hB1⟩ := exists_biBound hψ hG'
  have hFb : ∃ C : ℝ, ∀ a x, ‖F a x‖ ≤ C := ⟨B1, fun a x => by
    rw [hFdef, norm_mul, hc1, one_mul]; exact hB1 _ _⟩
  have hoF : ∀ s, oma p (F s) = fun u => c s * H' u (v + M' s) := by
    intro s
    have e : F s = c s • (fun u' => G' u' (v + M' s)) := rfl
    rw [e, map_smul]
    rfl
  have hoFc : Continuous fun q : ℝ × WO A S => oma p (F q.1) q.2 := by
    simp only [hoF]
    exact hoF0
  obtain ⟨B2, hB2⟩ := exists_biBound hψ hH'
  have hoFb : ∃ C : ℝ, ∀ a x, ‖oma p (F a) x‖ ≤ C := ⟨B2, fun a x => by
    rw [hoF, norm_mul, hc1, one_mul]; exact hB2 _ _⟩

  have hftc : ∀ u' t, ∫ s in (0 : ℝ)..t, F s u' = c t * G u' (v + M' t) - G u' v := by
    intro u' t
    have hd : ∀ s, HasDerivAt (fun t : ℝ => heisO ψ S A' (M' t) (G u') v)
        (heisO ψ S A' (M' s) (G' u') v) s := fun s =>
      GlobalTheory.WeilVacMove.hasDerivAt_line hψ hM hM0 (GlobalTheory.FrComb.slice_right hG u') v s
    have hcont : Continuous fun s => F s u' :=
      hF0.comp (f := fun s : ℝ => (s, u')) (continuous_id.prodMk continuous_const)
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t) (fun s _ => hd s)
      (hcont.intervalIntegrable _ _)
    change ∫ s in (0 : ℝ)..t, heisO ψ S A' (M' s) (G' u') v = _
    rw [this, hheis, hheis]
    simp only [hcdef, map_zero, add_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul]

  set φ : ℝ → ℂ := fun t => c t * H u (v + M' t) with hφdef
  set k : ℝ → ℂ := fun s => c s * H' u (v + M' s) with hkdef
  have hk : Continuous k := hoF0.comp (f := fun s : ℝ => (s, u)) (continuous_id.prodMk continuous_const)
  have hφint : ∀ t, 0 ≤ t → φ t = φ 0 + ∫ s in (0 : ℝ)..t, k s := by
    intro t ht
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
      isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    have hth : IsThetaFunO ψ A S (fun x => ∫ a, F a x ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) := by
      have e : (fun x => ∫ a, F a x ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) =
          c t • (fun u' => G u' (v + M' t)) - (fun u' => G u' v) := by
        funext x
        rw [← intervalIntegral.integral_of_le ht, hftc]
        rfl
      rw [e]
      exact GlobalTheory.WeilVacMove.isTheta_sub (GlobalTheory.WeilVacMove.isTheta_smul _ (GlobalTheory.FrComb.slice_left hG _))
        (GlobalTheory.FrComb.slice_left hG v)
    have hcomm := GlobalTheory.T.weilOperator_integral_comm_of_bounded_finiteMeasure D ψ A S χA χS oma hA ℝ (volume.restrict (Set.Ioc (0 : ℝ) t)) F p hFth hFc hFb hoFc hoFb hth u
    have e1 : (fun y => ∫ a, F a y ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) =
        c t • (fun u' => G u' (v + M' t)) - (fun u' => G u' v) := by
      funext x
      rw [← intervalIntegral.integral_of_le ht, hftc]
      rfl
    rw [e1, map_sub, map_smul] at hcomm
    have e2 : ∫ a, oma p (F a) u ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) = ∫ s in (0 : ℝ)..t, k s := by
      rw [intervalIntegral.integral_of_le ht]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      show oma p (F s) u = k s
      rw [hoF]
    rw [e2] at hcomm
    have e3 : φ 0 = H u v := by
      rw [hφdef]; simp only [map_zero, add_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, hcdef, AddChar.map_zero_eq_one, one_mul]
    rw [e3, ← hcomm]
    simp only [hφdef, hHdef, LinearMap.sub_apply, Pi.sub_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring

  have h1 : HasDerivAt φ (GlobalTheory.WeilVacMove.dLine ψ S A' M' (H u) v) 0 :=
    (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ hM hM0 (GlobalTheory.FrComb.slice_right hH u)).1 v
  have h2 : HasDerivWithinAt φ (k 0) (Set.Ici 0) 0 := by
    have h3 : HasDerivAt (fun t => φ 0 + ∫ s in (0 : ℝ)..t, k s) (k 0) 0 :=
      ((hk.integral_hasStrictDerivAt 0 0).hasDerivAt).const_add _
    refine h3.hasDerivWithinAt.congr (fun t ht => hφint t ht) (hφint 0 le_rfl)
  have h4 := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ h1.hasDerivWithinAt h2
  have e4 : k 0 = H' u v := by
    simp only [hkdef, hcdef, map_zero, add_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul]
  rw [e4] at h4
  exact h4.symm

end GlobalTheory.DerivComm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WithMuEq
section
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel Matrix

noncomputable section

namespace GlobalTheory.SeeSaw.MuUnits

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem Phi_eq {a t : Type} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] (Q Q' : TypeDatum k a)
    (hJ : Q.J = Q'.J) (hl : ∀ x (hx : x ∈ Q.J) (hx' : x ∈ Q'.J), Q.lam ⟨x, hx⟩ = Q'.lam ⟨x, hx'⟩)
    (μ μ' : kˣ →* ℂˣ) (hμ : ∀ x : kˣ, valuation k (x : k) = 1 → μ x = μ' x) (x : Matrix (a ⊕ t) a k) :
    Q.Phi t μ x = Q'.Phi t μ' x := by
  by_cases h : (∃ g ∈ Q.J, g.val = x.toRows₁) ∧ MaxM x.toRows₂
  · obtain ⟨⟨g, hg, e⟩, h2⟩ := h
    have hg' : g ∈ Q'.J := hJ ▸ hg
    rw [Q.Phi_of_mem μ ⟨g, hg⟩ e h2, Q'.Phi_of_mem μ' ⟨g, hg'⟩ e h2, hl g hg hg',
      hμ _ (valuation_det_of_mem_KO (Q.le_KO hg))]
  · have h' : ¬ ((∃ g ∈ Q'.J, g.val = x.toRows₁) ∧ MaxM x.toRows₂) := by rwa [← hJ]
    rw [not_not.1 (mt (Q.Phi_ne_zero_iff μ).1 h), not_not.1 (mt (Q'.Phi_ne_zero_iff μ').1 h')]

theorem iter_eq {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ μ' : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hμ' : ∀ j, IsTame (μ' j))
    (h : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = μ' j x) (j : ℕ) :
    (P.iter t μ hμ j).J = (P.iter t μ' hμ' j).J ∧ ∀ x (hx : x ∈ (P.iter t μ hμ j).J) (hx' : x ∈ (P.iter t μ' hμ' j).J),
      (P.iter t μ hμ j).lam ⟨x, hx⟩ = (P.iter t μ' hμ' j).lam ⟨x, hx'⟩ := by
  induction j with
  | zero => exact ⟨rfl, fun _ _ _ => rfl⟩
  | succ j ih =>
    obtain ⟨hJ, hl⟩ := ih
    set Q := P.iter t μ hμ j
    set Q' := P.iter t μ' hμ' j
    have hS : Q.stepJ t = Q'.stepJ t := by
      ext g; rw [TypeDatum.mem_stepJ, TypeDatum.mem_stepJ, hJ]
    refine ⟨?_, fun x hx hx' => ?_⟩
    · rw [TypeDatum.iter_succ, TypeDatum.iter_succ]
      change (Q.stepJ t).comap _ = (Q'.stepJ t).comap _
      rw [hS]
    · have hx1 : (reGL (ixSucc r t j)).symm x ∈ Q.stepJ t := hx
      have hx1' : (reGL (ixSucc r t j)).symm x ∈ Q'.stepJ t := hx'
      change (Q.step t (μ (j + 1)) (hμ _)).lam ⟨_, hx1⟩ = (Q'.step t (μ' (j + 1)) (hμ' _)).lam ⟨_, hx1'⟩
      have hg' : ((Q.corner ⟨_, hx1⟩ : Q.J) : GL _ k) ∈ Q'.J := hJ ▸ (Q.corner ⟨_, hx1⟩).2
      refine (Q.step_lam _ _ ⟨_, hx1⟩ (Q.corner ⟨_, hx1⟩) (Q.corner_val _)).trans
        (Eq.trans ?_ (Q'.step_lam _ _ ⟨_, hx1'⟩ ⟨_, hg'⟩ (Q.corner_val _)).symm)
      rw [hl _ (Q.corner ⟨_, hx1⟩).2 hg',
        h _ _ (valuation_det_of_mem_KO (Q.le_KO (Q.corner ⟨_, hx1⟩).2)), h _ _ (valuation_det_of_mem_KO hx1.1)]

theorem withMu_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ)
    (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) :
    (∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = S.μ j x) →
      (∀ j a H, ((withMu S μ hμ).T t).Phi j a H = (S.T t).Phi j a H) ∧
      ∀ j a H, (((withMu S μ hμ).T t).lev j a H).J = ((S.T t).lev j a H).J ∧
        ∀ x hx hx', (((withMu S μ hμ).T t).lev j a H).lam ⟨x, hx⟩ = ((S.T t).lev j a H).lam ⟨x, hx'⟩ := by
  intro h
  have E := iter_eq (t := t) S.P μ S.μ hμ S.tame h
  refine ⟨fun j a H => funext fun x => ?_, fun j a H => ⟨?_, fun x hx hx' => ?_⟩⟩
  · change (S.P.iter t μ hμ j).Phi t (μ (j + 1)) _ = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1)) _
    exact Phi_eq _ _ (E j).1 (E j).2 _ _ (h (j + 1)) _
  · change (S.P.iter t μ hμ j).J.comap _ = (S.P.iter t S.μ S.tame j).J.comap _
    rw [(E j).1]; rfl
  · exact (E j).2 _ hx hx'

end GlobalTheory.SeeSaw.MuUnits
end
end

