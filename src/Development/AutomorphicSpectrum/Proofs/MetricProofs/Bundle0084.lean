import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0074
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0076
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHolds
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftToLogResolutionAnalyticStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_to_log_resolution_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D e : ℕ) (R : AnLogRes P J D), J = ⊤ → ∀ (V : Set (Fin e → ℂ)) (μ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (g : (Fin e → ℂ) → R.X), IsOpen V → (∀ q, AnalyticOnNhd ℂ (fun u => μ u q) V) → (∀ u ∈ V, SameOrbit (R.lift (g u) (g u)) (μ u)) → ContinuousOn g V ∧ ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ g) (V ∩ g ⁻¹' (R.A.chart k).source) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.HoloLift.holo_of_analytic_lift | exact GlobalTheory.CompanionTheory.Ar.PB.HoloLift.holo_of_analytic_lift | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.HoloLift.holo_of_analytic_lift <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocDensAddOfFunContinuousOn
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem locDens_add_ofFun_continuousOn : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X), IsOpen U → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → ∀ j, ContinuousOn (locDens A (fun i => P i + LocPot.ofFun (f i) + Θ) j) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) := by
  intro e X _ A U P f Θ hU hP hΘ hf j
  have hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).isOpen_inter_preimage_symm hU
  have hm : Continuous (mdisc : (Fin e → Matrix (Fin e) (Fin e) ℂ) → ℂ) := by
    unfold mdisc; fun_prop
  have hf2 : ∀ k, ContDiffOn ℝ 2 (f k ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) := fun k =>
    (hf k j).of_le (WithTop.coe_le_coe.2 le_top)
  have hH : ContinuousOn (fun y => fun k =>
      (hessC (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y +
        hessC (f k ∘ (A.chart j).symm) y +
        hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y :
          Matrix (Fin e) (Fin e) ℂ))
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    continuousOn_pi.2 fun k =>
      (((hessC_base_continuousOn A (P k) (hP k) j).mono Set.inter_subset_left).add
        (hessC_continuousOn _ _ hVo (hf2 k))).add
        ((hessC_base_continuousOn A Θ hΘ j).mono Set.inter_subset_left)
  have hc := (continuousOn_const (c := (e.factorial : ℝ) * (2 / Real.pi) ^ e)
    (s := (A.chart j).target ∩ (A.chart j).symm ⁻¹' U)).mul
    (Complex.continuous_re.comp_continuousOn (hm.comp_continuousOn hH))
  refine hc.congr fun y hy => ?_
  unfold locDens maDens
  simp only [Function.comp_apply, Pi.mul_apply]
  congr 3
  funext k
  have hP' := potential_contDiffAt A (P k) (hP k) j hy.1
  have hΘ' := potential_contDiffAt A Θ hΘ j hy.1
  have hf' : ContDiffAt ℝ 2 (f k ∘ (A.chart j).symm) y :=
    (hf2 k).contDiffAt (hVo.mem_nhds hy)
  rw [show (fun y' => (P k + LocPot.ofFun (f k) + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) =
    fun y' => ((fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y' +
      (f k ∘ (A.chart j).symm) y') + (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y'
    from rfl]
  rw [hessC_add' _ _ _ (hP'.add hf') hΘ', hessC_add' _ _ _ hP' hf']

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalDensityInclusionExclusion
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

theorem locDens_expand_ofFun : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X), IsOpen U → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → ∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, locDens A (fun i => P i + LocPot.ofFun (f i)) j y = ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) * locDens A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y := by
  intro e X _ A U P f Θ hU hPot hΘ hf j y hy
  classical
  unfold ReciprocityTheory.AnForm.M.IsPotential at hPot hΘ
  have smooth_at : ∀ (g : X → ℝ) (W : Set X), IsOpen W → A.SmoothOn W g →
      y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W →
      ContDiffAt ℝ 2 (fun y' => g ((A.chart j).symm y')) y := by
    intro g W hW hg hyW
    have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
      (A.chart j).isOpen_inter_preimage_symm hW
    have h1 := (hg j).contDiffAt (hopen.mem_nhds hyW)
    exact h1.of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤) | decide | simp)
  have hsP : ∀ k, ContDiffAt ℝ 2
      (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := fun k =>
    smooth_at ((P k).φ ((A.chart j).symm y)) ((P k).U ((A.chart j).symm y)) ((P k).isOpen_U _)
      ((hPot k).1 _) ⟨hy.1, (P k).mem_U _⟩
  have hsf : ∀ k, ContDiffAt ℝ 2 (fun y' => f k ((A.chart j).symm y')) y := fun k =>
    smooth_at (f k) U hU (hf k) hy
  have hsΘ : ContDiffAt ℝ 2 (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y :=
    smooth_at (Θ.φ ((A.chart j).symm y)) (Θ.U ((A.chart j).symm y)) (Θ.isOpen_U _)
      (hΘ.1 _) ⟨hy.1, Θ.mem_U _⟩
  have hessAdd : ∀ φ ψ : (Fin e → ℂ) → ℝ, ContDiffAt ℝ 2 φ y → ContDiffAt ℝ 2 ψ y →
      hessC (fun w => φ w + ψ w) y = hessC φ y + hessC ψ y := by
    intro φ ψ hφ hψ
    have hev : ∀ χ : (Fin e → ℂ) → ℝ, ContDiffAt ℝ 2 χ y → ∀ᶠ w in 𝓝 y, DifferentiableAt ℝ χ w := by
      intro χ hχ
      obtain ⟨f', u, hu, -, hder⟩ :=
        contDiffAt_one_iff.1 (hχ.of_le (by first | norm_num | exact one_le_two))
      exact Filter.mem_of_superset hu fun w hw => (hder w hw).differentiableAt
    have hd2 : ∀ χ : (Fin e → ℂ) → ℝ, ContDiffAt ℝ 2 χ y → DifferentiableAt ℝ (fderiv ℝ χ) y := by
      intro χ hχ
      exact (hχ.fderiv_right (m := 1) (by first | norm_num | exact le_of_eq one_add_one_eq_two)).differentiableAt one_ne_zero
    have hfd : fderiv ℝ (fun w => φ w + ψ w) =ᶠ[𝓝 y] fun w => fderiv ℝ φ w + fderiv ℝ ψ w := by
      filter_upwards [hev φ hφ, hev ψ hψ] with w h1 h2
      exact fderiv_add h1 h2
    have h2 : fderiv ℝ (fderiv ℝ (fun w => φ w + ψ w)) y =
        fderiv ℝ (fderiv ℝ φ) y + fderiv ℝ (fderiv ℝ ψ) y := by
      rw [hfd.fderiv_eq]
      exact fderiv_add (hd2 φ hφ) (hd2 ψ hψ)
    ext a b
    simp only [ReciprocityTheory.AnForm.hessC, h2, Matrix.add_apply, ContinuousLinearMap.add_apply,
      Complex.ofReal_add, Complex.ofReal_sub]
    ring
  have hL : ∀ k, hessC (fun y' => (P k + LocPot.ofFun (f k)).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      hessC (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y +
        hessC (fun y' => f k ((A.chart j).symm y')) y := fun k =>
    hessAdd (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y'))
      (fun y' => f k ((A.chart j).symm y')) (hsP k) (hsf k)
  have hR : ∀ (T : Finset (Fin e)) (k : Fin e),
      hessC (fun y' => ((if k ∈ T then P k else LocPot.ofFun 0) + LocPot.ofFun (if k ∈ T then f k else 0) + Θ).φ
        ((A.chart j).symm y) ((A.chart j).symm y')) y =
        if k ∈ T then hessC (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y +
            hessC (fun y' => f k ((A.chart j).symm y')) y +
            hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y
        else hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
    intro T k
    by_cases hk : k ∈ T
    · simp only [hk, ↓reduceIte]
      rw [← hL k]
      exact hessAdd (fun y' => (P k + LocPot.ofFun (f k)).φ ((A.chart j).symm y) ((A.chart j).symm y'))
        (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) ((hsP k).add (hsf k)) hsΘ
    · simp only [hk, ↓reduceIte]
      congr 1
      funext y'
      show (0 : X → ℝ) ((A.chart j).symm y') + (0 : X → ℝ) ((A.chart j).symm y') +
          Θ.φ ((A.chart j).symm y) ((A.chart j).symm y') = Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')
      simp
  have hPE : ∀ x z : Fin e → ℂ, ∑ T : Finset (Fin e), (-1 : ℂ) ^ (e - T.card) *
      ∏ k, (if k ∈ T then x k + z k else z k) = ∏ k, x k := by
    intro x z
    have hadd := Finset.prod_add (fun k => x k + z k) (fun k => -z k) (Finset.univ : Finset (Fin e))
    simp only [add_neg_cancel_right, Finset.powerset_univ] at hadd
    rw [hadd]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_neg, Finset.card_univ_diff, Fintype.card_fin]
    rw [show (∏ k, if k ∈ T then x k + z k else z k) = ∏ k, T.piecewise (fun k => x k + z k) z k from rfl,
      Finset.prod_piecewise, Finset.univ_inter]
    ring
  have hK : ∀ c : Fin e → Fin e, ∑ S : Finset (Fin e), (-1 : ℂ) ^ (e - S.card) *
      (if ∀ i, c i ∈ S then (1 : ℂ) else 0) = if Function.Surjective c then 1 else 0 := by
    intro c
    have hterm : ∀ S : Finset (Fin e), (if ∀ i, c i ∈ S then (1 : ℂ) else 0) =
        ∏ k, (if k ∈ S then (if k ∈ Set.range c then (1 : ℂ) else 0) + (if k ∈ Set.range c then 0 else 1)
          else (if k ∈ Set.range c then 0 else 1)) := by
      intro S
      by_cases h : ∀ i, c i ∈ S
      · rw [if_pos h]
        symm
        refine Finset.prod_eq_one fun k _ => ?_
        by_cases hkS : k ∈ S
        · rw [if_pos hkS]
          split_ifs <;> simp
        · have hkr : k ∉ Set.range c := by
            rintro ⟨i, rfl⟩
            exact hkS (h i)
          rw [if_neg hkS, if_neg hkr]
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        rw [if_neg (fun h' => hi (h' i))]
        symm
        refine Finset.prod_eq_zero (Finset.mem_univ (c i)) ?_
        rw [if_neg hi, if_pos (Set.mem_range_self i)]
    simp only [hterm]
    rw [hPE, Finset.prod_boole]
    by_cases hs : Function.Surjective c
    · rw [if_pos hs, if_pos (show ∀ i ∈ Finset.univ, i ∈ Set.range c from fun k _ => hs k)]
    · rw [if_neg hs, if_neg (show ¬ ∀ i ∈ Finset.univ, i ∈ Set.range c from fun h => hs fun k => h k (Finset.mem_univ k))]
  have hE : ∀ B : Fin e → Matrix (Fin e) (Fin e) ℂ,
      ∑ S : Finset (Fin e), (-1 : ℂ) ^ (e - S.card) * (∑ k ∈ S, B k).det =
        ∑ σ : Equiv.Perm (Fin e), ∑ c : Fin e → Fin e,
          (if Function.Surjective c then (1 : ℂ) else 0) *
            (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, B (c i) (σ i) i) := by
    intro B
    have h1 : ∀ S : Finset (Fin e), (∑ k ∈ S, B k).det = ∑ σ : Equiv.Perm (Fin e), ∑ c : Fin e → Fin e,
        (if ∀ i, c i ∈ S then (1 : ℂ) else 0) * (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, B (c i) (σ i) i) := by
      intro S
      rw [Matrix.det_apply']
      refine Finset.sum_congr rfl fun σ _ => ?_
      have hs : ∀ i, (∑ k ∈ S, B k) (σ i) i = ∑ k, if k ∈ S then B k (σ i) i else 0 := by
        intro i
        rw [Matrix.sum_apply, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      simp only [hs]
      rw [Fintype.prod_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases h : ∀ i, c i ∈ S
      · rw [if_pos h, one_mul, Finset.prod_congr rfl fun i _ => if_pos (h i)]
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        rw [if_neg (fun h' => hi (h' i)), zero_mul, Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi),
          mul_zero]
    simp only [h1, Finset.mul_sum]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin e))))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin e))))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hK c, Finset.sum_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    ring
  have hT : ∀ (B : Fin e → Matrix (Fin e) (Fin e) ℂ) (C : Matrix (Fin e) (Fin e) ℂ)
      (σ : Equiv.Perm (Fin e)) (c : Fin e → Fin e), Function.Surjective c →
      ∑ T : Finset (Fin e), (-1 : ℂ) ^ (e - T.card) * ∏ i, (if c i ∈ T then B (c i) + C else C) (σ i) i =
        ∏ i, B (c i) (σ i) i := by
    intro B C σ c hc
    obtain ⟨E, rfl⟩ : ∃ E : Fin e ≃ Fin e, ⇑E = c :=
      ⟨Equiv.ofBijective c ⟨Finite.injective_iff_surjective.2 hc, hc⟩, rfl⟩
    have hre : ∀ T : Finset (Fin e), ∏ i, (if E i ∈ T then B (E i) + C else C) (σ i) i =
        ∏ k, (if k ∈ T then B k (σ (E.symm k)) (E.symm k) + C (σ (E.symm k)) (E.symm k)
          else C (σ (E.symm k)) (E.symm k)) := by
      intro T
      refine Fintype.prod_equiv E _ _ fun i => ?_
      simp only [Equiv.symm_apply_apply]
      split_ifs <;> rfl
    simp only [hre]
    rw [hPE]
    exact (Fintype.prod_equiv E _ _ fun i => by simp only [Equiv.symm_apply_apply]).symm
  have hKey : ∀ (B : Fin e → Matrix (Fin e) (Fin e) ℂ) (C : Matrix (Fin e) (Fin e) ℂ),
      mdisc B = ∑ T : Finset (Fin e), (-1 : ℂ) ^ (e - T.card) *
        mdisc (fun k => if k ∈ T then B k + C else C) := by
    intro B C
    unfold ReciprocityTheory.AnForm.mdisc
    simp only [hE]
    have hterm : ∀ (σ : Equiv.Perm (Fin e)) (c : Fin e → Fin e),
        (if Function.Surjective c then (1 : ℂ) else 0) * (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, B (c i) (σ i) i) =
          ∑ T : Finset (Fin e), (-1 : ℂ) ^ (e - T.card) * ((if Function.Surjective c then (1 : ℂ) else 0) *
            (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, (if c i ∈ T then B (c i) + C else C) (σ i) i)) := by
      intro σ c
      by_cases hc : Function.Surjective c
      · rw [if_pos hc, ← hT B C σ c hc, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ => ?_
        ring
      · simp only [if_neg hc, zero_mul, mul_zero, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun c _ => hterm σ c]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin e))))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin e))))]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun T _ => ?_
    ring
  unfold ReciprocityTheory.AnForm.M.locDens ReciprocityTheory.AnForm.maDens
  simp only [hL, hR]
  rw [hKey (fun k => hessC (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y +
      hessC (fun y' => f k ((A.chart j).symm y')) y)
    (hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y)]
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [show ((-1 : ℂ) ^ (e - T.card)) = (((-1 : ℝ) ^ (e - T.card) : ℝ) : ℂ) by norm_num,
    Complex.re_ofReal_mul]
  ring

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorOfRegularMatrixValue
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem regAt_minorIJ_valAt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (N : ℕ) (A : Matrix (Fin N) (Fin N) Ω), z ∈ mcPts (mCoordIdeal x) → (∀ a b, RegAt x (mCoordIdeal z) (A a b)) → ∀ I J : Finset (Fin N), RegAt x (mCoordIdeal z) (minorIJ A I J) ∧ valAt x (minorIJ A I J) z = minorIJ (Matrix.of fun a b => valAt x (A a b) z) I J := by
  intro K _ ι _ Ω _ x z N A hz hA I J
  let A' : Matrix (Fin N) (Fin N) (GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.regRing x z) :=
    Matrix.of fun a b => ⟨A a b, hA a b⟩
  have hAA : A = A'.map (GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.regRing x z).subtype := by
    ext a b
    rfl
  have h1 : minorIJ A I J = ((minorIJ A' I J : GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.regRing x z) : Ω) := by
    rw [hAA, GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.minorIJ_map]
    rfl
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact (minorIJ A' I J).2
  · rw [h1]
    have h2 : valAt x ((minorIJ A' I J : GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.regRing x z) : Ω) z =
        GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.regVal x hz (minorIJ A' I J) := rfl
    rw [h2, ← GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.minorIJ_map]
    congr 1

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelDyWeightsStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_dy_weights : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ) (h : ModelOK A x₀ m) (τ : Ψ) (i : Fin (p + q)), (∀ k, (model A x₀ m h).dy (τ, i) (.inl k) = -((rkW i * m (.inl τ) + rkO i * m (.inr τ) : ℕ) : ℤ)) ∧ ∀ t : StepIx Ψ p q, ((t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) → (model A x₀ m h).dy (τ, i) (.inr t) = 1) ∧ (¬ (t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) → (model A x₀ m h).dy (τ, i) (.inr t) = 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy.dy_flag | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy.dy_flag | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy.dy_flag <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultAtTwistQuadEqStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multAt_twist_quad_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (J W : Ideal (MRing ι)), W ∈ J.minimalPrimes → (twist p W).IsPrime → multAt (J.map inc ⊔ Ideal.span {quad p}) (twist p W) = multAt J W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.multAt_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.multAt_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.multAt_twist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultiprojectivePointsNonempty
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem exists_ratAlgHom_complex (A : Type) [CommRing A] [Nontrivial A] [Algebra ℚ A] [Algebra.FiniteType ℚ A] :
    Nonempty (A →ₐ[ℚ] ℂ) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite ℚ (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ M)
  let κ : (A ⧸ M) →ₐ[ℚ] ℂ := IsAlgClosed.lift
  exact ⟨κ.comp (Ideal.Quotient.mkₐ ℚ M)⟩

theorem aeval_eq_zero_of_mem_mCoordIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] {x : (Σ k, ι k) → Ω} {f : MRing ι} (hf : f ∈ mCoordIdeal x) : aeval x f = 0 := by
  have h0 : mConeMap x f = 0 := hf
  have e : ((MvPolynomial.eval fun _ : K => (1 : Ω)).comp (mConeMap x).toRingHom) =
      (aeval x : MRing ι →ₐ[ℤ] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro p
      simp [mConeMap]
  have := congrArg (fun g => g f) e
  simp only [RingHom.comp_apply] at this
  have h1 : (aeval x : MRing ι →ₐ[ℤ] Ω) f = (MvPolynomial.eval fun _ : K => (1 : Ω)) ((mConeMap x) f) := this.symm
  rw [h1, h0, map_zero]

theorem mcPts_mCoordIdeal_nonempty (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (x : (Σ k, ι k) → Ω) (hx : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) : (mcPts (mCoordIdeal x)).Nonempty := by
  choose c hc using hx
  set u : Ω := ∏ k, x ⟨k, c k⟩ with hu
  have hu0 : u ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  let S : Set Ω := Set.range x ∪ {u⁻¹}
  have hS : S.Finite := (Set.finite_range x).union (Set.finite_singleton _)
  let A : Subalgebra ℚ Ω := Algebra.adjoin ℚ S
  have : Algebra.FiniteType ℚ A := Algebra.FiniteType.adjoin_of_finite hS
  obtain ⟨ρ⟩ := exists_ratAlgHom_complex A
  let xA : (Σ k, ι k) → A := fun p => ⟨x p, Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩)⟩
  let v : A := ⟨u⁻¹, Algebra.subset_adjoin (Or.inr rfl)⟩
  have huv : (∏ k, xA ⟨k, c k⟩) * v = 1 := by
    apply Subtype.ext
    have : ((∏ k, xA ⟨k, c k⟩ : A) : Ω) = u := by
      rw [hu]
      exact map_prod A.val _ _
    show ((∏ k, xA ⟨k, c k⟩ : A) : Ω) * u⁻¹ = 1
    rw [this, mul_inv_cancel₀ hu0]
  have hz : (∏ k, ρ (xA ⟨k, c k⟩)) * ρ v = 1 := by
    rw [← map_prod, ← map_mul, huv, map_one]
  refine ⟨fun p => ρ (xA p), fun k => ⟨c k, fun h0 => ?_⟩, fun f hf => ?_⟩
  · have : ∏ k, ρ (xA ⟨k, c k⟩) = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
    rw [this, zero_mul] at hz
    exact zero_ne_one hz
  · have h1 : aeval xA f = 0 := by
      apply Subtype.ext
      have e : (A.val.toRingHom.comp (aeval xA : MRing ι →ₐ[ℤ] A).toRingHom) =
          (aeval x : MRing ι →ₐ[ℤ] Ω).toRingHom := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp
        · intro p
          simp [xA]
      have := congrArg (fun g => g f) e
      simp only [RingHom.comp_apply] at this
      exact this.trans (aeval_eq_zero_of_mem_mCoordIdeal hf)
    have e : ((MvPolynomial.eval fun p => ρ (xA p)).comp (MvPolynomial.map (Int.castRingHom ℂ))) =
        ρ.toRingHom.comp (aeval xA : MRing ι →ₐ[ℤ] A).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp
      · intro p
        simp
    have := congrArg (fun g => g f) e
    simp only [RingHom.comp_apply] at this
    refine this.trans ?_
    show ρ ((aeval xA : MRing ι →ₐ[ℤ] A) f) = 0
    rw [h1, map_zero]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralUniqueEmbeddingStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_integral_unique_embedding : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (sg : F →+* ℂ), IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsConjInvariantH (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y (ComplexEmbedding.conjugate sg) z}.indicator fun _ => (1 : ℝ)) = ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.conjugate_pieces_same_mass | exact GlobalTheory.CompanionTheory.Ar.Giv.conjugate_pieces_same_mass | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.conjugate_pieces_same_mass <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ScaledCoordinatesValueAtPoint
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec

theorem isValueAt_aeval {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]
    {y' : (Σ k, ι' k) → Ω} {z : (Σ k, ι' k) → ℂ} {σ : Type} {s : σ → Ω} {w : σ → ℂ}
    (hv : ∀ q, IsValueAt y' (s q) z (w q)) (f : MvPolynomial σ ℤ) :
    IsValueAt y' (aeval s f) z (eval w (map (Int.castRingHom ℂ) f)) := by
  induction f using MvPolynomial.induction_on with
  | C n => simpa using GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_intCast y' z n
  | add p q hp hq => simpa using GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_add hp hq
  | mul_X p i hp => simpa using GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_mul hp (hv i)

theorem mem_mcPts_of_specialise : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] (a : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (z : (Σ k, ι' k) → ℂ) (zt : (Σ k, ι k) → ℂ) (e : K → Ω) (s : (Σ k, ι k) → Ω) (t : K → ℂ), z ∈ mcPts (mCoordIdeal y') → (∀ k, ∃ i, zt ⟨k, i⟩ ≠ 0) → (∀ k, e k ≠ 0) → (∀ k, t k ≠ 0) → (∀ q, a q = e q.1 * s q) → (∀ q, IsValueAt y' (s q) z (t q.1 * zt q)) → zt ∈ mcPts (mCoordIdeal a) := by
  intro K _ ι _ K' _ ι' _ Ω _ a y' z zt e s t hz hzt he ht has hv
  refine ⟨hzt, fun f hf => ?_⟩
  obtain ⟨T, hT, hE⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal a
  rw [hE] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨d, hd⟩ := hT g hg
    have h0 : aeval a g = 0 :=
      (GlobalTheory.CompanionTheory.Ar.PB.form_mem_mCoordIdeal_iff a hd).1 (by rw [hE]; exact Ideal.subset_span hg)
    have ha : a = fun p => e p.1 * s p := funext has
    have h1 : aeval s g = 0 := by
      have h := GroundTheory.Heights₂.Heights.Inter.ChartNormPts.aeval_smul_homog g d hd e s
      rw [← ha, h0] at h
      have hne : (∏ k, e k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (he k)
      exact (mul_eq_zero.1 h.symm).resolve_left hne
    have hval := isValueAt_aeval (w := fun q => t q.1 * zt q) hv g
    rw [h1] at hval
    have h2 := GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_zero hz hval
    rw [ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_homog g d hd t zt] at h2
    have hne : (∏ k, t k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k)
    exact (mul_eq_zero.1 h2).resolve_left hne
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul r x _ hx => simp [smul_eq_mul, map_mul, hx]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.Spec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SumOverEmbeddingsUnitInvarianceStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_over_embeddings_unit_invariance : ArithIntersectionSystemStatement → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (θ : (𝓞 F)ˣ), IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, IsSmoothHerm (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ∑ sg : F →+* ℂ, Real.log ‖sg ((θ : 𝓞 F) : F)‖ * ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.sum_log_unit_mul_mass_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Giv.sum_log_unit_mul_mass_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.sum_log_unit_mul_mass_eq_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHoldsStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tail_bound_statement_holds : TailBoundStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.tailBound_holds | exact GlobalTheory.CompanionTheory.Ar.Giv.tailBound_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.tailBound_holds <;> assumption)
end

