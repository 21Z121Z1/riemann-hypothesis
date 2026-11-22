import Mathlib
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
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfInjOn
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0098
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0115
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0003
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAnalyticLogResolution
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralTendstoOffDivisor
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0027
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0116
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HilbertSamuelG3OfMoriwaki
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem selfIntersection_le_of_boundedInjection :
    MoriwakiHSStatement → MoriwakiBigStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.G3.Statement :=
  fun hHS hBig =>
    GroundTheory.Heights₂.Heights.HilbertSamuel.G3.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.LocalRep.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantShift.proof
      (GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeBig.of_moriwakiBig_only hBig)
      (GlobalTheory.T.hilbert_samuel_G7_of_moriwaki hHS) GlobalTheory.T.packing'

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChart
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem exists_injective_linear {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {n : ℕ}
    (h : Module.finrank ℂ W ≤ n) : ∃ j : W →ₗ[ℂ] (Fin n → ℂ), Function.Injective j := by
  let e : W ≃ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := LinearEquiv.ofFinrankEq _ _ (by simp)
  let s : Fin (Module.finrank ℂ W) → Fin n := Fin.castLE h
  have hs : Function.Injective s := Fin.castLE_injective h
  refine ⟨(Function.ExtendByZero.linearMap ℂ s).comp e.toLinearMap, fun a b hab => e.injective ?_⟩
  funext i
  have := congrFun hab (s i)
  change Function.extend s (e a) 0 (s i) = Function.extend s (e b) 0 (s i) at this
  rwa [hs.extend_apply, hs.extend_apply] at this

theorem exists_injOn_of_strict {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {Φ : E → F} {L : E →L[ℂ] F} {w : E}
    (hΦ : HasStrictFDerivAt Φ L w) (hL : Function.Injective L) :
    ∃ B : Set E, IsOpen B ∧ w ∈ B ∧ Set.InjOn Φ B := by
  obtain ⟨N, hN, hanti⟩ := (L : E →ₗ[ℂ] F).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 hL)
  have hc : (0 : NNReal) < (2 * N)⁻¹ := by positivity
  obtain ⟨s, hs, hap⟩ := hΦ.approximates_deriv_on_nhds (c := (2 * N)⁻¹) (Or.inr hc)
  obtain ⟨B, hBs, hB, hwB⟩ := mem_nhds_iff.1 hs
  refine ⟨B, hB, hwB, fun u hu v hv huv => ?_⟩
  have h1 := hap u (hBs hu) v (hBs hv)
  rw [huv, sub_self, zero_sub, norm_neg] at h1
  have h2 : ‖u - v‖ ≤ N * ‖L (u - v)‖ := by
    have := hanti.le_mul_dist (u - v) 0
    simpa [dist_eq_norm] using this
  by_contra hne
  have hpos : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : ‖u - v‖ ≤ N * (((2 * N)⁻¹ : NNReal) * ‖u - v‖) :=
    h2.trans (mul_le_mul_of_nonneg_left h1 hN'.le)
  have h4 : (N : ℝ) * (((2 * N)⁻¹ : NNReal) * ‖u - v‖) = ‖u - v‖ / 2 := by
    push_cast
    field_simp
  rw [h4] at h3
  linarith

theorem exists_linear_separation {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (n : ℕ)
    (hcard : Fintype.card σ ≤ Module.finrank ℂ (ReciprocityTheory.AnForm.R.jacSpanAt I w) + n) :
    ∃ (π : (σ → ℂ) →L[ℂ] (Fin n → ℂ)) (B : Set (σ → ℂ)), IsOpen B ∧ w ∈ B ∧
      ∀ u ∈ B, ∀ v ∈ B, (∀ h ∈ I, eval u h = 0) → (∀ h ∈ I, eval v h = 0) → π u = π v → u = v := by
  classical
  set S : Set (σ → ℂ) := (fun h : MvPolynomial σ ℂ => fun j => eval w (pderiv j h)) '' (I : Set _) with hS
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℂ S
  have hbfin : b.Finite := hli.setFinite
  haveI : Fintype b := hbfin.fintype
  have hex : ∀ t : b, ∃ f ∈ I, (fun j => eval w (pderiv j f)) = (t : σ → ℂ) := fun t => by
    obtain ⟨f, hf, h⟩ := hbS t.2
    exact ⟨f, hf, h⟩
  choose F hFI hFg using hex
  let M : Matrix b σ ℂ := fun t q => (t : σ → ℂ) q
  have hrank : M.rank = Module.finrank ℂ (ReciprocityTheory.AnForm.R.jacSpanAt I w) := by
    rw [Matrix.rank_eq_finrank_span_row]
    have : Set.range M.row = b := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact t.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [this, hspan]
    rfl
  let W : Submodule ℂ (σ → ℂ) := LinearMap.ker M.mulVecLin
  have hW : Module.finrank ℂ W ≤ n := by
    have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have h' : Module.finrank ℂ (LinearMap.range M.mulVecLin) = M.rank := rfl
    simp only [Module.finrank_fintype_fun_eq_card] at h
    show Module.finrank ℂ (LinearMap.ker M.mulVecLin) ≤ n
    omega
  obtain ⟨j, hj⟩ := exists_injective_linear hW
  obtain ⟨l, hl⟩ := W.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype W)
  let π : (σ → ℂ) →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap (j.comp l)
  let Φ : (σ → ℂ) → (b → ℂ) × (Fin n → ℂ) := fun x => (fun t => eval x (F t), π x)
  let L0 : (σ → ℂ) →L[ℂ] (b → ℂ) := ContinuousLinearMap.pi fun t => polyDiff (F t) w
  have hd : HasStrictFDerivAt Φ (L0.prod π) w :=
    (hasStrictFDerivAt_pi.2 fun t => hasStrictFDerivAt_eval_poly (F t) w).prodMk π.hasStrictFDerivAt
  have hinj : Function.Injective (L0.prod π) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    have h1 : L0 v = 0 := congrArg Prod.fst hv
    have h2 : π v = 0 := congrArg Prod.snd hv
    have hvW : v ∈ W := by
      show M.mulVecLin v = 0
      funext t
      have h3 := congrFun h1 t
      have h4 : polyDiff (F t) w v = 0 := h3
      rw [polyDiff_apply] at h4
      have h5 : ∀ q, eval w (pderiv q (F t)) = (t : σ → ℂ) q := fun q => congrFun (hFg t) q
      simp only [h5] at h4
      show ∑ q, (t : σ → ℂ) q * v q = 0
      exact h4
    have h6 : j (l v) = 0 := h2
    have h7 : l v = 0 := hj (by rw [h6, map_zero])
    have h8 : l (W.subtype ⟨v, hvW⟩) = ⟨v, hvW⟩ := LinearMap.congr_fun hl _
    have h9 : (⟨v, hvW⟩ : W) = 0 := by rw [← h8]; exact h7
    exact congrArg Subtype.val h9
  obtain ⟨B, hB, hwB, hBinj⟩ := exists_injOn_of_strict hd hinj
  refine ⟨π, B, hB, hwB, fun u hu v hv hIu hIv huv => hBinj hu hv ?_⟩
  refine Prod.ext (funext fun t => ?_) huv
  show eval u (F t) = eval v (F t)
  rw [hIu _ (hFI t), hIv _ (hFI t)]

theorem localOrbitChart : LocalOrbitChart.Statement := by
  intro K _ ι _ Ω _ inst y n hP hsm z₀ hz₀
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) :=
    isMultiHomogIdeal_pC hP.2.1.2.1
  obtain ⟨p, hp, -⟩ := ReciprocityTheory.AnForm.R.exists_chart z₀ hz₀.1
  have hy : ∀ k, y ⟨k, p k⟩ ≠ 0 := by
    intro k h0
    have hX : (X ⟨k, p k⟩ : MRing ι) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0]
      simp
    have h1 := hz₀.2 _ hX
    rw [map_X, eval_X] at h1
    exact hp k h1
  have hzero : ∀ z ∈ mcPts (mCoordIdeal y), (∀ k, z ⟨k, p k⟩ ≠ 0) →
      ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p,
        eval (ReciprocityTheory.AnForm.R.affCoord p z) h = 0 := fun z hz hzp =>
    (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPh p z hzp).1 ((mem_mcPts_iff_conePts_pC _ _).1 hz)
  have hrank := GlobalTheory.CompanionTheory.Ar.PB.SmoothMan.card_le_finrank_jacSpanAt K ι Ω y n hP hsm p hy
    (ReciprocityTheory.AnForm.R.affCoord p z₀) (hzero z₀ hz₀ hp)
  obtain ⟨π, B, hB, hwB, hsep⟩ := exists_linear_separation _ _ n hrank
  let D : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, z ⟨k, p k⟩ ≠ 0}
  have hDopen : IsOpen D := by
    have : D = ⋂ k, {z | z ⟨k, p k⟩ ≠ 0} := by ext z; simp [D]
    rw [this]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have han : ∀ z ∈ D, AnalyticAt ℂ (ReciprocityTheory.AnForm.R.affCoord p) z := by
    intro z hz
    refine analyticAt_pi_iff.2 fun q => ?_
    have hc : ∀ r : Σ k, ι k, AnalyticAt ℂ (fun v : (Σ k, ι k) → ℂ => v r) z := fun r =>
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) r).analyticAt z
    exact (hc q).div (hc ⟨q.1, p q.1⟩) (hz q.1)
  have hcont : ContinuousOn (ReciprocityTheory.AnForm.R.affCoord p) D := fun z hz =>
    (han z hz).continuousAt.continuousWithinAt
  refine ⟨D ∩ ReciprocityTheory.AnForm.R.affCoord p ⁻¹' B, hcont.isOpen_inter_preimage hDopen hB, ⟨hp, hwB⟩,
    fun z => π (ReciprocityTheory.AnForm.R.affCoord p z), ?_, ?_, ?_⟩
  · intro z hz
    exact (π.analyticAt _).comp (han z hz.1)
  · intro z hz c hc
    have hA : ReciprocityTheory.AnForm.R.affCoord p (torusSmul c z) = ReciprocityTheory.AnForm.R.affCoord p z :=
      ReciprocityTheory.AnForm.R.affCoord_eq_of_sameOrbit p ⟨c, hc, rfl⟩
    refine ⟨⟨fun k => mul_ne_zero (hc k) (hz.1 k), ?_⟩, ?_⟩
    · show ReciprocityTheory.AnForm.R.affCoord p (torusSmul c z) ∈ B
      rw [hA]
      exact hz.2
    · show π _ = π _
      rw [hA]
  · rintro z ⟨hzN, hzX⟩ z' ⟨hzN', hzX'⟩ hκ
    have hA := hsep _ hzN.2 _ hzN'.2 (hzero z hzX hzN.1) (hzero z' hzX' hzN'.1) hκ
    refine ⟨fun k => z' ⟨k, p k⟩ / z ⟨k, p k⟩, fun k => div_ne_zero (hzN'.1 k) (hzN.1 k), ?_⟩
    funext q
    have h1 : z q / z ⟨q.1, p q.1⟩ = z' q / z' ⟨q.1, p q.1⟩ := congrFun hA q
    have h2 := hzN.1 q.1
    have h3 := hzN'.1 q.1
    show z' q = z' ⟨q.1, p q.1⟩ / z ⟨q.1, p q.1⟩ * z q
    rw [div_mul_eq_mul_div, eq_div_iff h2]
    rw [div_eq_div_iff h2 h3] at h1
    linear_combination -h1

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFromOrbitChartsStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_resolution_from_orbit_charts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ), Nonempty K → IsMultiHomogIdeal P → ¬ (⊤ : Ideal (MRing ι)) ≤ P → (∀ z ∈ mcPts P, ∃ C : OrbitChart P e, z ∈ C.O) → ∃ R : AnLogRes P ⊤ e, ∀ C : OrbitChart P e, (mcPts P).Nonempty → ∃ ψ : OpenPartialHomeomorph R.X (Fin e → ℂ), IsCompatChart R.A ψ ∧ ψ.target = C.D ∧ (∀ x, x ∈ ψ.source ↔ R.lift x x ∈ C.O) ∧ ∀ x ∈ ψ.source, SameOrbit (C.φ (ψ x)) (R.lift x x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen.exists_anLogRes_of_orbitCharts | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen.exists_anLogRes_of_orbitCharts | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen.exists_anLogRes_of_orbitCharts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralTendstoOffDivisorStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_integral_tendsto_off_divisor : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (Θ : LocPot X), IsPotential A Θ → IsPosPot A Θ → ∀ (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (fT : Fin e → ℝ → X → ℝ) (G : X → ℝ) (GT : ℝ → X → ℝ) (C : ℝ), (∀ i, IsPotential A (P i)) → (∀ i, A.SmoothOn R.Yo (f i)) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, A.Smooth (fT i t) ∧ IsPsh A (P i + LocPot.ofFun (fT i t) + Θ) ∧ ∀ x ∈ R.Yo, |fT i t x| ≤ C + C * Real.log (R.r x) ∧ fT i t x ≤ C) → (∀ i, ∀ j, ∀ K' ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => fT i t ∘ (A.chart j).symm) (f i ∘ (A.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fT i t ∘ (A.chart j).symm)) (fderiv ℝ (f i ∘ (A.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (fT i t ∘ (A.chart j).symm))) (fderiv ℝ (fderiv ℝ (f i ∘ (A.chart j).symm))) (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), @Measurable X ℝ (borel X) _ (R.Yo.indicator (GT t)) ∧ ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x)) → (∀ K' ⊆ R.Yo, IsCompact K' → TendstoUniformlyOn GT G (𝓝[>] 0) K') → MIntegrable A (fun i => P i + LocPot.ofFun (f i)) G ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable A (fun i => P i + LocPot.ofFun (fT i t)) (GT t)) ∧ Tendsto (fun t => mInt A (fun i => P i + LocPot.ofFun (fT i t)) (GT t)) (𝓝[>] 0) (𝓝 (mInt A (fun i => P i + LocPot.ofFun (f i)) G)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.mixed_integral_tendsto_of_C2_off_divisor | exact GlobalTheory.CompanionTheory.Ar.Giv.mixed_integral_tendsto_of_C2_off_divisor | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.mixed_integral_tendsto_of_C2_off_divisor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralIndependentOfMetricStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_integral_independent_of_metric : ArithIntersectionSystemStatement → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L L' : Fin D → HermLine ι) (sg : F →+* ℂ), IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) → (∀ j, (L j).a = (L' j).a) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) = ptsIntegral (mCoordIdeal y) (pot L') ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.mass_eq_of_degrees | exact GlobalTheory.CompanionTheory.Ar.Giv.mass_eq_of_degrees | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.mass_eq_of_degrees <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjChartSetEqSetChartSet
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

section Defs

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def setChartSet (S : Set ((Σ k, ι k) → ℂ)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, Ψ (segre z) 0 = 1 ∧ x = fun a => segre z (σ a)}

def setChartIdeal (S : Set ((Σ k, ι k) → ℂ)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Ideal (MvPolynomial (Fin m) ℂ) :=
  vanishingIdeal ℂ (setChartSet S σ Ψ)

def setSegChartSet (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, segre z i = 1 ∧ x = fun a => segre z (σ a)}

def setSegChartIdeal (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Ideal (MvPolynomial (Fin m) ℂ) :=
  vanishingIdeal ℂ (setSegChartSet S σ i)

def setSegreCone (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, x = fun a => segre z (σ a)}

theorem isMultiHomogIdeal_toR {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal Q) :
    ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ

theorem cone_scale {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) : (fun p => c p.1 * z p) ∈ conePts Q := by
  refine ⟨fun k => ?_, ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hQ c z hz.2⟩
  obtain ⟨i, hi⟩ := hz.1 k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem exists_segre_smul {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    [Nonempty K] {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) {c : ℂ} (hc : c ≠ 0) :
    ∃ z' ∈ conePts Q, segre z' = c • segre z := by
  classical
  obtain ⟨k0⟩ := ‹Nonempty K›
  refine ⟨_, cone_scale hQ (c := fun k => if k = k0 then c else 1) (fun k => ?_) hz, ?_⟩
  · split_ifs
    · exact hc
    · exact one_ne_zero
  · exact GoodChartZeroSet.segre_scaleBlock k0 c z

end Defs

section ZeroSet

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def liftPolyC [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (f : MRingOver ℂ ι) : MvPolynomial (Fin m) ℂ :=
  aeval (fun p : Σ k, ι k => (X (σ.symm (Function.update i p.1 p.2)) : MvPolynomial (Fin m) ℂ)) f

theorem eval_liftPolyC [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (x : Fin m → ℂ) (f : MRingOver ℂ ι) :
    eval x (liftPolyC σ i f) = eval (chartLift σ i x) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [liftPolyC]
  | add f g hf hg =>
    simp only [liftPolyC, map_add] at hf hg ⊢
    rw [hf, hg]
  | mul_X f q hf =>
    simp only [liftPolyC, map_mul] at hf ⊢
    rw [hf]
    simp [chartLift]

theorem segChart_zeroSet {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) {m : ℕ}
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    zeroSet (setSegChartIdeal (conePts Q) σ i) = setSegChartSet (conePts Q) σ i := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ setSegChartSet (conePts Q) σ i, eval y q = 0) →
        eval x q = 0 :=
      fun q hq => hx q (by rw [setSegChartIdeal, mem_vanishingIdeal_iff]; exact hq)
    have ha : x (σ.symm i) = 1 := by
      have h := hv (X (σ.symm i) - 1) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        simp [hzi])
      rw [map_sub, eval_X, map_one] at h
      exact sub_eq_zero.1 h
    have hb : ∀ i' : (k : K) → ι k,
        x (σ.symm i') = ∏ k, x (σ.symm (Function.update i k (i' k))) := by
      intro i'
      have h := hv (X (σ.symm i') - ∏ k, X (σ.symm (Function.update i k (i' k)))) (by
        rintro _ ⟨z, -, hzi, rfl⟩
        have hs : ∏ k, segre z (Function.update i k (i' k)) = segre z i' := by
          have h1 := congrFun (segre_chartLift σ i z hzi) i'
          simpa [ReciprocityTheory.ChartRestriction.G.Geo.segre, chartLift] using h1
        rw [map_sub, eval_X, map_prod]
        simp only [eval_X, Equiv.apply_symm_apply]
        rw [hs, sub_self])
      rw [map_sub, eval_X, map_prod] at h
      simp only [eval_X] at h
      exact sub_eq_zero.1 h
    have hc : ∀ f ∈ Q, eval (chartLift σ i x) f = 0 := by
      intro f hf
      rw [← eval_liftPolyC]
      refine hv _ ?_
      rintro _ ⟨z, hz, hzi, rfl⟩
      rw [eval_liftPolyC]
      have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
        have h1 : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
        rw [hzi] at h1
        exact one_ne_zero h1
      have hcl : chartLift σ i (fun a => segre z (σ a)) = fun p => (z ⟨p.1, i p.1⟩)⁻¹ * z p := by
        funext ⟨k, j⟩
        rw [chartLift_segre_apply σ i z hzi, mul_comm]
      rw [hcl]
      exact (cone_scale hQ (c := fun k => (z ⟨k, i k⟩)⁻¹) (fun k => inv_ne_zero (hne k)) hz).2 f hf
    refine ⟨chartLift σ i x, ⟨chartLift_blockNonzero σ i ha, hc⟩, ?_, ?_⟩
    · show ∏ k, chartLift σ i x ⟨k, i k⟩ = 1
      simp [chartLift, ha]
    · funext a
      show x a = ∏ k, chartLift σ i x ⟨k, σ a k⟩
      simp only [chartLift]
      rw [← hb, Equiv.symm_apply_apply]
  · intro x hx q hq
    rw [setSegChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx

theorem chart_zeroSet {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) [Nonempty K]
    {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    zeroSet (setChartIdeal (conePts Q) σ Ψ) = setChartSet (conePts Q) σ Ψ := by
  classical
  apply Set.Subset.antisymm
  swap
  · intro x hx q hq
    rw [setChartIdeal, mem_vanishingIdeal_iff] at hq
    exact hq x hx
  intro x hx
  have hv : ∀ q : MvPolynomial (Fin m) ℂ, (∀ y ∈ setChartSet (conePts Q) σ Ψ, eval y q = 0) → eval x q = 0 :=
    fun q hq => hx q (by rw [setChartIdeal, mem_vanishingIdeal_iff]; exact hq)
  have hseg : ∀ z : (Σ k, ι k) → ℂ, (fun i' => segre z (σ (σ.symm i'))) = segre z := fun z => by
    funext i'; rw [Equiv.apply_symm_apply]

  have hx1 : Ψ (fun i' => x (σ.symm i')) 0 = 1 := by
    have h := hv (GoodChartZeroSet.linForm σ Ψ - 1) (by
      rintro _ ⟨z, -, hz1, rfl⟩
      rw [map_sub, GoodChartZeroSet.eval_linForm, map_one, hseg, hz1, sub_self])
    rw [map_sub, GoodChartZeroSet.eval_linForm, map_one] at h
    exact sub_eq_zero.1 h
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    have h0 : (fun i' => x (σ.symm i')) = 0 := funext fun i' => h _
    rw [h0, map_zero] at hx1
    exact zero_ne_one hx1

  have hzero : (x a)⁻¹ • x ∈ zeroSet (setSegChartIdeal (conePts Q) σ (σ a)) := by
    intro f hf
    rw [setSegChartIdeal, mem_vanishingIdeal_iff] at hf
    have hg := hv (X a * ∑ d ∈ Finset.range (f.totalDegree + 1),
        X a ^ (f.totalDegree - d) * homogeneousComponent d f) (by
      rintro _ ⟨z, hz, -, rfl⟩
      by_cases h0 : segre z (σ a) = 0
      · simp [h0]
      · rw [GoodChartZeroSet.eval_homogenize f le_rfl a _ h0]
        obtain ⟨z', hz', hz'e⟩ := exists_segre_smul hQ hz (inv_ne_zero h0)
        refine mul_eq_zero_of_right _ (hf _ ⟨z', hz', ?_, ?_⟩)
        · rw [hz'e, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ h0]
        · funext b
          rw [hz'e]
          rfl)
    rw [GoodChartZeroSet.eval_homogenize f le_rfl a x ha] at hg
    exact (mul_eq_zero.1 hg).resolve_left (pow_ne_zero _ ha)
  rw [segChart_zeroSet hQ σ (σ a)] at hzero
  obtain ⟨z', hz', -, hz'e⟩ := hzero
  obtain ⟨z, hz, hze⟩ := exists_segre_smul hQ hz' ha
  have hxz : x = fun b => segre z (σ b) := by
    funext b
    have hb := congrFun hz'e b
    simp only [Pi.smul_apply, smul_eq_mul] at hb
    rw [hze, Pi.smul_apply, smul_eq_mul, ← hb, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  refine ⟨z, hz, ?_, hxz⟩
  rw [← hseg z, ← hx1, hxz]

end ZeroSet

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartRegularWithBoundaryChoiceStatement
section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_chart_regular_with_boundary_choice : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (x : SncRes.Pts P) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)) (σ : Fin e → Option (Fin (SncRes.rc P D))), IsMultiHomogIdeal P → IsMultiHomogIdeal D → x ∈ SncRes.src P p → (∀ h ∈ (SncRes.ideal P p), eval (SncRes.coord P p x) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (SncRes.coord P p x)) → ringKrullDim (locRing (SncRes.ideal P p) (SncRes.coord P p x)) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (SncRes.coord P p x)) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (SncRes.coord P p x))) (ptIdeal (SncRes.coord P p x)) → (∀ l, σ l = none ↔ l ∉ Jf) → (∀ l k, σ l = some k → SncRes.ideal (SncRes.compIdeal P D k) p = SncRes.Par.chPrime (SncRes.ideal P p) (SncRes.coord P p x) (r l)) → (∀ k, (∀ g ∈ SncRes.compIdeal P D k, eval (SncRes.rep x) g = 0) → ∃ l ∈ Jf, σ l = some k) → ∃ O : Set (SncRes.Pts P), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src P p ∧ ∀ k, SncRes.comp P D k ∩ O = {x' ∈ O | ∃ l, σ l = some k ∧ eval (SncRes.coord P p x') (r l) = 0} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp.comp_eq_near | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp.comp_eq_near | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.NearComp.comp_eq_near <;> assumption)
end

