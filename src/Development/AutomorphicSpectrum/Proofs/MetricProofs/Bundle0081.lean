import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0044
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0013
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XNefCurve
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
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

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ]

def tauAt (ha : a ≤ n) (T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (w : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  T0 (expCover a w) + ∑ j, (w (Fin.castLE ha j) / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))

structure IsChart (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ)
    (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ) : Prop where
  form : ∀ i j, L.E (bas (.inl i)) (bas (.inl j)) = 0 ∧ L.E (bas (.inr i)) (bas (.inr j)) = 0 ∧
    L.E (bas (.inl i)) (bas (.inr j)) = if i = j then -1 else 0
  A_cont : ContinuousOn A (Metric.ball 0 1)
  A_det : (A 0).det ≠ 0
  T_cont : ContinuousOn T0 (Metric.ball 0 1)
  B_psd : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef
  c_pos : 0 < c
  ρ_pos : 0 < ρ
  ρ_le : ρ ≤ 1
  im_lower : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ l : Fin a → ℂ,
    (∀ j, Complex.exp (l j) = z (Fin.castLE L.a_le j)) →
    ((T0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map
      Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef
  sym : ∀ w ∈ logCover L.a_le, (tauAt L.a_le T0 B w)ᵀ = tauAt L.a_le T0 B w
  im_pos : ∀ w ∈ logCover L.a_le, ((tauAt L.a_le T0 B w).map Complex.im).PosDef
  per : ∀ w ∈ logCover L.a_le, ∀ x, L.P w x =
    (A (expCover a w))ᵀ *ᵥ (cst (uCo bas x) + tauAt L.a_le T0 B w *ᵥ cst (vCo bas x))

theorem exists_isChart (L : Flat.LogPeriods n a g Λ) : ∃ bas A T0 B c ρ, IsChart L bas A T0 B c ρ := by
  obtain ⟨bas, Q, A, T0, hE, hAd, hA0, hT0, hBpsd, hPa, hPb⟩ := GlobalTheory.T.symplectic_polydisc_period_basis n a g Λ L
  obtain ⟨ρ₁, c, C₁, hρ₁, hρ₁1, hc, hb⟩ :=
    (ImTauBounds.cond RiemannExtensionSlices.proof PuncturedExpOrder.proof LogCoverDescent.proof) n a g Q
  have hAc : ContinuousOn A (Metric.ball 0 1) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hAd i j).continuousOn
  have hTc : ContinuousOn T0 (Metric.ball 0 1) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hT0.1 i j).continuousOn
  have hQa : Q.a_le = L.a_le := rfl
  have hτ : ∀ w ∈ logCover L.a_le, Q.τ w = tauAt L.a_le T0 Q.B w := by
    intro w hw
    have h := hT0.2 w hw
    simp only [PeriodPolydisc.tau0] at h
    simp only [tauAt]
    rw [← h]
    exact (sub_add_cancel _ _).symm
  refine ⟨bas, A, T0, Q.B, c, ρ₁, hE, hAc, hA0, hTc, hBpsd, hc, hρ₁, hρ₁1.le, ?_, ?_, ?_, ?_⟩
  · intro z hz l hl
    have hz1 : ∀ k, ‖z k‖ < 1 := fun k =>
      lt_of_le_of_lt (norm_le_pi_norm z k)
        (lt_trans (by simpa [dist_zero_right] using hz) hρ₁1)
    let w : Fin n → ℂ := fun k => if h : k.val < a then l ⟨k.val, h⟩ else z k
    have hwj : ∀ j : Fin a, w (Fin.castLE L.a_le j) = l j := by
      intro j
      have hj : (Fin.castLE L.a_le j).val < a := j.2
      simp [w, hj]
    have hexp : expCover a w = z := by
      funext k
      by_cases hk : k.val < a
      · have := hl ⟨k.val, hk⟩
        simp only [expCover, hk, if_true, w, dif_pos]
        rw [this]
        rfl
      · simp [expCover, hk, w]
    have hw : w ∈ logCover L.a_le := by
      refine ⟨fun i => ?_, fun k hk => ?_⟩
      · rw [hwj]
        have h1 : ‖Complex.exp (l i)‖ < 1 := by rw [hl i]; exact hz1 _
        rw [Complex.norm_exp] at h1
        exact Real.exp_lt_one_iff.1 h1
      · have hk' : ¬ k.val < a := not_lt.2 hk
        simp only [w, hk', dif_neg, not_false_eq_true]
        exact hz1 k
    have h1 := (hb w hw (by rw [hexp]; exact Metric.ball_subset_closedBall hz)).1
    rw [hτ w hw] at h1
    simp only [tauAt, hexp, hwj] at h1
    exact h1
  · intro w hw
    rw [← hτ w hw]
    exact Q.symm w hw
  · intro w hw
    rw [← hτ w hw]
    exact Q.im_posDef w hw
  · intro w hw x
    rw [← hτ w hw]
    exact per_coords bas (L.P w) (Q.τ w) (A (expCover a w)) (Q.symm w hw) (hPa w hw) (hPb w hw) x

def chartS (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (x : Λ)
    (z : Fin n → ℂ) : Fin g → ℂ :=
  (A z)ᵀ *ᵥ (cst (uCo bas x) + T0 z *ᵥ cst (vCo bas x))

def chartW (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) : Submodule ℤ Λ :=
  LinearMap.ker ((∑ j, B j).mulVecLin ∘ₗ vCo bas)

def chartPer (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) : chartW bas B →+ (Fin g → ℂ) :=
  AddMonoidHom.mk' (fun x => chartS bas A T0 (x : Λ) 0) (fun x y => by
    simp only [chartS, Submodule.coe_add, map_add, cst_add, mulVec_add]
    abel_nf)

def IsKerProj (S : Matrix (Fin g) (Fin g) ℤ) (Pr : Matrix (Fin g) (Fin g) ℝ) : Prop :=
  Pr * Pr = Pr ∧ Prᵀ = Pr ∧ ∀ v : Fin g → ℝ, S.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 ↔ Pr *ᵥ v = v

def compInv (Pr Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g) (Fin g) ℝ :=
  Pr * (Pr * Y * Pr + (1 - Pr))⁻¹ * Pr

def chartQ (Pr : Matrix (Fin g) (Fin g) ℝ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (z : Fin n → ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (A z)⁻¹ * (compInv Pr ((T0 z).map Complex.im)).map (fun x : ℝ => (x : ℂ)) * ((A z)ᴴ)⁻¹

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FixedMemberBase
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem epsT_small (C : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ t, 0 < t → t ≤ a → |epsT C t| ≤ 1 / 2 ∧ C * epsT C t ≤ 1 := by
  have hL : Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] 0) atTop := by
    have hinv : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop := by
      first | exact tendsto_inv_nhdsGT_zero | exact tendsto_inv_zero_atTop
    exact (Real.tendsto_log_atTop.comp hinv).congr fun t => by simp [one_div]
  have hq : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have he : Tendsto (fun t => epsT C t) (𝓝[>] 0) (𝓝 0) := by
    have h := (hq.comp hL).const_mul C
    rw [mul_zero] at h
    refine h.congr fun t => ?_
    simp only [Function.comp, epsT]
    ring
  have ha : ∀ᶠ t in 𝓝[>] (0:ℝ), |epsT C t| < 1 / 2 := by
    have h := he.abs
    rw [abs_zero] at h
    exact h.eventually (gt_mem_nhds (by norm_num))
  have hb : ∀ᶠ t in 𝓝[>] (0:ℝ), C * epsT C t < 1 := by
    have h := he.const_mul C
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨u, hu, hsub⟩ : ∃ u ∈ Set.Ioi (0:ℝ), Set.Ioc 0 u ⊆ {t | |epsT C t| < 1 / 2 ∧ C * epsT C t < 1} := by
    first | exact mem_nhdsGT_iff_exists_Ioc_subset.mp (ha.and hb) | exact mem_nhdsWithin_Ioi_iff_exists_Ioc_subset.mp (ha.and hb)
  refine ⟨u, hu, fun t ht htu => ?_⟩
  obtain ⟨h1, h2⟩ := hsub ⟨ht, htu⟩
  exact ⟨h1.le, h2.le⟩

private theorem contDiffAt_comp_chart_symm_of_smoothOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (U : Set X) (f : X → ℝ) (hU : IsOpen U) (hf : A.SmoothOn U f) (j : Fin A.n) (y : Fin e → ℂ)
    (hy : y ∈ (A.chart j).target) (hyU : (A.chart j).symm y ∈ U) :
    ContDiffAt ℝ 2 (f ∘ (A.chart j).symm) y := by
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target hU
  refine ((hf j).contDiffAt (hopen.mem_nhds ⟨hy, hyU⟩)).of_le ?_
  first | exact_mod_cast (le_top : ((2 : ℕ∞)) ≤ ⊤) | simp | decide

private theorem levi_add_mul {ι : Type} [Fintype ι] (F G : (ι → ℂ) → ℝ) (y w : ι → ℂ) (k : ℝ)
    (hF : ContDiffAt ℝ 2 F y) (hG : ContDiffAt ℝ 2 G y) :
    levi (fun z => F z + k * G z) y w = levi F y w + k * levi G y w := by
  have hF1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ F z :=
    (hF.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hG1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ G z :=
    (hG.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hD : (fderiv ℝ fun z => F z + k * G z) =ᶠ[𝓝 y] fun z => fderiv ℝ F z + k • fderiv ℝ G z := by
    filter_upwards [hF1, hG1] with z hz1 hz2
    exact (hz1.hasFDerivAt.add (hz2.hasFDerivAt.const_mul k)).fderiv
  have hF2 : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG2 : DifferentiableAt ℝ (fderiv ℝ G) y :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ fun z => F z + k * G z) y =
      fderiv ℝ (fderiv ℝ F) y + k • fderiv ℝ (fderiv ℝ G) y := by
    rw [hD.fderiv_eq]
    exact (hF2.hasFDerivAt.add (hG2.hasFDerivAt.const_smul k)).fderiv
  unfold levi
  rw [h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem levi_split {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ th : LocPot X)
    (u : X → ℝ) (hΘ : IsPotential A Θ) (hth : IsPotential A th) (hu : A.Smooth u) (ε c : ℝ) (x : X)
    (j : Fin A.n) (y : Fin e → ℂ) (hy : y ∈ (A.chart j).target)
    (h1 : (A.chart j).symm y ∈ th.U x) (h2 : (A.chart j).symm y ∈ Θ.U x) (w : Fin e → ℂ) :
    levi (fun z => th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) +
        c * Θ.φ x ((A.chart j).symm z)) y w =
      levi ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) y w +
        (c - ε) * levi (Θ.φ x ∘ (A.chart j).symm) y w := by
  have hthC := contDiffAt_comp_chart_symm_of_smoothOn A (th.U x) (th.φ x) (th.isOpen_U x) (hth.1 x) j y hy h1
  have hΘC := contDiffAt_comp_chart_symm_of_smoothOn A (Θ.U x) (Θ.φ x) (Θ.isOpen_U x) (hΘ.1 x) j y hy h2
  have huC := contDiffAt_comp_chart_symm_of_smoothOn A Set.univ u isOpen_univ hu j y hy trivial
  have hPC : ContDiffAt ℝ 2 ((th + LocPot.ofFun u + Θ.rsmul ε).φ x ∘ (A.chart j).symm) y :=
    (hthC.add huC).add (contDiffAt_const.mul hΘC)
  rw [← levi_add_mul _ _ y w (c - ε) hPC hΘC]
  congr 1
  funext z
  show _ = th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) + ε * Θ.φ x ((A.chart j).symm z) +
    (c - ε) * Θ.φ x ((A.chart j).symm z)
  ring

private theorem levi_sub_const' {ι : Type} [Fintype ι] (g : (ι → ℂ) → ℝ) (a : ℝ) (y w : ι → ℂ) :
    levi (fun z => g z - a) y w = levi g y w := by
  have h : fderiv ℝ (fun z => g z - a) = fderiv ℝ g := by
    funext z
    by_cases hg : DifferentiableAt ℝ g z
    · exact (hg.hasFDerivAt.sub_const a).fderiv
    · have hg' : ¬ DifferentiableAt ℝ (fun z => g z - a) z := fun h => hg (by simpa using h.add_const a)
      rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt hg']
  unfold levi
  rw [h]

private theorem levi_zero' {ι : Type} [Fintype ι] (g : (ι → ℂ) → ℝ) (y : ι → ℂ) : levi g y 0 = 0 := by
  unfold levi
  simp

theorem isPsh_of_le {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ th : LocPot X) (u : X → ℝ) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ)
    (hth : IsPotential A th) (hu : A.Smooth u) (ε c a : ℝ) (hεc : ε ≤ c)
    (hP : IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε)) (Q : LocPot X)
    (hU : ∀ x, Q.U x ⊆ th.U x ∩ Θ.U x)
    (hφ : ∀ x z, Q.φ x z = th.φ x z + u z + c * Θ.φ x z - a) : IsPsh A Q := by
  intro x j y hy w
  obtain ⟨hyt, hyQ⟩ := hy
  have hsub := hU x hyQ
  have hfun : Q.φ x ∘ (A.chart j).symm = fun z => (th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) +
      c * Θ.φ x ((A.chart j).symm z)) - a := by
    funext z
    simp only [Function.comp_apply, hφ]
  rw [hfun, levi_sub_const' (fun z => th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) +
      c * Θ.φ x ((A.chart j).symm z)) a y w,
    levi_split A Θ th u hΘ hth hu ε c x j y hyt hsub.1 hsub.2 w]
  have hmem : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (th + LocPot.ofFun u + Θ.rsmul ε).U x := by
    refine ⟨hyt, ?_⟩
    show (A.chart j).symm y ∈ th.U x ∩ Set.univ ∩ Θ.U x
    exact ⟨⟨hsub.1, trivial⟩, hsub.2⟩
  have hPs := hP x j y hmem w
  rcases eq_or_ne w 0 with rfl | hw
  · simp [levi_zero']
  · have hΘp := hpos x j y ⟨hyt, hsub.2⟩ w hw
    have hce : 0 ≤ c - ε := sub_nonneg.mpr hεc
    nlinarith

theorem isPosPot_of_lt {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ th : LocPot X) (u : X → ℝ) (hΘ : IsPotential A Θ) (hpos : IsPosPot A Θ)
    (hth : IsPotential A th) (hu : A.Smooth u) (ε c : ℝ) (hεc : ε < c)
    (hP : IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε)) (Q : LocPot X)
    (hU : ∀ x, Q.U x ⊆ th.U x ∩ Θ.U x)
    (hφ : ∀ x z, Q.φ x z = th.φ x z + u z + c * Θ.φ x z) : IsPosPot A Q := by
  intro x j y hy w hw
  obtain ⟨hyt, hyQ⟩ := hy
  have hsub := hU x hyQ
  have hfun : Q.φ x ∘ (A.chart j).symm = fun z => th.φ x ((A.chart j).symm z) + u ((A.chart j).symm z) +
      c * Θ.φ x ((A.chart j).symm z) := by
    funext z
    simp only [Function.comp_apply, hφ]
  rw [hfun, levi_split A Θ th u hΘ hth hu ε c x j y hyt hsub.1 hsub.2 w]
  have hmem : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (th + LocPot.ofFun u + Θ.rsmul ε).U x := by
    refine ⟨hyt, ?_⟩
    show (A.chart j).symm y ∈ th.U x ∩ Set.univ ∩ Θ.U x
    exact ⟨⟨hsub.1, trivial⟩, hsub.2⟩
  have hPs := hP x j y hmem w
  have hΘp := hpos x j y ⟨hyt, hsub.2⟩ w hw
  have hce : 0 < c - ε := sub_pos.mpr hεc
  nlinarith

private theorem isPotential_add' {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P Q : LocPot X) (hP : IsPotential A P) (hQ : IsPotential A Q) : IsPotential A (P + Q) := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · show ContDiffOn ℝ _ (fun z => P.φ x ((A.chart j).symm z) + Q.φ x ((A.chart j).symm z))
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U x ∩ Q.U x))
    exact ((hP.1 x j).mono fun z (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U x ∩ Q.U x)) =>
      ⟨hz.1, hz.2.1⟩).add ((hQ.1 x j).mono fun z
        (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (P.U x ∩ Q.U x)) => ⟨hz.1, hz.2.2⟩)
  · obtain ⟨⟨hPx, hQx⟩, hPx', hQx'⟩ := hy
    obtain ⟨W1, hW1o, hyW1, G1, hG1, hd1⟩ := hP.2 x x' y ⟨hPx, hPx'⟩
    obtain ⟨W2, hW2o, hyW2, G2, hG2, hd2⟩ := hQ.2 x x' y ⟨hQx, hQx'⟩
    refine ⟨W1 ∩ W2, hW1o.inter hW2o, ⟨hyW1, hyW2⟩, fun z => G1 z + G2 z, fun j => ?_, fun z hz => ?_⟩
    · exact ((hG1 j).mono fun z (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (W1 ∩ W2)) =>
        ⟨hz.1, hz.2.1⟩).add ((hG2 j).mono fun z
          (hz : z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (W1 ∩ W2)) => ⟨hz.1, hz.2.2⟩)
    · obtain ⟨⟨⟨hz1, hz2⟩, hzPx, hzQx⟩, hzPx', hzQx'⟩ := hz
      have e1 := hd1 z ⟨⟨hz1, hzPx⟩, hzPx'⟩
      have e2 := hd2 z ⟨⟨hz2, hzQx⟩, hzQx'⟩
      show P.φ x z + Q.φ x z - (P.φ x' z + Q.φ x' z) = (G1 z + G2 z).re
      rw [Complex.add_re, ← e1, ← e2]
      ring

theorem fixedMember_base : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C₅ C t₀ : ℝ), IsPotential A Θ → IsPosPot A Θ → (∀ y, logNormSec L s y ≤ 0) → IsSingWeight A L s th ph C₅ → IsRegFamily A Θ L s th ph phT C t₀ → ∃ t₂ : ℝ, 0 < t₂ ∧ t₂ ≤ t₀ ∧ ∀ t₁, 0 < t₁ → t₁ ≤ t₂ → IsPotential A (th + LocPot.ofFun (phT t₁) + Θ) ∧ IsPsh A (th + LocPot.ofFun (phT t₁) + Θ + Θ.rsmul (-(1 / 2))) ∧ IsPosPot A (th + LocPot.ofFun (phT t₁) + Θ) ∧ ∀ t, 0 < t → t ≤ t₁ → A.Smooth (fun y => phT t y - phT t₁ y - C * epsT C t₁) ∧ IsPsh A (th + LocPot.ofFun (phT t₁) + Θ + LocPot.ofFun (fun y => phT t y - phT t₁ y - C * epsT C t₁)) ∧ (∀ y, phT t y - phT t₁ y - C * epsT C t₁ ≤ 0) ∧ ∀ y ∉ bdry s, -(|C₅| + |C| + 1) * Real.log (rW L s y) ≤ phT t y - phT t₁ y - C * epsT C t₁ := by
  intro e X _ A Θ L s th ph phT C₅ C t₀ hΘ hpos hlog hSW hRF
  obtain ⟨a, ha, hab⟩ := epsT_small C
  obtain ⟨ht0, -, hR⟩ := hRF
  obtain ⟨hthP, -, -, hSW4⟩ := hSW
  refine ⟨min t₀ a, lt_min ht0 ha, min_le_left _ _, fun t₁ ht₁ ht₁2 => ?_⟩
  have ht₁0 : t₁ ≤ t₀ := ht₁2.trans (min_le_left _ _)
  have ht₁a : t₁ ≤ a := ht₁2.trans (min_le_right _ _)
  obtain ⟨hsm1, hC1, -, -, hpsh1, -, -, -⟩ := hR t₁ ht₁ ht₁0
  obtain ⟨he1, he1'⟩ := hab t₁ ht₁ ht₁a
  have hepsle : epsT C t₁ ≤ 1 / 2 := (le_abs_self _).trans he1
  refine ⟨isPotential_add' A _ _ (isPotential_add' A _ _ hthP (isPotential_ofFun A _ hsm1)) hΘ,
    ?_, ?_, fun t ht htt₁ => ?_⟩
  · exact isPsh_of_le A Θ th (phT t₁) hΘ hpos hthP hsm1 (epsT C t₁) (1 / 2) 0 hepsle hpsh1 _
      (fun x z (hz : z ∈ th.U x ∩ Set.univ ∩ Θ.U x ∩ Θ.U x) => ⟨hz.1.1.1, hz.1.2⟩)
      (fun x z => by
        show th.φ x z + phT t₁ z + Θ.φ x z + -(1 / 2) * Θ.φ x z = th.φ x z + phT t₁ z + 1 / 2 * Θ.φ x z - 0
        ring)
  · exact isPosPot_of_lt A Θ th (phT t₁) hΘ hpos hthP hsm1 (epsT C t₁) 1 (by linarith) hpsh1 _
      (fun x z (hz : z ∈ th.U x ∩ Set.univ ∩ Θ.U x) => ⟨hz.1.1, hz.2⟩)
      (fun x z => by
        show th.φ x z + phT t₁ z + Θ.φ x z = th.φ x z + phT t₁ z + 1 * Θ.φ x z
        ring)
  have htt0 : t ≤ t₀ := htt₁.trans ht₁0
  obtain ⟨hsm, -, hph, -, hpsh, -, -, hmono⟩ := hR t ht htt0
  obtain ⟨he, -⟩ := hab t ht (htt₁.trans ht₁a)
  have hepsle' : epsT C t ≤ 1 := by linarith [le_abs_self (epsT C t)]
  refine ⟨fun j => ((hsm j).sub (hsm1 j)).sub contDiffOn_const, ?_, fun y => ?_, fun y hy => ?_⟩
  · exact isPsh_of_le A Θ th (phT t) hΘ hpos hthP hsm (epsT C t) 1 (C * epsT C t₁) hepsle' hpsh _
      (fun x z (hz : z ∈ th.U x ∩ Set.univ ∩ Θ.U x ∩ Set.univ) => ⟨hz.1.1.1, hz.1.2⟩)
      (fun x z => by
        show th.φ x z + phT t₁ z + Θ.φ x z + (phT t z - phT t₁ z - C * epsT C t₁) =
          th.φ x z + phT t z + 1 * Θ.φ x z - C * epsT C t₁
        ring)
  · have h := hmono t₁ htt₁ ht₁0 y
    linarith
  · have h1 := hph y hy
    have h2 := (hSW4 y hy).1
    have h3 := hC1 y
    have hr : Real.exp 1 ≤ rW L s y := by
      have := hlog y
      unfold rW
      linarith
    have hL : 1 ≤ Real.log (rW L s y) := by
      have h := Real.log_le_log (Real.exp_pos 1) hr
      rwa [Real.log_exp] at h
    have k1 : 0 ≤ (|C₅| - C₅) * Real.log (rW L s y) :=
      mul_nonneg (sub_nonneg.mpr (le_abs_self C₅)) (by linarith)
    have k2 : 0 ≤ (|C| + 1) * (Real.log (rW L s y) - 1) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hL)
    have k3 := le_abs_self C
    nlinarith

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointMapsToPoints
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem comp_v_mem_mcPts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ), zb ∈ mcPts (mCoordIdeal M'.x) → zb ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv zb hz
  have hb := Cv.block
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 (Cv.κ k)
    obtain ⟨p, hp⟩ := hb.2.2.2 ⟨Cv.κ k, i⟩ ⟨k, rfl⟩
    have hk : p.1 = k := hb.1 (by have h := hb.2.2.1 p; rw [hp] at h; exact h.symm)
    obtain ⟨k₀, i₀⟩ := p
    cases hk
    exact ⟨i₀, by simpa [Function.comp, hp] using hi⟩
  · have key : ∀ g, mConeMap (M'.x ∘ Cv.v) g = MvPolynomial.map Cv.φ (mConeMap M.x g) := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a => simp [mConeMap]
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p n hp =>
        simp only [map_mul, hp]
        congr 1
        simp [mConeMap, Cv.x_eq]
    have h0 : mConeMap M.x f = 0 := hf
    have h1 : f ∈ mCoordIdeal (M'.x ∘ Cv.v) := by
      show mConeMap (M'.x ∘ Cv.v) f = 0
      rw [key, h0, map_zero]
    have h2 : rename Cv.v f ∈ mCoordIdeal M'.x :=
      GlobalTheory.CompanionTheory.Ar.PB.FA.ImageIdeal.mCoordIdeal_comp_le_imageZ _ _ _ _ Cv.κ Cv.v _ M'.x hb h1
    have h3 := hz.2 _ h2
    rwa [map_rename, eval_rename] at h3

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFrameCompatibility
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem trans_blockDiag_det : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (b : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), b ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal b) → M.GoodAt F (mCoordIdeal (b ∘ Cv.v)) → ∀ τ, IsBlockDiag j (Cv.trans F' F b τ) ∧ (Cv.trans F' F b τ).det ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv b F' F hb hF' hF hG' hG τ
  have hT := hF.1 τ
  have hT' := hF'.1 τ
  have hdet : ((F.T τ).map Cv.φ).det ≠ 0 := by
    have e : ((F.T τ).map Cv.φ).det = Cv.φ (F.T τ).det := by
      rw [RingHom.map_det]; rfl
    rw [e]
    exact (map_ne_zero Cv.φ).2 hT.2
  have hu : IsUnit ((F.T τ).map Cv.φ).det := isUnit_iff_ne_zero.2 hdet
  have hu' : IsUnit (F'.T τ).det := isUnit_iff_ne_zero.2 hT'.2
  have hA : IsBlockDiag j (((F.T τ).map Cv.φ)⁻¹ * F'.T τ) :=
    ((hT.1.map Cv.φ).inv hu).mul hT'.1
  have hreg := Cv.agree b hb F' F hF' hF hG' hG τ
  have hz : valMat M'.x b (1 : Matrix (Fin N) (Fin N) M'.Ω) = 1 := by
    have hring := ValRing.regAt_valAt_ring _ _ _ M'.x b hb
    ext a c
    by_cases e : a = c
    · subst e
      show valAt M'.x ((1 : Matrix (Fin N) (Fin N) M'.Ω) a a) b = _
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      exact hring.2.2.2.1
    · show valAt M'.x ((1 : Matrix (Fin N) (Fin N) M'.Ω) a c) b = _
      rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e]
      exact hring.2.2.1
  have hAB : (((F.T τ).map Cv.φ)⁻¹ * F'.T τ) * ((F'.T τ)⁻¹ * (F.T τ).map Cv.φ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu', Matrix.nonsing_inv_mul _ hu]
  have hmul := (regMat_mul hb (fun a c => (hreg a c).1) (fun a c => (hreg a c).2)).2
  rw [hAB, hz] at hmul
  have htr : Cv.trans F' F b τ = valMat M'.x b (((F.T τ).map Cv.φ)⁻¹ * F'.T τ) := rfl
  refine ⟨fun a c h => ?_, ?_⟩
  · show valAt M'.x ((((F.T τ).map Cv.φ)⁻¹ * F'.T τ) a c) b = 0
    rw [hA a c h]
    exact (ValRing.regAt_valAt_ring _ _ _ M'.x b hb).2.2.1
  · rw [htr]
    intro h0
    have := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact one_ne_zero this

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericIntersectionEqualsPointsIntegral
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem curvatureIntegral_eq_genericIntersection : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : IFamily ℚ ι), IsFieldIntersection I → ∀ (D : ℕ) (P : Ideal (MRing ι)) (L : Fin D → HermLine ι), IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → ptsIntegral P (pot L) (fun _ => 1) = (I (P.map (MvPolynomial.map (Int.castRingHom ℚ))) D fun j => (L j).a : ℤ) :=
  @PositivityTheory.Xgp.t_deg_generic

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GeometricDegreeNonnegativePsh
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem nonneg_degree_horizontal_curve : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (Fl : Set σ), (∀ a ∈ Fl, ∀ t, IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ IsPsh S.A (S.potT a t)) → Re.J = ⊤ → ∀ n : σ → ℤ, (∀ a ∉ Fl, 0 ≤ n a) → ∀ W : Ideal (MRing ι), IsArithVar W 2 → P ≤ W → 0 ≤ geomDeg W (combLine Re.ref n) 1 :=
  PositivityTheory.Xgp.t_nef_curve

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightsNonnegOfIntersectionSystemStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heights_nonneg_of_intersection_system : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (II : IntersectionSystem) (q : ℕ) (w : Fin q → Ω), IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A → (∀ j, w j ∈ chartLat y A.a 1) → KH.GeneratesOn y A.a w → (∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)) → HeightsNonneg II (mCoordIdeal y) A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.heightsNonneg_of_smallGenerators | exact GlobalTheory.CompanionTheory.Ar.Giv.heightsNonneg_of_smallGenerators | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.heightsNonneg_of_smallGenerators <;> assumption)
end

