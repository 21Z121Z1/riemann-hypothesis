import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.RankOneEisenstein.Theta2Integral
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0187
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchExponentEqZeroOfMulSelf
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.EisRk1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRk1

theorem archExponent_eq_zero_of_mul_self {K : Type _} [Field K] [NumberField K]
    (w : InfinitePlace K) {μ : HeckeCharacter K} (hμ : μ * μ = 1) : archExponent w μ = 0 := by
  have h : archExponent w μ = -archExponent w μ := by
    rw [← archExponent_inv, ← eq_inv_of_mul_eq_one_left hμ]
  linarith

end GlobalTheory.CompanionTheory.EisRk1
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariance
section
open MeasureTheory Filter Topology
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisAvg

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem pointwise_bound {K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {φ : K → ℂ} {M : ℝ}
    (hM1 : 1 ≤ M) (hM : ∀ κ, ‖ρ κ‖ ≤ M) (hc : ∀ p ∈ P, ‖c p‖ = 1) (hL : Law K P c φ)
    (hN : Near K P {v | ‖ρ v - 1‖ ≤ 1 / (4 * M)} φ) {w : W} (hw : w ∈ secSp K P c ρ) (κ : K) :
    ‖φ κ • ρ κ w - ((‖φ κ‖ : ℝ) : ℂ) • w‖ ≤ ‖φ κ‖ * ‖w‖ / 2 := by
  by_cases h0 : φ κ = 0
  · simp [h0]
  obtain ⟨r, v, hr, hv, rfl, hn⟩ := hN κ h0
  have hM0 : 0 < M := by linarith
  have hcr : ‖c r‖ = 1 := hc _ hr
  have hφ : φ (r * v) = c r * φ v := hL r v hr
  have hnorm : ‖φ (r * v)‖ = ‖φ v‖ := by rw [hφ, norm_mul, hcr, one_mul]
  have hwr : c r • ρ r w = w := hw r hr
  obtain ⟨u, hu⟩ : ∃ u, u = ρ v w - w := ⟨_, rfl⟩
  have hub : ‖u‖ ≤ ‖w‖ / (4 * M) := by
    have h1 : u = (ρ v - 1) w := by simp [hu]
    have hv' : ‖ρ v - 1‖ ≤ 1 / (4 * M) := hv
    rw [h1]
    calc ‖(ρ v - 1) w‖ ≤ ‖ρ v - 1‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 / (4 * M) * ‖w‖ := by gcongr
      _ = ‖w‖ / (4 * M) := by ring
  have hrb : ‖c r • ρ r u‖ ≤ ‖w‖ / 4 := by
    rw [norm_smul, hcr, one_mul]
    calc ‖ρ r u‖ ≤ ‖ρ r‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * (‖w‖ / (4 * M)) := by
          gcongr
          exact hM r
      _ = ‖w‖ / 4 := by field_simp
  have hexp : φ (r * v) • ρ (r * v) w - ((‖φ (r * v)‖ : ℝ) : ℂ) • w =
      (φ v - ((‖φ v‖ : ℝ) : ℂ)) • w + φ v • (c r • ρ r u) := by
    have h2 : ρ v w = w + u := by simp [hu]
    have h3 : ρ (r * v) w = ρ r w + ρ r u := by
      rw [map_mul, ContinuousLinearMap.mul_apply, h2, map_add]
    rw [hnorm, hφ, h3, smul_add, mul_comm, mul_smul, hwr, sub_smul, mul_smul]
    abel
  rw [hexp, hnorm]
  calc ‖(φ v - ((‖φ v‖ : ℝ) : ℂ)) • w + φ v • (c r • ρ r u)‖
      ≤ ‖φ v - ((‖φ v‖ : ℝ) : ℂ)‖ * ‖w‖ + ‖φ v‖ * ‖c r • ρ r u‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
    _ ≤ ‖φ v‖ / 4 * ‖w‖ + ‖φ v‖ * (‖w‖ / 4) := by gcongr
    _ = ‖φ v‖ * ‖w‖ / 2 := by ring

theorem avg_sub_bound [FiniteDimensional ℂ W] {K : Subgroup G} [MeasurableSpace K] [BorelSpace K]
    [CompactSpace K] (μ : Measure K) [IsProbabilityMeasure μ] {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ)
    {φ : K → ℂ} (hφ : Continuous φ) (w : W)
    (h : ∀ κ, ‖φ κ • ρ κ w - ((‖φ κ‖ : ℝ) : ℂ) • w‖ ≤ ‖φ κ‖ * ‖w‖ / 2) :
    ‖avg μ ρ φ w - ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w‖ ≤ (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2 := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hint : Integrable (fun κ => φ κ • ρ κ) μ :=
    (hφ.smul hρ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun κ => ‖φ κ‖) μ :=
    hφ.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint3 : Integrable (fun κ => φ κ • ρ κ w) μ := by
    have := hint.apply_continuousLinearMap w
    exact this
  have hint4 : Integrable (fun κ => ((‖φ κ‖ : ℝ) : ℂ) • w) μ :=
    (hint2.ofReal (𝕜 := ℂ)).smul_const w
  have e1 : avg μ ρ φ w = ∫ κ, φ κ • ρ κ w ∂μ := ContinuousLinearMap.integral_apply hint w
  have e2 : ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w = ∫ κ, ((‖φ κ‖ : ℝ) : ℂ) • w ∂μ := by
    rw [integral_smul_const, integral_complex_ofReal]
  rw [e1, e2, ← integral_sub hint3 hint4]
  have e3 : (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2 = ∫ κ, ‖φ κ‖ * ‖w‖ / 2 ∂μ := by
    rw [integral_div, integral_mul_const]
  rw [e3]
  exact norm_integral_le_of_norm_le ((hint2.mul_const _).div_const _) (Eventually.of_forall h)

theorem mass_pos {K : Subgroup G} [MeasurableSpace K] [BorelSpace K] [CompactSpace K]
    [IsTopologicalGroup K] (μ : Measure K) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    {φ : K → ℂ} (hφ : Continuous φ) (h1 : φ 1 = 1) : 0 < ∫ κ, ‖φ κ‖ ∂μ := by
  refine hφ.norm.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun _ => norm_nonneg _) (x := 1) ?_
  simp [h1]

end Abstract

theorem avgInv_of_avgMem : AvgMem → AvgInv := by
  intro hA G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hH hP Γ P c hPar
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI := hH
  haveI := hP
  obtain ⟨M, hM1, hM⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ κ, ‖ρ κ‖ ≤ M := by
    obtain ⟨C, hC⟩ := (isCompact_range hρ).isBounded.exists_norm_le
    exact ⟨max 1 C, le_max_left _ _, fun κ => (hC _ ⟨κ, rfl⟩).trans (le_max_right _ _)⟩
  have hM0 : 0 < M := by linarith
  refine ⟨{v | ‖ρ v - 1‖ ≤ 1 / (4 * M)}, ?_, ?_⟩
  · have ht : Tendsto (fun v => ρ v - 1) (𝓝 (1 : K)) (𝓝 0) := by
      have h5 := hρ.tendsto (1 : K)
      rw [map_one] at h5
      simpa using h5.sub_const 1
    have h4 : (0 : ℝ) < 1 / (4 * M) := by positivity
    filter_upwards [ht (Metric.closedBall_mem_nhds 0 h4)] with v hv
    simpa using hv
  · intro φ hφ h1 hL hN
    have hI : 0 < ∫ κ, ‖φ κ‖ ∂μ := mass_pos μ hφ h1
    have hb : ∀ w ∈ secSp K P c ρ,
        ‖avg μ ρ φ w - ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w‖ ≤ (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2 := fun w hw =>
      avg_sub_bound μ hρ hφ w (pointwise_bound hM1 hM hPar.ch.norm hL hN hw)
    have hmem : ∀ w : W, avg μ ρ φ w ∈ secSp K P c ρ := fun w =>
      hA G W K ρ hK hρ μ hH hP Γ P c hPar φ hφ hL w
    let T : secSp K P c ρ →ₗ[ℂ] secSp K P c ρ :=
      ((avg μ ρ φ : W →L[ℂ] W) : W →ₗ[ℂ] W).restrict fun w _ => hmem w
    have hinj : Function.Injective T := by
      refine (injective_iff_map_eq_zero T).mpr fun w hw => ?_
      have h0 : avg μ ρ φ (w : W) = 0 := congrArg Subtype.val hw
      have h6 := hb w w.2
      rw [h0, zero_sub, norm_neg, norm_smul, Complex.norm_real, Real.norm_of_nonneg hI.le] at h6
      have h7 : ‖(w : W)‖ = 0 := by
        have h8 : 0 ≤ ‖(w : W)‖ := norm_nonneg _
        nlinarith
      exact Subtype.ext (norm_eq_zero.mp h7)
    let e := LinearEquiv.ofInjectiveEndo T hinj
    refine ⟨LinearMap.toContinuousLinearMap ((secSp K P c ρ).subtype ∘ₗ e.symm.toLinearMap), fun w => ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply w)

end GlobalTheory.CompanionTheory.RgEisAvg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageMembership
section
open MeasureTheory PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.EisMirGen

theorem avgMem : AvgMem := by
  unfold AvgMem ForRep
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hHaar _ _Γ P c _ φ hφ hLaw w
  haveI := hHaar
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  change ∀ r : K, (r : G) ∈ P → c r • ρ r (avg μ ρ φ w) = avg μ ρ φ w
  intro r hr
  have hcont : Continuous fun κ : K => φ κ • ρ κ := hφ.smul hρ
  have hint : Integrable (fun κ : K => φ κ • ρ κ) μ :=
    hcont.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  have key : avg μ ρ φ = c r • (ρ r).comp (avg μ ρ φ) := by
    show ∫ κ, φ κ • ρ κ ∂μ = c r • (ρ r).comp (∫ κ, φ κ • ρ κ ∂μ)
    calc ∫ κ, φ κ • ρ κ ∂μ = ∫ κ, φ (r * κ) • ρ (r * κ) ∂μ :=
          (integral_mul_left_eq_self (fun κ => φ κ • ρ κ) r).symm
      _ = ∫ κ, c r • (ContinuousLinearMap.compL ℂ W W W (ρ r)) (φ κ • ρ κ) ∂μ := by
          congr 1
          funext κ
          rw [hLaw r κ hr, map_mul]
          ext x
          simp [mul_smul]
      _ = c r • ∫ κ, (ContinuousLinearMap.compL ℂ W W W (ρ r)) (φ κ • ρ κ) ∂μ := integral_smul _ _
      _ = c r • (ρ r).comp (∫ κ, φ κ • ρ κ ∂μ) := by
          rw [(ContinuousLinearMap.compL ℂ W W W (ρ r)).integral_comp_comm hint]
          rfl
  have hw := congrArg (fun T : W →L[ℂ] W => T w) key
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply] at hw
  exact hw.symm

end GlobalTheory.CompanionTheory.EisMirGen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryTermGood
section
noncomputable section

open MeasureTheory Filter Topology Metric PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisLeft

lemma gauss_strip (b c : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ c →
    ‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) ^ 4 ≤ C := by
  set X := max |b| |c| with hX
  have hX0 : 0 ≤ X := le_trans (abs_nonneg _) (le_max_left _ _)
  refine ⟨8 * Real.exp ((1 + X) ^ 2 + X ^ 2), by positivity, fun z hb hc => ?_⟩
  have hx : |z.re| ≤ X := by
    rw [abs_le]
    constructor
    · have h1 := neg_abs_le b
      have h2 := le_max_left |b| |c|
      linarith
    · have h1 := le_abs_self c
      have h2 := le_max_right |b| |c|
      linarith
  have hn : ‖Complex.exp (z ^ 2)‖ = Real.exp (z.re ^ 2 - z.im ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two, Complex.mul_re]
  have hz : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  obtain ⟨t, ht⟩ : ∃ t, t = 1 + ‖z‖ := ⟨_, rfl⟩
  rw [← ht, hn]
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hta : t ≤ (1 + X) + |z.im| := by linarith
  have ht2 : t ^ 2 ≤ 2 * (1 + X) ^ 2 + 2 * z.im ^ 2 := by
    have h1 : t ^ 2 ≤ ((1 + X) + |z.im|) ^ 2 := pow_le_pow_left₀ ht0 hta 2
    have h2 : |z.im| ^ 2 = z.im ^ 2 := sq_abs _
    nlinarith [sq_nonneg ((1 + X) - |z.im|)]
  have h4 : t ^ 4 ≤ 8 * Real.exp (t ^ 2 / 2) := by
    have h1 := Real.quadratic_le_exp_of_nonneg (x := t ^ 2 / 2) (by positivity)
    have h2 : t ^ 4 = 8 * ((t ^ 2 / 2) ^ 2 / 2) := by ring
    have h3 : 0 ≤ t ^ 2 / 2 := by positivity
    linarith
  have hx2 : z.re ^ 2 ≤ X ^ 2 := by
    rw [← sq_abs z.re]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  calc Real.exp (z.re ^ 2 - z.im ^ 2) * t ^ 4
      ≤ Real.exp (z.re ^ 2 - z.im ^ 2) * (8 * Real.exp (t ^ 2 / 2)) := by gcongr
    _ = 8 * Real.exp (z.re ^ 2 - z.im ^ 2 + t ^ 2 / 2) := by rw [Real.exp_add]; ring
    _ ≤ 8 * Real.exp ((1 + X) ^ 2 + X ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

lemma leftGood_of {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℂ → E}
    (hd : DifferentiableOn ℂ A {z | z.re < 1 / 2})
    (hb : ∀ b c : ℝ, c < 1 / 2 → ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ c → ‖A z‖ ≤ M * (1 + ‖z‖) ^ 2) :
    LeftGood (fun z => (Complex.exp (z ^ 2) * (z - 1)) • A z) (1 / 2) ∧
    LeftGood (fun z => z • (Complex.exp (z ^ 2) * (z - 1)) • A z) (1 / 2) := by
  have hd1 : DifferentiableOn ℂ (fun z => (Complex.exp (z ^ 2) * (z - 1)) • A z) {z | z.re < 1 / 2} :=
    DifferentiableOn.smul
      (by fun_prop : Differentiable ℂ fun z : ℂ => Complex.exp (z ^ 2) * (z - 1)).differentiableOn hd
  have hd2 : DifferentiableOn ℂ (fun z => z • (Complex.exp (z ^ 2) * (z - 1)) • A z) {z | z.re < 1 / 2} :=
    DifferentiableOn.smul differentiableOn_id hd1
  have key : ∀ b c : ℝ, c < 1 / 2 → ∃ B : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ c →
      ‖(Complex.exp (z ^ 2) * (z - 1)) • A z‖ * (1 + ‖z‖) ≤ B := by
    intro b c hc
    obtain ⟨M, hM⟩ := hb b c hc
    obtain ⟨C, hC0, hC⟩ := gauss_strip b c
    refine ⟨|M| * C, fun z h1 h2 => ?_⟩
    have hA : ‖A z‖ ≤ |M| * (1 + ‖z‖) ^ 2 :=
      (hM z h1 h2).trans (by gcongr; exact le_abs_self M)
    have hz1 : ‖z - 1‖ ≤ 1 + ‖z‖ := by
      have := norm_sub_le z 1
      simp only [norm_one] at this
      linarith
    have ht : 0 ≤ 1 + ‖z‖ := by positivity
    rw [norm_smul, norm_mul]
    calc ‖Complex.exp (z ^ 2)‖ * ‖z - 1‖ * ‖A z‖ * (1 + ‖z‖)
        ≤ ‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) * (|M| * (1 + ‖z‖) ^ 2) * (1 + ‖z‖) := by gcongr
      _ = |M| * (‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) ^ 4) := by ring
      _ ≤ |M| * C := by
          gcongr
          exact hC z h1 h2
  refine ⟨⟨hd1, fun b c hc => ?_⟩, ⟨hd2, fun b c hc => ?_⟩⟩
  · obtain ⟨B, hB⟩ := key b c hc
    refine ⟨B, fun z h1 h2 => le_trans ?_ (hB z h1 h2)⟩
    have : 1 ≤ 1 + ‖z‖ := by simp
    exact le_mul_of_one_le_right (norm_nonneg _) this
  · obtain ⟨B, hB⟩ := key b c hc
    refine ⟨B, fun z h1 h2 => le_trans ?_ (hB z h1 h2)⟩
    rw [norm_smul, mul_comm]
    have : ‖z‖ ≤ 1 + ‖z‖ := by simp
    gcongr

theorem differentiableOn_integral {T E : Type} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [SecondCountableTopology E] (μ : Measure T) [IsFiniteMeasure μ] {r : T → E} (hr : Continuous r)
    {ζ : ℂ → T → ℂ} (hζ : LeftFam ζ) :
    DifferentiableOn ℂ (fun z => ∫ κ, ζ z κ • r κ ∂μ) {z | z.re < 1 / 2} := by
  have hopen : IsOpen {z : ℂ | z.re < 1 / 2} := isOpen_lt Complex.continuous_re continuous_const
  intro z₀ hz₀
  have hz₀' : z₀.re < 1 / 2 := hz₀
  obtain ⟨ε, hε⟩ : ∃ ε, ε = (1 / 2 - z₀.re) / 4 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hball : ∀ w ∈ closedBall z₀ (2 * ε), w.re < 1 / 2 ∧ z₀.re - 2 * ε ≤ w.re ∧ w.re ≤ z₀.re + 2 * ε ∧
      ‖w‖ ≤ ‖z₀‖ + 2 * ε := by
    intro w hw
    have h1 : ‖w - z₀‖ ≤ 2 * ε := by simpa [dist_eq_norm] using hw
    have h2 : |(w - z₀).re| ≤ ‖w - z₀‖ := Complex.abs_re_le_norm _
    have h3 := abs_le.mp (h2.trans h1)
    have h4 : ‖w‖ ≤ ‖z₀‖ + ‖w - z₀‖ := by
      have := norm_add_le z₀ (w - z₀)
      simpa using this
    simp only [Complex.sub_re] at h3
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hsub : closedBall z₀ (2 * ε) ⊆ {z : ℂ | z.re < 1 / 2} := fun w hw => (hball w hw).1
  obtain ⟨M, hM⟩ := hζ.strip (z₀.re - 2 * ε) (z₀.re + 2 * ε) (by rw [hε]; linarith)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = |M| * (1 + (‖z₀‖ + 2 * ε)) ^ 2 := ⟨_, rfl⟩
  have hbd : ∀ w ∈ closedBall z₀ (2 * ε), ∀ t, ‖ζ w t‖ ≤ B := by
    intro w hw t
    obtain ⟨-, h2, h3, h4⟩ := hball w hw
    refine (hM w h2 h3 t).trans ?_
    rw [hB]
    gcongr
    exact le_abs_self M
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hr.continuousOn
  have hR' : ∀ t, ‖r t‖ ≤ R := fun t => hR t (Set.mem_univ t)
  have hcont : ∀ z : ℂ, z.re < 1 / 2 → Continuous (ζ z) := by
    intro z hz
    have h := hζ.cont.comp_continuous (f := fun t : T => (z, t)) (by fun_prop)
      (fun t => ⟨hz, Set.mem_univ t⟩)
    exact h
  have hmeasF : ∀ z : ℂ, z.re < 1 / 2 → AEStronglyMeasurable (fun κ => ζ z κ • r κ) μ := fun z hz =>
    ((hcont z hz).measurable.aestronglyMeasurable).smul hr.aestronglyMeasurable
  have hdiff : ∀ (t : T) (z : ℂ), z.re < 1 / 2 → HasDerivAt (ζ · t) (deriv (ζ · t) z) z := fun t z hz =>
    (((hζ.hol t) z hz).differentiableAt (hopen.mem_nhds hz)).hasDerivAt
  have hd0 : Measurable fun t => deriv (ζ · t) z₀ := by
    let h : ℕ → ℂ := fun n => ((ε / (n + 1) : ℝ) : ℂ)
    have hh0 : ∀ n, h n ≠ 0 := fun n => by
      have : ε / ((n : ℝ) + 1) ≠ 0 := by positivity
      exact Complex.ofReal_ne_zero.mpr this
    have hhs : ∀ n, z₀ + h n ∈ closedBall z₀ (2 * ε) := by
      intro n
      have h1 : ε / ((n : ℝ) + 1) ≤ ε := div_le_self hε0.le (by simp)
      have h2 : 0 ≤ ε / ((n : ℝ) + 1) := by positivity
      simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, h, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg h2]
      linarith
    have hlim : Tendsto h atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hh0⟩
      have h1 : Tendsto (fun n : ℕ => ε / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε
        simpa [div_eq_mul_inv] using h0
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      simpa [h, Function.comp_def] using h2
    refine measurable_of_tendsto_metrizable
      (f := fun (n : ℕ) t => (h n)⁻¹ • (ζ (z₀ + h n) t - ζ z₀ t)) (fun n => ?_) ?_
    · have hc : Continuous fun t => (h n)⁻¹ • (ζ (z₀ + h n) t - ζ z₀ t) :=
        (continuous_const_smul (h n)⁻¹).comp
          (show Continuous fun t => ζ (z₀ + h n) t - ζ z₀ t from
            (hcont _ (hsub (hhs n))).sub (hcont _ hz₀'))
      exact hc.measurable
    · rw [tendsto_pi_nhds]
      intro t
      exact (hasDerivAt_iff_tendsto_slope_zero.mp (hdiff t z₀ hz₀')).comp hlim
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℂ)
    (F := fun z κ => ζ z κ • r κ) (F' := fun z κ => deriv (ζ · κ) z • r κ) (x₀ := z₀)
    (s := ball z₀ ε) (bound := fun _ => B / ε * R)
    (ball_mem_nhds z₀ hε0)
    (by
      filter_upwards [hopen.mem_nhds hz₀] with z hz using hmeasF z hz)
    (by
      refine Integrable.of_bound (hmeasF z₀ hz₀') (B * R) (Eventually.of_forall fun t => ?_)
      rw [norm_smul]
      have h1 := hbd z₀ (mem_closedBall_self (by positivity)) t
      have h0 : 0 ≤ B := (norm_nonneg _).trans h1
      exact mul_le_mul h1 (hR' t) (norm_nonneg _) h0)
    (hd0.aestronglyMeasurable.smul hr.aestronglyMeasurable)
    (Eventually.of_forall fun t z hz => by
      have hz' : dist z z₀ < ε := hz
      have hsph : closedBall z ε ⊆ closedBall z₀ (2 * ε) := by
        intro w hw
        have h1 : dist w z ≤ ε := hw
        have h2 := dist_triangle w z z₀
        show dist w z₀ ≤ 2 * ε
        linarith
      have hder : ‖deriv (ζ · t) z‖ ≤ B / ε :=
        Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε0
          (((hζ.hol t).mono hsub).mono hsph |>.diffContOnCl_ball subset_rfl)
          (fun w hw => hbd w (hsph (sphere_subset_closedBall hw)) t)
      rw [norm_smul]
      exact mul_le_mul hder (hR' t) (norm_nonneg _) ((norm_nonneg _).trans hder))
    (integrable_const _)
    (Eventually.of_forall fun t z hz => by
      have hz' : z ∈ closedBall z₀ (2 * ε) := by
        have : dist z z₀ < ε := hz
        show dist z z₀ ≤ 2 * ε
        linarith
      exact (hdiff t z (hsub hz')).smul_const (r t))
  exact hmain.2.differentiableAt.differentiableWithinAt

theorem bGood : BGood := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hH hP ζ hζ
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  haveI : ProperSpace (W →L[ℂ] W) := FiniteDimensional.proper ℂ _
  haveI : IsProbabilityMeasure μ := hP
  obtain ⟨R, hR⟩ := (isCompact_univ (X := K)).exists_bound_of_continuousOn hρ.continuousOn
  refine leftGood_of (A := fun z => avg μ ρ (ζ z)) (differentiableOn_integral μ hρ hζ) ?_
  intro b c hc
  obtain ⟨M, hM⟩ := hζ.strip b c hc
  refine ⟨|M| * |R|, fun z h1 h2 => ?_⟩
  have hpt : ∀ κ : K, ‖ζ z κ • ρ κ‖ ≤ |M| * |R| * (1 + ‖z‖) ^ 2 := by
    intro κ
    rw [norm_smul]
    have h3 : ‖ζ z κ‖ ≤ |M| * (1 + ‖z‖) ^ 2 :=
      (hM z h1 h2 κ).trans (by gcongr; exact le_abs_self M)
    have h4 : ‖ρ κ‖ ≤ |R| := (hR κ (Set.mem_univ κ)).trans (le_abs_self R)
    calc ‖ζ z κ‖ * ‖ρ κ‖ ≤ (|M| * (1 + ‖z‖) ^ 2) * |R| :=
          mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
      _ = |M| * |R| * (1 + ‖z‖) ^ 2 := by ring
  have := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hpt)
  simpa [avg] using this

end GlobalTheory.CompanionTheory.RgEisLeft
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechConnectingPullNatural
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

noncomputable section

namespace GlobalTheory.CompanionTheory.CechOne

theorem hPull_zero {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}
    (φ : G ⟶ (push f).obj G') (s : G.obj.obj (op ⊤)) :
    hPull f φ 0 ((Sheaf.H.equiv₀ G isTerminalTop).symm s) =
      (Sheaf.H.equiv₀ G' isTerminalTop).symm
        (G'.obj.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op (φ.hom.app (op ⊤) s)) := by
  have hx : (Sheaf.H.equiv₀ G isTerminalTop).symm s =
      GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop ((GlobalTheory.SheafLES.equivZero.{0} G ⊤).symm s) := by
    rw [AddEquiv.symm_apply_eq]
    refine Eq.symm ((GlobalTheory.SiteCoh.equiv₀_terminalEquiv G isTerminalTop _).trans ?_)
    exact (GlobalTheory.SheafLES.equivZero.{0} G ⊤).apply_symm_apply s
  rw [hx, AddEquiv.eq_symm_apply]
  have h1 : hPull f φ 0 (GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop ((GlobalTheory.SheafLES.equivZero.{0} G ⊤).symm s)) =
      GlobalTheory.SiteCoh.terminalEquiv G' 0 isTerminalTop
        (pull.{0, 0} f φ 0 (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤)
          ((GlobalTheory.SheafLES.equivZero.{0} G ⊤).symm s)) := by
    simp only [hPull, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
  rw [h1]
  refine (GlobalTheory.SiteCoh.equiv₀_terminalEquiv G' isTerminalTop _).trans ?_
  refine (SheafPull.equivZero_pull f φ (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤) _).trans ?_
  rw [AddEquiv.apply_symm_apply]

theorem pullCoch_globalCocycle {X Y : TopCat.{0}} (f : X ⟶ Y) {P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (φ : P ⟶ (Opens.map f).op ⋙ Q)
    {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (s : P.obj (op ⊤)) :
    pullCoch f φ V U τ hτ 0 (globalCocycle P V s).1 =
      (globalCocycle Q U (Q.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op
        (φ.app (op ⊤) s))).1 := by
  funext t
  change res Q (inter_le_map f V U τ hτ t) (φ.app (op (inter V (τ ∘ t))) (res P _ s)) =
    res Q _ (Q.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op (φ.app (op ⊤) s))
  rw [app_res_map, res_res]
  change _ = res Q _ (res Q _ (φ.app (op ⊤) s))
  rw [res_res]

theorem cechHOneEquiv_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤)
    (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)} (hS : S.ShortExact) [Injective S.X₂]
    (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : GroundTheory.Arith.SchemeCoh.CechAcyclic S.X₂.obj V) (hS' : S'.ShortExact) [Injective S'.X₂]
    (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : GroundTheory.Arith.SchemeCoh.CechAcyclic S'.X₂.obj U) (α : S ⟶ S'.map (push f))
    (x : GroundTheory.Arith.SchemeCoh.cechH S.X₁.obj V 1) :
    (cechHOneEquiv U hU hS' hC' hI' : GroundTheory.Arith.SchemeCoh.cechH S'.X₁.obj U 1 ≃+ Sheaf.H.{0} S'.X₁ 1) (cechPullH f α.τ₁.hom V U τ hτ 1 x) =
      hPull f α.τ₁ 1 ((cechHOneEquiv V hV hS hC hI : GroundTheory.Arith.SchemeCoh.cechH S.X₁.obj V 1 ≃+ Sheaf.H.{0} S.X₁ 1) x) := by
  obtain ⟨s, rfl⟩ := cechOneProj_surjective V hV hC hI x
  have h₁₂ : ∀ W y, α.τ₂.hom.app W (S.f.hom.app W y) = S'.f.hom.app _ (α.τ₁.hom.app W y) := fun W y =>
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun g => g.hom) α.comm₁₂.symm) W) y
  have h₂₃ : ∀ W y, α.τ₃.hom.app W (S.g.hom.app W y) = S'.g.hom.app _ (α.τ₂.hom.app W y) := fun W y =>
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun g => g.hom) α.comm₂₃.symm) W) y
  have hmap : cechPullH f α.τ₁.hom V U τ hτ 1 (cechOneProj V hC s) =
      cechOneProj U hC' (S'.X₃.obj.map (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤).op
        (α.τ₃.hom.app (op ⊤) s)) := by
    change cechPullH f α.τ₁.hom V U τ hτ (0 + 1) (hC.delta 0 (globalCocycle S.X₃.obj V s)) =
      hC'.delta 0 (globalCocycle S'.X₃.obj U _)
    refine (GlobalTheory.T.cech_short_exact_pull_compat f V U τ hτ hC hC' α.τ₁.hom α.τ₂.hom α.τ₃.hom h₁₂ h₂₃ 0 _).trans ?_
    exact congrArg (hC'.delta 0) (Subtype.ext (pullCoch_globalCocycle f α.τ₃.hom V U τ hτ s))
  rw [hmap, cechHOneEquiv_cechOneProj, cechHOneEquiv_cechOneProj]
  change H.δ hS' 0 1 rfl ((Sheaf.H.equiv₀ S'.X₃ isTerminalTop).symm _) =
    hPull f α.τ₁ 1 (H.δ hS 0 1 rfl ((Sheaf.H.equiv₀ S.X₃ isTerminalTop).symm s))
  rw [GlobalTheory.T.sheaf_pull_connecting_compat f hS hS' α 0 _]
  exact congrArg (H.δ hS' 0 1 rfl) (hPull_zero f α.τ₃ s).symm

end GlobalTheory.CompanionTheory.CechOne
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeLeSpanNormStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_le_span_norm : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ), chartLatQ y a τ ≤ Submodule.span ℚ (chartLatNm y a τ : Set Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartDenom.chartLatQ_le_span_chartLatNm | exact GlobalTheory.CompanionTheory.Ar.ChartDenom.chartLatQ_le_span_chartLatNm | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartDenom.chartLatQ_le_span_chartLatNm <;> assumption)
end

