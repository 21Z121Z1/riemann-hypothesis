import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0609
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryNearOneEqChartMul
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

noncomputable section

namespace GlobalTheory

theorem eq_chart_mul_of_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (σ : V (nd X) → realSU X.Ψ X.Gm) (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (ρ : ℝ), IsOrth X x → 0 < ρ → σ 0 = 1 → ContinuousOn σ (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) → (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) → (∀ θ θ', t (θ + θ') = t θ * t θ') → Continuous t → (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) → ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ grpBall (realSU X.Ψ X.Gm) ε, ∃ w : ChartSp X, ‖w‖ < δ ∧ σ w.1 * t w.2 = g := by
  intro E _ _ _ r X x σ t ρ hx hρ hσ0 hσc hσB ht _ _ hstab δ hδ
  obtain ⟨η, hη, hB⟩ := GlobalTheory.T.diagonalPhaseFrame_small_angles E X.Ψ r δ hδ
  have hσa : ContinuousAt σ 0 := hσc.continuousAt (Metric.ball_mem_nhds 0 hρ)
  obtain ⟨ε1, hε1, κ, hκ, hC⟩ := GlobalTheory.T.exists_conj_inv_section_mul_entries_near_one E r X x σ hx hσ0 hσa η hη
  obtain ⟨ε2, hε2, hA⟩ := GlobalTheory.T.leftMul_near_one_lu_split_small_chart E r X x hx (min (min δ ρ) κ) (lt_min (lt_min hδ hρ) hκ)
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun g hg => ?_⟩
  have hg1 : g ∈ grpBall (realSU X.Ψ X.Gm) ε1 := fun τ a b => lt_of_lt_of_le (hg τ a b) (min_le_left _ _)
  obtain ⟨z, hz, b, hb, hgx⟩ := hA (fun τ => (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ))
    (fun τ a c => lt_of_lt_of_le (hg τ a c) (min_le_right _ _))
  have hz1 : ‖z‖ < δ := lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_left _ _))
  have hz2 : z ∈ Metric.ball (0 : V (nd X)) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hz ((min_le_left _ _).trans (min_le_right _ _))
  have hz3 : ‖z‖ < κ := lt_of_lt_of_le hz (min_le_right _ _)
  obtain ⟨b', hb', hσx⟩ := hσB z hz2
  have hxu : ∀ τ, IsUnit (mat x τ) := fun τ =>
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.orthogonalFrame_det_ne_zero X x hx τ))

  have hstep : ∃ b'' ∈ Bor X.Ψ r, X.lmulC (fun τ => (((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b'' := by
    refine ⟨fun τ => ((mat b' τ)⁻¹ * mat b τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ?_, ?_⟩
    · have hb'u : IsUnit (mat b' τ).det := isUnit_iff_ne_zero.2 (hb' τ).1
      refine ⟨?_, fun a c hca => ?_⟩
      · show ((mat b' τ)⁻¹ * mat b τ).det ≠ 0
        rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
        exact mul_ne_zero (inv_ne_zero (hb' τ).1) (hb τ).1
      · show ((mat b' τ)⁻¹ * mat b τ) a c = 0
        letI := Matrix.invertibleOfIsUnitDet _ hb'u
        have h1 : (mat b' τ)⁻¹.BlockTriangular id :=
          Matrix.blockTriangular_inv_of_blockTriangular (fun a c h => (hb' τ).2 a c h)
        have h2 : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
        exact (h1.mul h2) hca
    · funext τ
      have hb'u : IsUnit (mat b' τ).det := isUnit_iff_ne_zero.2 (hb' τ).1
      set S : GL (Fin r) ℂ := ((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ with hS
      set G : GL (Fin r) ℂ := ((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ with hG
      have eM : ((((σ z)⁻¹ * g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ) = S⁻¹ * G := rfl
      have e1 : (S : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (nmat X z) τ * mat b' τ := congrFun hσx τ
      have e2 : (G : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (nmat X z) τ * mat b τ := congrFun hgx τ
      have e3 : mat x τ * mat (nmat X z) τ = (S : Matrix (Fin r) (Fin r) ℂ) * mat x τ * (mat b' τ)⁻¹ := by
        rw [e1, Matrix.mul_assoc (mat x τ * mat (nmat X z) τ), Matrix.mul_nonsing_inv _ hb'u, Matrix.mul_one]
      show (((S⁻¹ * G : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ : Matrix (Fin r) (Fin r) ℂ) =
        mat x τ * ((mat b' τ)⁻¹ * mat b τ)
      rw [Units.val_mul, Matrix.mul_assoc, e2, e3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc]
  obtain ⟨θ, hθ⟩ := hstab _ hstep
  have hP : ∀ θ₀, ∀ τ, (mat x τ)⁻¹ * ((((t θ₀ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat (phaseFrame θ₀) τ := by
    intro θ₀ τ
    have h1 : ((((t θ₀ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = mat x τ * mat (phaseFrame θ₀) τ := congrFun (ht θ₀) τ
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hxu τ)), Matrix.one_mul]
  have hph : ∀ τ (a : Fin r), ‖phaseFrame θ τ a a - 1‖ < η := by
    intro τ a
    have h := hC z hz3 g hg1 τ a a
    rw [hθ, hP θ τ] at h
    simpa [mat] using h
  obtain ⟨θ', hθ', hPP⟩ := hB θ hph
  have htt : t θ' = t θ := by
    apply Subtype.ext; funext τ; apply Units.ext
    have h1 := congrFun ((ht θ').trans ((congrArg (rmul x) hPP).trans (ht θ).symm)) τ
    exact (hxu τ).mul_left_injective h1
  refine ⟨(z, θ'), ?_, ?_⟩
  · rw [Prod.norm_def]; exact max_lt hz1 hθ'
  · show σ z * t θ' = g
    rw [htt, ← hθ, mul_inv_cancel_left]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqNormSmoothSectionSubGluedLe
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.GlueDist

theorem sq_norm_smoothSection_sub_glued_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), A.IsSSec (A.kap + la) F0 → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → n0 A la (F0 - glue C la u) ≤ (C.m : ℝ≥0∞) * ∑ a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
  intro n Y _ _ _ _ _ ι La _ A C la F0 u hF hu
  classical
  set L := A.kap + la with hL

  set D : Fin C.m → ι → Y → ℂ := fun a j y =>
    F0 j y - A.g L j (C.idx a) y * u a (A.chart (C.idx a) y) with hD
  set S : Fin C.m → Set Y := fun a =>
    (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) with hS
  have hSo : ∀ a, IsOpen (S a) := fun a =>
    (A.chart (C.idx a)).isOpen_inter_preimage isOpen_ball
  have hsec : ∀ a, ∀ y ∈ (A.chart (C.idx a)).source, ∀ j, y ∈ (A.chart j).source →
      D a j y = A.g L j (C.idx a) y * D a (C.idx a) y := by
    intro a y hy j hj
    simp only [hD]
    rw [hF.2 j (C.idx a) y hj hy, A.g_self L (C.idx a) hy]
    ring
  have hchart : ∀ a, ∀ y ∈ (A.chart (C.idx a)).source,
      A.nsq L (D a) y = ‖F0 (C.idx a) y - u a (A.chart (C.idx a) y)‖ ^ 2 *
        Real.exp (-A.ph L (C.idx a) y) := by
    intro a y hy
    rw [A.nsq_chart L (D a) (C.idx a) hy (hsec a y hy _ (A.mem_pick y))]
    simp only [hD, A.g_self L (C.idx a) hy, one_mul]

  have hsum1 : ∀ y, ∑ a, (C.chi a y : ℂ) = 1 := by
    intro y; rw [← Complex.ofReal_sum, C.sum_one y, Complex.ofReal_one]
  have hG : F0 - glue C la u = fun j y => ∑ a, (C.chi a y : ℂ) * D a j y := by
    funext j y
    simp only [Pi.sub_apply, glue, hD, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hsum1 y, one_mul]
    congr 1
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have hchi1 : ∀ a y, C.chi a y ≤ 1 := by
    intro a y
    rw [← C.sum_one y]
    exact Finset.single_le_sum (fun b _ => C.nonneg b y) (Finset.mem_univ a)

  have hpt : ∀ y, A.nsq L (F0 - glue C la u) y ≤
      (C.m : ℝ) * ∑ a, (S a).indicator (A.nsq L (D a)) y := by
    intro y
    rw [hG]
    refine (A.nsq_sum_le L Finset.univ (fun a j y => (C.chi a y : ℂ) * D a j y) y).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (Nat.cast_nonneg _)
    have he : A.nsq L (fun j y => (C.chi a y : ℂ) * D a j y) y = C.chi a y ^ 2 * A.nsq L (D a) y := by
      unfold WeightedAtlas.nsq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (C.nonneg a y)]
      ring
    rw [he]
    by_cases h0 : C.chi a y = 0
    · rw [h0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      exact Set.indicator_nonneg (fun x _ => A.nsq_nonneg L (D a) x) y
    · have hyS : y ∈ S a := C.supp a (subset_tsupport _ h0)
      rw [Set.indicator_of_mem hyS]
      have h2 : C.chi a y ^ 2 ≤ 1 := pow_le_one₀ (C.nonneg a y) (hchi1 a y)
      nlinarith [A.nsq_nonneg L (D a) y]

  have hF0c : ∀ i, ContinuousOn (F0 i) (A.chart i).source := by
    intro i
    have h1 : ContinuousOn (F0 i ∘ (A.chart i).symm) (A.chart i).target := (hF.1 i).continuousOn
    refine (h1.comp (A.chart i).continuousOn (fun x hx => (A.chart i).map_source hx)).congr
      (fun x hx => ?_)
    simp [Function.comp, (A.chart i).left_inv hx]
  have hcont : ∀ a, ContinuousOn (fun y => ENNReal.ofReal (A.nsq L (D a) y)) (S a) := by
    intro a
    refine ENNReal.continuous_ofReal.comp_continuousOn ?_
    have hu' : ContinuousOn (fun y => u a (A.chart (C.idx a) y)) (S a) :=
      (hu a).continuousOn.comp ((A.chart (C.idx a)).continuousOn.mono Set.inter_subset_left)
        (fun y hy => hy.2)
    have hc : ContinuousOn (fun y => ‖F0 (C.idx a) y - u a (A.chart (C.idx a) y)‖ ^ 2 *
        Real.exp (-A.ph L (C.idx a) y)) (S a) :=
      ((((hF0c (C.idx a)).mono Set.inter_subset_left).sub hu').norm.pow 2).mul
        ((A.continuousOn_ph L (C.idx a)).mono Set.inter_subset_left).neg.rexp
    exact hc.congr (fun y hy => hchart a y hy.1)
  have hmeas : ∀ a, AEMeasurable ((S a).indicator (fun y => ENNReal.ofReal (A.nsq L (D a) y))) A.mu :=
    fun a => (aemeasurable_indicator_iff (hSo a).measurableSet).2
      ((hcont a).aemeasurable (hSo a).measurableSet)

  have hpiece : ∀ a, ∫⁻ y in S a, ENNReal.ofReal (A.nsq L (D a) y) ∂A.mu =
      ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
    intro a
    have hWt : ball (C.c a) (C.r a) ⊆ (A.chart (C.idx a)).target :=
      ball_subset_closedBall.trans (C.sub a)
    have heq : ∀ v ∈ ball (C.c a) (C.r a),
        D a (C.idx a) ((A.chart (C.idx a)).symm v) = F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v := by
      intro v hv
      have hvt := hWt hv
      simp only [hD, A.g_self L (C.idx a) ((A.chart (C.idx a)).map_target hvt),
        (A.chart (C.idx a)).right_inv hvt, one_mul]
    have hae : AEMeasurable (D a (C.idx a) ∘ (A.chart (C.idx a)).symm) (volume.restrict (ball (C.c a) (C.r a))) := by
      have hc : ContinuousOn (fun v => F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v) (ball (C.c a) (C.r a)) :=
        (((hF.1 (C.idx a)).continuousOn.mono hWt).sub (hu a).continuousOn)
      exact (hc.congr (fun v hv => heq v hv)).aemeasurable measurableSet_ball
    rw [GlobalTheory.T.lintegral_nsq_canonical_add_chart_part n Y ι La A la (C.idx a) (ball (C.c a) (C.r a)) (D a) measurableSet_ball hWt
      (fun y hy _ => hsec a y hy _ (A.mem_pick y)) hae]
    refine setLIntegral_congr_fun measurableSet_ball (fun v hv => ?_)
    rw [heq v hv]

  unfold n0
  calc ∫⁻ y, ENNReal.ofReal (A.nsq L (F0 - glue C la u) y) ∂A.mu
      ≤ ∫⁻ y, (C.m : ℝ≥0∞) * ∑ a, (S a).indicator (fun y => ENNReal.ofReal (A.nsq L (D a) y)) y ∂A.mu := by
        refine lintegral_mono fun y => ?_
        refine (ENNReal.ofReal_le_ofReal (hpt y)).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun a _ => Set.indicator_nonneg (fun x _ => A.nsq_nonneg L (D a) x) y)]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases hy : y ∈ S a
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy]
    _ = (C.m : ℝ≥0∞) * ∑ a, ∫⁻ y in S a, ENNReal.ofReal (A.nsq L (D a) y) ∂A.mu := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _), lintegral_finset_sum' _ (fun a _ => hmeas a)]
        congr 1
        exact Finset.sum_congr rfl fun a _ => lintegral_indicator (hSo a).measurableSet _
    _ = _ := by
        congr 1
        exact Finset.sum_congr rfl fun a _ => hpiece a

end GlobalTheory.GlueDist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubIn
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.KatzCongr

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

def coeffIdeal (τ : Type) (J : Ideal B) : Ideal (MvPowerSeries τ B) where
  carrier := {w | ∀ α, coeff α w ∈ J}
  add_mem' ha hb α := by rw [map_add]; exact J.add_mem (ha α) (hb α)
  zero_mem' α := by rw [map_zero]; exact J.zero_mem
  smul_mem' c x hx α := by
    classical
    rw [smul_eq_mul, coeff_mul]
    exact J.sum_mem fun _ _ => J.mul_mem_left _ (hx _)

def scaledIdeal (τ : Type) (K : Ideal B) (c : Q) : Ideal (MvPowerSeries τ B) where
  carrier := {x | ∀ γ, ∃ b ∈ K, c * algebraMap B Q (coeff γ x) = algebraMap B Q b}
  add_mem' {x y} hx hy γ := by
    obtain ⟨a, ha, ea⟩ := hx γ
    obtain ⟨b, hb, eb⟩ := hy γ
    exact ⟨a + b, K.add_mem ha hb, by rw [map_add, map_add, mul_add, ea, eb, map_add]⟩
  zero_mem' γ := ⟨0, K.zero_mem, by simp⟩
  smul_mem' r x hx γ := by
    classical
    rw [smul_eq_mul, coeff_mul, map_sum, Finset.mul_sum]
    have key : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal γ, ∃ b ∈ K,
        c * algebraMap B Q (coeff q.1 r * coeff q.2 x) = algebraMap B Q b := by
      intro q _
      obtain ⟨b, hb, eb⟩ := hx q.2
      exact ⟨coeff q.1 r * b, K.mul_mem_left _ hb, by rw [map_mul, map_mul, ← eb]; ring⟩
    choose! g hg eg using key
    exact ⟨∑ q ∈ Finset.HasAntidiagonal.antidiagonal γ, g q, K.sum_mem hg, by
      rw [map_sum]; exact Finset.sum_congr rfl eg⟩

end GlobalTheory.KatzCongr

namespace GlobalTheory.KatzCongr

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {τ : Type} {J : Ideal B}

theorem pow_add_sub_pow
    (hdp : ∀ w ∈ coeffIdeal τ J, ∀ n : ℕ, 0 < n → ∃ y ∈ coeffIdeal τ J, w ^ n = (n.factorial : MvPowerSeries τ B) * y)
    (v w : MvPowerSeries τ B) (hw : w ∈ coeffIdeal τ J) (n : ℕ) :
    ∃ z ∈ coeffIdeal τ J, (v + w) ^ n - v ^ n = (n : MvPowerSeries τ B) * z := by
  cases n with
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | succ m =>
    choose! y hy ey using fun k (hk : 0 < k) => hdp w hw k hk
    refine ⟨∑ k ∈ Finset.range (m + 1), (m.descFactorial k : MvPowerSeries τ B) * y (k + 1) * v ^ (m - k),
      Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hy _ (Nat.succ_pos k))), ?_⟩
    rw [add_comm v w, add_pow, Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, add_sub_cancel_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h : (((k + 1).factorial * (m + 1).choose (k + 1) : ℕ) : MvPowerSeries τ B) =
        ((m + 1 : ℕ) : MvPowerSeries τ B) * (m.descFactorial k : ℕ) := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.succ_descFactorial_succ, Nat.cast_mul]
    rw [ey (k + 1) (Nat.succ_pos k), Nat.add_sub_add_right]
    push_cast at h ⊢
    linear_combination (y (k + 1) * v ^ (m - k)) * h

theorem prod_sub_mem {σ : Type} (K : Ideal B) (c : Q) (α : σ →₀ ℕ) (u v : σ → MvPowerSeries τ B)
    (hdp : ∀ w ∈ coeffIdeal τ J, ∀ n : ℕ, 0 < n → ∃ y ∈ coeffIdeal τ J, w ^ n = (n.factorial : MvPowerSeries τ B) * y)
    (huv : ∀ i, u i - v i ∈ coeffIdeal τ J)
    (hsc : ∀ i, ∀ z ∈ coeffIdeal τ J, (α i : MvPowerSeries τ B) * z ∈ scaledIdeal τ K c)
    (s : Finset σ) : ∏ i ∈ s, u i ^ α i - ∏ i ∈ s, v i ^ α i ∈ scaledIdeal τ K c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    obtain ⟨z, hz, ez⟩ := pow_add_sub_pow hdp (v a) (u a - v a) (huv a) (α a)
    rw [add_sub_cancel] at ez
    have e : u a ^ α a * ∏ i ∈ s, u i ^ α i - v a ^ α a * ∏ i ∈ s, v i ^ α i =
        u a ^ α a * (∏ i ∈ s, u i ^ α i - ∏ i ∈ s, v i ^ α i) +
          (u a ^ α a - v a ^ α a) * ∏ i ∈ s, v i ^ α i := by ring
    rw [e, ez]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_right _ _ (hsc a z hz))

end GlobalTheory.KatzCongr

namespace GlobalTheory.KatzCongr

theorem subst_sub_in : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q) (u v : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i α, coeff α (u i - v i) ∈ J) → In (J * N) (subst (up Q u) f - subst (up Q v) f) := by
  intro p _ B O Q _ _ _ _ θ hF J hJ σ τ _ N f u v hf hu hv huv
  classical
  have hdp : ∀ w ∈ coeffIdeal τ J, ∀ n : ℕ, 0 < n →
      ∃ y ∈ coeffIdeal τ J, w ^ n = (n.factorial : MvPowerSeries τ B) * y := fun w hw n hn => by
    obtain ⟨y, hy, e⟩ := GlobalTheory.T.mvPowerSeries_coeffsInIdeal_pow_eq_factorial_mul p B O Q θ hF J hJ τ w hw n hn
    exact ⟨y, hy, e⟩
  have hsU : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun i => by simp [up, hu i]
  have hsV : HasSubst (up Q v) := hasSubst_of_constantCoeff_zero fun i => by simp [up, hv i]
  intro γ
  rw [map_sub, coeff_subst hsU, coeff_subst hsV,
    ← finsum_sub_distrib (coeff_subst_finite hsU f γ) (coeff_subst_finite hsV f γ)]
  refine finsum_induction (fun q => ∃ b ∈ J * N, q = algebraMap B Q b) ⟨0, Submodule.zero_mem _, by simp⟩
    (fun x y ⟨a, ha, ea⟩ ⟨b, hb, eb⟩ => ⟨a + b, Submodule.add_mem _ ha hb, by rw [ea, eb, map_add]⟩)
    (fun d => ?_)
  have hprod : ∀ w : σ → MvPowerSeries τ B,
      (d.prod fun s e => up Q w s ^ e) = map (algebraMap B Q) (∏ i, w i ^ d i) := by
    intro w
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_prod]
    simp [up, map_pow]
  have hsc : ∀ i, ∀ z ∈ coeffIdeal τ J,
      (d i : MvPowerSeries τ B) * z ∈ scaledIdeal τ (J * N) (coeff d f) := by
    intro i z hz γ'
    obtain ⟨b, hb, eb⟩ := hf d i
    refine ⟨coeff γ' z * b, Ideal.mul_mem_mul (hz γ') hb, ?_⟩
    rw [show ((d i : ℕ) : MvPowerSeries τ B) = C (d i : B) from (map_natCast C _).symm, coeff_C_mul,
      map_mul, map_mul, ← eb, map_natCast]
    ring
  have hmem := prod_sub_mem (J := J) (J * N) (coeff d f) d u v hdp (fun i α => huv i α) hsc Finset.univ
  obtain ⟨b, hb, eb⟩ := hmem γ
  refine ⟨b, hb, ?_⟩
  rw [hprod, hprod, smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub (coeff γ), ← map_sub, coeff_map, ← eb]

end GlobalTheory.KatzCongr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumCupOneFormsZeroImpCoordinatesZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem sum_toO_eq_zero_of_sum_cup : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ hc : Closed1 F = ⊤, Function.Surjective (toO F) → ∀ (n : ℕ) (a : Fin n → Hyp1 F) (w : Fin n → Glob1 F), ∑ k, cupHyp F (a k) (clAll F hc (w k)) = 0 → ∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • toO F (a k) = 0 := by
  intro R _ C _ F hF hH hc hsurj n a w hsum l
  obtain ⟨δ, hδnat, hδw⟩ := GlobalTheory.T.exists_globalVectorField_of_oneForm_functional R C F hF hH l
  choose c hcA using fun k => Hyp1.mk_surjective F (a k)
  have hmem : ∀ v : Glob1 F, v ∈ Closed1 F := fun v => hc ▸ Submodule.mem_top
  have hcl : ∀ v : Glob1 F, clAll F hc v = Hyp1.mk F (formZZ F ⟨v, hmem v⟩) := fun v => rfl
  have hf : ∀ v : Glob1 F, (formZZ F ⟨v, hmem v⟩).1 = (0, v.1) := fun v => rfl
  have h2 : Hyp2.mk F (∑ k, cupZZ F (c k) (formZZ F ⟨w k, hmem (w k)⟩)) = 0 := by
    rw [map_sum, ← hsum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcl, ← hcA k, cupHyp_mk]
  obtain ⟨e, he⟩ := Hyp2.mk_eq_zero.1 h2
  have hsumv : (∑ k, cupZZ F (c k) (formZZ F ⟨w k, hmem (w k)⟩)).1 =
      ∑ k, cupTot F (c k).1 (0, (w k).1) := by
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coe_cupZZ, hf]
  rw [hsumv] at he
  have hz : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), d1 F e.1 T T' T'' φ ψ = 0 := by
    intro T T' T'' φ ψ
    have := congrArg (fun x : Tot2 F => x.1 T T' T'' φ ψ) he
    simp only [Prod.fst_sum, Finset.sum_apply, cupTot_apply, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero] at this
    exact this
  have ha : ∀ T T' (φ : T ⟶ T'), e.2 T' - p1 F φ (e.2 T) - D R _ (e.1 T T' φ) =
      ∑ k, (c k).1.1 T T' φ • (w k).1 T' := by
    intro T T' φ
    have := congrArg (fun x : Tot2 F => x.2.1 T T' φ) he
    simp only [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, cupTot_a, Pi.zero_apply, zero_smul,
      sub_zero] at this
    exact this
  have he1 : e.1 ∈ Z1 F := by
    rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker]
    funext T T' T'' φ ψ
    exact hz T T' T'' φ ψ
  obtain ⟨b, hb⟩ := hsurj (H1.mk F ⟨e.1, he1⟩)
  obtain ⟨c', rfl⟩ := Hyp1.mk_surjective F b
  rw [toO_mk, H1.mk_eq_mk] at hb
  obtain ⟨g, hg⟩ := hb
  have hfn : ∀ x : cechDeRhamTotalCocyclesOne F, ((cechDeRhamTotalCocyclesOne.fn F x : Z1 F) : C1 F) = x.1.1 := fun x => rfl
  rw [hfn] at hg
  have hg' : ∀ T T' (φ : T ⟶ T'), e.1 T T' φ = c'.1.1 T T' φ - (g T' - mp F φ (g T)) := by
    intro T T' φ
    have := congrFun (congrFun (congrFun hg T) T') φ
    simp only [amitsur_d0_apply, Pi.sub_apply] at this
    rw [this]; abel
  have hD : ∀ T T' (φ : T ⟶ T'), D R _ (e.1 T T' φ) =
      (c'.1.2 T' - D R _ (g T')) - p1 F φ (c'.1.2 T - D R _ (g T)) := by
    intro T T' φ
    rw [hg', cechDeRhamTotalCocyclesOne.conn c' φ]
    simp only [map_sub, ← p1_D]
    abel
  have hgoal : ∑ k, l (w k) • toO F (a k) = H1.mk F (∑ k, l (w k) • cechDeRhamTotalCocyclesOne.fn F (c k)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, ← hcA k, toO_mk]
  rw [hgoal, H1.mk_eq_zero]
  refine ⟨fun T => δ T (e.2 T - (c'.1.2 T - D R _ (g T))), ?_⟩
  funext T T' φ
  rw [amitsur_d0_apply, ← hδnat, ← map_sub]
  have key : e.2 T' - (c'.1.2 T' - D R _ (g T')) - p1 F φ (e.2 T - (c'.1.2 T - D R _ (g T))) =
      ∑ k, (c k).1.1 T T' φ • (w k).1 T' := by
    rw [← ha, hD]
    simp only [map_sub]
    abel
  rw [key, map_sum]
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, hfn,
    LinearMap.map_smul, hδw, smul_eq_mul, Algebra.smul_def]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]
  rfl

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWedgeGlobalOneFormsEqZeroIff
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem wsum_eq_zero_iff : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (n : ℕ) (u v : Fin n → Glob1 F), wsum F u v = 0 ↔ ∀ l l' : Glob1 F →ₗ[R] R, ∑ k, (l (u k) * l' (v k) - l (v k) * l' (u k)) = 0 := by
  intro R _ C _ F hfr hH n u v
  constructor
  · intro hw l l'
    obtain ⟨δ, -, hδ⟩ := GlobalTheory.T.exists_globalVectorField_of_oneForm_functional R C F hfr hH l
    obtain ⟨δ', -, hδ'⟩ := GlobalTheory.T.exists_globalVectorField_of_oneForm_functional R C F hfr hH l'
    have key : ∀ T, algebraMap R (F.obj T) (∑ k, (l (u k) * l' (v k) - l (v k) * l' (u k))) = 0 := by
      intro T
      have h0 := congrArg (exteriorPower.pairingDual (F.obj T) Ω[F.obj T⁄R] 2
        (exteriorPower.ιMulti (F.obj T) 2 ![δ T, δ' T])) (congrFun hw T)
      simp only [wsum, map_sum, wedge_eq_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti,
        Matrix.det_fin_two, map_zero, Pi.zero_apply] at h0
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.head_cons, hδ, hδ'] at h0
      rw [← h0, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_sub, map_mul, map_mul]
      ring
    obtain ⟨r, -, huniq⟩ := hH 0 (map_zero _)
    have h1 := huniq _ (fun T => by rw [key T]; rfl)
    have h2 := huniq 0 (fun T => by rw [map_zero]; rfl)
    rw [h1, h2]
  · intro h
    obtain ⟨m, ⟨Φ⟩⟩ := hfr
    obtain ⟨L, -, hL⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F hH m Φ
    funext T
    have hexp : ∀ w : Glob1 F, w.1 T = ∑ i, L i w • (Φ.w i).1 T := by
      intro w
      conv_lhs => rw [hL w]
      simp [Submodule.coe_sum, Finset.sum_apply]
    let x : Fin m → Fin m → Om R (F.obj T) 2 := fun i j => wedge R _ ((Φ.w i).1 T) ((Φ.w j).1 T)
    let c : Fin m → Fin m → R := fun i j => ∑ k, L i (u k) * L j (v k)
    have hc : ∀ i j, c i j = c j i := by
      intro i j
      have := h (L i) (L j)
      rw [Finset.sum_sub_distrib, sub_eq_zero] at this
      simp only [c, this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hsum : wsum F u v T = ∑ i, ∑ j, c i j • x i j := by
      have hu : ∀ k, (u k).1 T = ∑ i, L i (u k) • (Φ.w i).1 T := fun k => hexp _
      have hv : ∀ k, (v k).1 T = ∑ i, L i (v k) • (Φ.w i).1 T := fun k => hexp _
      simp only [wsum, hu, hv, map_sum, LinearMap.sum_apply, wedge_smul_left, wedge_smul_right, c, x,
        Finset.sum_smul, mul_smul]
      conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    rw [Pi.zero_apply, hsum, ← Finset.sum_product' (f := fun i j => c i j • x i j)]
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ _
      simp only [Prod.swap_prod_mk, x]
      rw [hc j i, wedge_swap ((Φ.w j).1 T), smul_neg, add_neg_cancel]
    · rintro ⟨i, j⟩ _ hne heq
      apply hne
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      simp [x]
    · simp
    · simp

end GlobalTheory.AbCoh
end
end

