import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0074
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0079
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0081
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0076
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualBasisTraceLogNorm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.DualLattices.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTateMatricesLink
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftPrincipallyPolarisedAbelianSquareZeroStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0059
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0055
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0057
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0056
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPeriodTowerDatumOfAbelianSchemeSymmetricBuStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0081
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0065
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0077
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0058

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaOpenCone
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem setCrofton : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ A : Set (EuclideanSpace ℂ (Fin n)), IsOpen A → IsScaleStable A →
    planeMass n e * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1)) =
      gaussM (e + 1) n Set.univ *
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A} := by
  intro n e δ h W f hW hf hδ A hA hAs
  have hle : e + 1 ≤ n := chowGroups_le hW hf hδ
  have hδpos : 1 ≤ δ := ChowDegreePos.proof n (e + 1) δ W f (Nat.succ_pos e) hW hf hδ
  have hfib := ConeFibreDegree.full n e δ h W f hW hf hδ
  have hfin : ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin (e + 1)),
      fibreCount h W π w ≠ ⊤ := by
    filter_upwards [hfib] with π hπ
    filter_upwards [hπ] with w hw
    rw [hw]
    exact ENat.natCast_ne_top δ
  obtain ⟨K, hK0, hKtop, hK⟩ := GlobalTheory.T.hausdorff_cone_ball_measure n (e + 1) (Nat.succ_pos e) hle
  have hball : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) < ⊤ :=
    ConeBallFinite.full n e h W f hW hf
  have hmass : ∀ B : Set (EuclideanSpace ℂ (Fin n)),
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ B} < ⊤ := fun B =>
    lt_of_le_of_lt (measure_mono (show _ ⊆ coneBall h W from fun y hy => And.intro hy.1 hy.2.1)) hball

  have key : ∀ B : Set (EuclideanSpace ℂ (Fin n)), IsOpen B → IsScaleStable B →
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) *
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
          cntOver (coneSet h W ∩ B) π (firstCoordVec (e + 1)) =
      K * (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ B} := by
    intro B hB hBs
    have h1 := hK h W hW hfin B hB.measurableSet
      (fun y hy t ht => by
        have := hBs y hy (t : ℂ) (by exact_mod_cast ht.ne')
        simpa using this) (hmass B)
    have h2 := GlobalTheory.T.ball_average_fibre_count n e (coneSet h W ∩ B)
      ((isScaleStable_coneSet h hW).inter hBs) (isSigmaCompact_cone_inter h W hB) id measurable_id
    simp only [id] at h2
    rw [← h2, h1]
  have hΓ : gaussM (e + 1) n Set.univ = ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π := by
    rw [gaussM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hcnt : ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
      cntOver (coneSet h W ∩ Set.univ) π (firstCoordVec (e + 1)) =
      gaussM (e + 1) n Set.univ * (δ : ℝ≥0∞) := by
    rw [hΓ, ← lintegral_mul_const' _ _ (ENNReal.natCast_ne_top δ)]
    refine lintegral_congr_ae ?_
    filter_upwards [GlobalTheory.T.ae_fibre_points_card_eq_degree n e δ h W f hW hf hδ] with π hπ
    have : cntOver (coneSet h W ∩ Set.univ) π (firstCoordVec (e + 1)) = (δ : ℝ≥0∞) := by
      rw [Set.inter_univ, cntOver]
      have : (ptsOver (coneSet h W) π (firstCoordVec (e + 1))).encard = δ := hπ
      rw [this]
      simp
    rw [this]
  have hcb : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ Set.univ} = coneBall h W := by
    ext y
    simp [coneBall, coneSet]
  have hmf : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) =
      (δ : ℝ≥0∞) * planeMass n e :=
    ConeMassOfFibre.full n (e + 1) δ h W hW hfib
  have hV0 : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) ≠ 0 :=
    (Metric.measure_ball_pos _ _ one_pos).ne'
  have hVtop : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hδ0 : (δ : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : δ ≠ 0)
  have hδtop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top δ

  have hVΓ : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) * gaussM (e + 1) n Set.univ =
      K * planeMass n e := by
    have h0 := key Set.univ isOpen_univ (fun _ _ _ _ => Set.mem_univ _)
    rw [hcnt, hcb, hmf] at h0
    refine (ENNReal.mul_left_inj hδ0 hδtop).1 ?_
    rw [mul_assoc, h0]
    ring
  have hA1 := key A hA hAs
  refine (ENNReal.mul_right_inj hV0 hVtop).1 ?_
  calc volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) * (planeMass n e * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1)))
      = planeMass n e * (volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1))) := by ring
    _ = planeMass n e * (K * (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A}) := by rw [hA1]
    _ = (K * planeMass n e) * (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A} := by ring
    _ = _ := by rw [← hVΓ]; ring

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentTwistedGeneratorExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.RelDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rt_sq_field (H : Host E) : ((H.rt : E)) ^ 2 = -(H.d : E) := by
  have h := congrArg (algebraMap (𝓞 E) E) H.rt_sq
  rw [map_pow, map_neg, map_natCast] at h
  exact h

theorem rt_ne_zero (H : Host E) : (H.rt : E) ≠ 0 := by
  intro h
  have h1 := rt_sq_field H
  rw [h, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at h1
  exact H.d_prime.ne_zero h1

theorem conj_eq_neg_of_sq {z : ℂ} {d : ℝ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero] at hre him
  have h0 : z.re = 0 := by
    rcases mul_eq_zero.mp (show z.re * z.im = 0 by nlinarith) with h | h
    · exact h
    · rw [h] at hre
      nlinarith [sq_nonneg z.re]
  apply Complex.ext <;> simp [h0]

theorem conj_rt (H : Host E) : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  let φ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  apply conj_eq_neg_of_sq (d := (H.d : ℝ)) (by exact_mod_cast H.d_prime.pos)
  rw [← map_pow, rt_sq_field, map_neg, map_natCast]
  simp

theorem exists_local_generator (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : Nat.Primes) :
    ∃ δ : E, δ ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ],
      Real.log ‖j δ‖ = logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (H.rt : E)‖ ∧
      Real.log ‖j (IsCMField.complexConj E δ)‖ = Real.log ‖j δ‖ := by
  obtain ⟨δ₀, -, hδ₀, hconj, hlog⟩ := GlobalTheory.T.exists_real_different_generator E H.unram ℓ
  have hrt : (H.rt : E) ≠ 0 := rt_ne_zero H
  have hδ₀E : (δ₀ : E) ≠ 0 := by exact_mod_cast hδ₀
  refine ⟨(δ₀ : E) / (H.rt : E), div_ne_zero hδ₀E hrt, fun j => ⟨?_, ?_⟩⟩
  · rw [map_div₀, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero j).mpr hδ₀E))
        (norm_ne_zero_iff.mpr ((map_ne_zero j).mpr hrt)), hlog]
  · rw [map_div₀, hconj, conj_rt H, div_neg, map_neg, norm_neg]

end GlobalTheory.CompanionTheory.Ar.Fl.RelDiff
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualBasisTraceLogNormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_basis_trace_log_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : Nat.Primes) (f : ℕ) (b : Fin f → 𝓞 E), IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b → ∃ b' : Fin f → E, (∀ (K : Type) [Field K] (σ σ' : E →+* K), σ (H.rt : E) = σ' (H.rt : E) → (σ = σ' → ∑ k, σ (b' k) * σ' (b k : E) = 1) ∧ (σ ≠ σ' → ∑ k, σ (b' k) * σ' (b k : E) = 0)) ∧ ∀ j : E →+* ℂ_[ℓ], 0 < (⨆ k, ‖j (b' k)‖) ∧ Real.log (⨆ k, ‖j (b' k)‖) = Real.log ‖j (H.rt : E)‖ - logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RelDual.relative_dual | exact GlobalTheory.CompanionTheory.Ar.RelDual.relative_dual | (intros; apply GlobalTheory.CompanionTheory.Ar.RelDual.relative_dual <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependenceStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_independence : GroundTheory.Heights₂.Heights.NumbersDVR.FlagIndependence.Statement := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main | exact GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main | (intros; apply GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupChartFamily
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.Ar.GR

private theorem thetaBar_surj (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) :
    Function.Surjective (Ainf.thetaBar p O hv ε hε) := by
  intro b
  obtain ⟨a, rfl⟩ := Ainf.theta_surj p O hv b
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

private theorem thetaBar_mul (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
    (x y : Ainf.R0 p O ε) (hx : x ∈ RingHom.ker (Ainf.thetaBar p O hv ε hε))
    (hy : y ∈ RingHom.ker (Ainf.thetaBar p O hv ε hε)) : x * y = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha : a ∈ RingHom.ker (WittVector.fontaineTheta O p) := hx
  have hb : b ∈ RingHom.ker (WittVector.fontaineTheta O p) := hy
  rw [Ainf.ker_theta p O hv ε hε, Ideal.mem_span_singleton'] at ha hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton'.2 ⟨a' * b', by ring⟩

private theorem ptOf_act {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] (g : ℕ) (B : BX R₀) (O : LAlg R₀)
    (τ : Ix g → ℕ → B.G O) (h0 : ∀ i, p • τ i 0 = 0) (f : B.G O →+ B.G O)
    (M : Matrix (Ix g) (Ix g) ℤ_[p])
    (hf : ∀ j, f (τ j 0) = ∑ k, (PadicInt.toZModPow (0 + 1) (M k j)).val • τ k 0) (t : TT p g) :
    f (ptOf B τ (red p g t)) = ptOf B τ (red p g (M *ᵥ t)) := by
  have hsum : ∀ (s : Finset (Ix g)) (c : Ix g → ZMod p) (x : B.G O), p • x = 0 →
      (∑ j ∈ s, c j).val • x = ∑ j ∈ s, (c j).val • x := by
    intro s c x hx
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert b s hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb, GlobalTheory.TateMatrices.val_add_smul _ _ x hx, ih]
  simp only [ptOf, red, map_sum, map_nsmul, hf]
  have hred : ∀ k, PadicInt.toZMod ((M *ᵥ t) k) = ∑ j, PadicInt.toZMod (M k j) * PadicInt.toZMod (t j) := by
    intro k
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp only [hred]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hsum _ _ _ (h0 k)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, GlobalTheory.TateMatrices.val_mul_smul _ _ _ (h0 k), GlobalTheory.TateMatrices.toZMod_val_smul _ _ (h0 k)]

private theorem htd_of_dat {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    (v : Valuation C NNReal) (Tw : ATowerL R₀ p) [Algebra (Tw.O : Type) C] (hv : v.Integers (Tw.O : Type))
    (hp : ¬IsUnit (p : (Tw.O : Type))) (hc : IsAdicComplete (Ideal.span {(p : (Tw.O : Type))}) (Tw.O : Type))
    [Algebra ℤ_[p] (Tw.O : Type)] (g : ℕ) (OE : Type) [CommRing OE] [StarRing OE]
    (B : BX R₀) (F : FGLaw (Tw.O : Type) g)
    (Y : ∀ R : LAlg R₀, LHom Tw.O R → (Fin g → (R : Type)) → B.G R) (hY : BXChart B Tw.O F.F Y)
    (α : OE → Fin g → PS (Tw.O : Type) 1 g) (hα : ∀ a j, MvPowerSeries.constantCoeff (α a j) = 0)
    (A : OE → OEnd B Tw.O)
    (hA : ∀ b (R : LAlg R₀) (s : LHom Tw.O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) →
      (A b).f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α b j) ![a]))
    (Dt : DualTower Tw) (cp : (Tw.O : Type)) (D : Dat p g B Tw Dt (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp)
    (h₁ : D.H.P = 0) (h₂ : D.H.PL = 0)
    (h₃ : ∀ a {R S : LAlg R₀} (s : LHom Tw.O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker)
      (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) →
      (A a).f s (B.tg π hπ (D.ch.gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k)) :
    ∃ (H : HodgeTateDatum p g v (Tw.O : Type) (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) (Tw.O : Type)),
      H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧
      (∀ i, ∃ u : PS (Tw.O : Type) 1 g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) ∧
      H.AA.carrier = D.evImg C ∧ H.ρ = D.H.ρ := by
  obtain ⟨S, hS, hT⟩ := GlobalTheory.T.exists_tangentChartMatrix_of_basis R₀ B Tw.O g F Y hY D.ch.gb
  refine ⟨GlobalTheory.EvClose.htdOfDat D C v (Function.Injective.isDomain _ hv.hom_inj) hv.hom_inj, S, h₁, h₂, hS,
    fun a => ?_, fun i => ?_, rfl, rfl⟩
  · exact GlobalTheory.T.jacobian_mul_tangentChartMatrix_intertwines R₀ B Tw.O g F Y hY D.ch.gb S hT (A a) (α a) _ (hα a) (hA a) (h₃ a)
  · obtain ⟨u, hu, hP⟩ := GlobalTheory.T.exists_character_pairSer_alt R₀ B Tw.O g F Y hY p hp hc (D.L.τ i) (D.L.τ_tors i) (D.L.τ_compat i)
    refine ⟨u, hu, ?_⟩
    rw [GlobalTheory.T.linear_part_pairing_series_eq_height R₀ B p Tw Dt g Y D.ch.gb S hT (D.L.τ i) u hu.1 hP (D.L.ht i) (D.L.ht_spec i)]
    funext l
    exact (D.L.Ht_eq l i).symm

private theorem htd_of_tower (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
    (Tw : ATowerL (Ainf.R0 p O ε) p) (hTw : Tw = Ainf.ainfTowerL p O hv ε hε)
    [Algebra (Tw.O : Type) C] (hv' : v.Integers (Tw.O : Type))
    [hp : Fact ¬IsUnit (p : (Tw.O : Type))]
    [hc : IsAdicComplete (Ideal.span {(p : (Tw.O : Type))}) (Tw.O : Type)]
    [Algebra ℤ_[p] (Tw.O : Type)] (hvp : v (p : C) < 1)
    (T : Type) [CommRing T] [IsNoetherianRing T] (P₀ : Out.PolAV (Geo.Tor.Sp T)) (io : T →+* (Tw.O : Type))
    (P : Out.PolAV (Geo.Tor.Sp (Tw.O : Type))) (φ : P.A.left ⟶ P₀.A.left)
    (h₁ : Geo.Tor.IsGrpPullback P.A P₀.A (Geo.Tor.spMap io) φ) (h₂ : Geo.Tor.LBIso P.L (P₀.L.pull φ))
    (h₃ : P.g = P₀.g) (h₄ : 1 ≤ P.g) (OE : Type) [CommRing OE] [StarRing OE] (o : P.OAct OE)
    (F : FGLaw (Tw.O : Type) P.g) (X : Fam P.A P.g) (hX : NilChart P.A F.F X)
    (α : OE → Fin P.g → PS (Tw.O : Type) 1 P.g) (hα : ∀ a, Reads X X (o.act a) (α a)) :
    ∃ (H : HodgeTateDatum p P.g v (Tw.O : Type) (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) Tw.c)
      (S : Matrix (Fin P.g) (Fin P.g) (Tw.O : Type))
      (pt : Nb p P.g → (sp (R₀ := (Tw.O : Type)) (Tw.O : Type) ⟶ P.A)),
      H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧
      (∀ i, ∃ u : PS (Tw.O : Type) 1 P.g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) ∧
      IsTorsPts P.A p pt ∧ (∀ T : TorsRep P.A p, H.AA.carrier = torsFun C T pt) ∧
      ∀ (a : OE) (t : TT p P.g), pt (red p P.g (H.ρ (1 ⊗ₜ[ℤ] a) *ᵥ t)) = pt (red p P.g t) ≫ o.act a := by
  have hsurj : Function.Surjective (algebraMap (Ainf.R0 p O ε) (Tw.O : Type)) := by
    subst hTw; exact thetaBar_surj p O hv ε hε
  have hmul : ∀ x y : Ainf.R0 p O ε, x ∈ RingHom.ker (algebraMap (Ainf.R0 p O ε) (Tw.O : Type)) →
      y ∈ RingHom.ker (algebraMap (Ainf.R0 p O ε) (Tw.O : Type)) → x * y = 0 := by
    subst hTw; exact thetaBar_mul p O hv ε hε
  have hker : RingHom.ker (algebraMap (Ainf.R0 p O ε) (Tw.O : Type)) ^ 2 = ⊥ := by
    refine (pow_two _).trans (eq_bot_iff.2 ?_)
    exact Ideal.mul_le.2 fun x hx y hy => (Submodule.mem_bot _).2 (hmul x y hx hy)
  haveI : IsLocalRing (Ainf.R0 p O ε) := Ainf.local_of_surj_sq _ hsurj (fun k hk => hmul k k hk hk)
  obtain ⟨G, iG, cG, Q, ψ, ψ₂, hab, hQ, t₁, t₂, hsym, hamp, hnd, hpb, hsq, hΛ⟩ :=
    GlobalTheory.T.exists_lift_principally_polarised_abelian_square_zero p C v (Tw.O : Type) hv' T P₀ io P φ h₁ h₂ h₃ h₄ _ _ hsurj hker
  letI : Algebra (Ainf.R0 p O ε) C :=
    ((algebraMap (Tw.O : Type) C).comp (algebraMap (Ainf.R0 p O ε) (Tw.O : Type))).toAlgebra
  haveI : IsScalarTower (Ainf.R0 p O ε) (Tw.O : Type) C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hp0 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hsm := GlobalTheory.T.smoothOfRelativeDimension_of_grpPullback_localRing _ _ _ G P.A ψ P.g hab hpb P.smoothDim
  obtain ⟨hθ, hn⟩ := GlobalTheory.T.cube_trivial_and_finite_flat_surjective_mul_abelianScheme _ G _ Q hab (LB.isLB_pull hQ _) hamp hQ
  obtain ⟨hf₁, hf₂, hf₃⟩ := hn p hp0
  have hcard := GlobalTheory.T.card_torsion_of_polarisedAbelianScheme_lift _ _ C G P ψ hpb p (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hros := fun a : OE =>
    GlobalTheory.T.exists_generator_of_rosatiAdjoint_lambdaBundle _ P _ Q ψ₂ hQ hΛ _ _ (o.hom a) (o.hom (star a)) (o.rosati a)
  have key : ∃ (B : BX (Ainf.R0 p O ε)) (e : ∀ R : LAlg (Ainf.R0 p O ε), B.G R → (sp (R₀ := (Ainf.R0 p O ε)) (R : Type) ⟶ G)) (Ad : OE → OAdj B Tw.O), (∀ R, Function.Bijective (e R)) ∧ (∀ R x y, e R (x + y) = e R x * e R y) ∧ (∀ {R S : LAlg (Ainf.R0 p O ε)} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) ∧ (∀ a, (∀ {R : LAlg (Ainf.R0 p O ε)} (s : LHom Tw.O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ P.A), x'.left ≫ ψ = (e R x).left → (x' ≫ o.act a).left ≫ ψ = (e R ((Ad a).a.f s x)).left)) ∧ ∃ (Dt : DualTower Tw) (D : Dat p P.g B Tw Dt (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) Tw.c), D.H.P = 0 ∧ D.H.PL = 0 ∧ (∀ a {R S : LAlg (Ainf.R0 p O ε)} (s : LHom Tw.O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin P.g) (i : π.ker) (m : Fin P.g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) → (Ad a).a.f s (B.tg π hπ (D.ch.gb l ⊗ₜ[(Ainf.R0 p O ε)] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[(Ainf.R0 p O ε)] m k)) ∧ (∀ a j, (Ad a).a.f (LHom.id Tw.O) (D.L.τ j 0) = ∑ k, (PadicInt.toZModPow (0 + 1) (D.H.ρ (1 ⊗ₜ[ℤ] a) k j)).val • D.L.τ k 0) := by
    subst hTw
    obtain ⟨B, e, Ad, k₁, k₂, k₃, k₄, Dt, D, k₅, k₆, k₇, k₈⟩ :=
      GlobalTheory.T.exists_periodTowerDatum_of_abelianScheme_symmetricBundle p O hv ε hε P.g G Q hab hsm hQ hθ t₁ t₂ hsym hf₁ hf₂ hf₃ hv' (hnd _) hcard
        P.A ψ ψ₂ P.isAb hpb hsq OE (cjZ OE) o.toRingAct (fun a => star_star a) hros
    exact ⟨B, e, Ad, k₁, k₂, k₃, k₄, Dt, D, k₅, k₆, k₇, fun a j => k₈ a j 0⟩
  obtain ⟨B, e, Ad, k₁, k₂, k₃, k₄, Dt, D, k₅, k₆, k₇, k₈⟩ := key
  obtain ⟨Y, hY, hR⟩ := GlobalTheory.T.abelianFunctorNilChart_of_nilpotent_chart _ G B e k₁ k₂ k₃ Tw.O P.A ψ hpb P.g F.F X hX
  obtain ⟨H, S, e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ :=
    htd_of_dat p C v Tw hv' hp.out hc P.g OE B F Y hY α (fun a => (hα a).1) (fun a => (Ad a).a)
      (fun b => hR _ _ _ (hα b) (k₄ b)) Dt Tw.c D k₅ k₆ k₇
  obtain ⟨pt, hpt, hT, hE⟩ :=
    GlobalTheory.T.dual_tower_hodge_tate_datum p C v P.g B Tw Dt hv' hvp _ (sigE p OE) Tw.c D G e k₁ k₂ k₃ P.A ψ hpb
  refine ⟨H, S, pt, e₁, e₂, e₃, e₄, e₅, hT, fun T => e₆.trans (hE T), fun a t => ?_⟩
  have h0 : ∀ i, p • D.L.τ i 0 = 0 := fun i => by
    have h := D.L.τ_tors i 0
    rwa [zero_add, pow_one] at h
  have hAct := ptOf_act p P.g B Tw.O D.L.τ h0 ((Ad a).a.f (LHom.id Tw.O)) (D.H.ρ (1 ⊗ₜ[ℤ] a)) (k₈ a) t
  have hA := k₄ a (LHom.id Tw.O) (ptOf B D.L.τ (red p P.g t)) (pt (red p P.g t)) (hpt _)
  rw [hAct] at hA
  rw [e₇]
  apply Over.OverMorphism.ext
  apply hpb.1.hom_ext
  · rw [hpt]
    exact hA.symm
  · simp

theorem exists_htd_act : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (P : Out.PolAV (Geo.Tor.Sp O)), 1 ≤ P.g → ∀ (g : ℕ), P.g = g → ∀ (OE : Type) [CommRing OE] [StarRing OE] (o : P.OAct OE) (F : FGLaw O g) (X : Fam P.A g), NilChart P.A F.F X → ∀ α : OE → Fin g → PS O 1 g, (∀ a, Reads X X (o.act a) (α a)) → ∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) O) (pt : Nb p g → (sp (R₀ := O) O ⟶ P.A)), H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (α a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧ (∀ i, ∃ u : PS O 1 g, IsCh F.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) ∧ IsTorsPts P.A p pt ∧ (∀ T : TorsRep P.A p, H.AA.carrier = torsFun C T pt) ∧ ∀ (a : OE) (t : TT p g), pt (red p g (H.ρ (1 ⊗ₜ[ℤ] a) *ᵥ t)) = pt (red p g t) ≫ o.act a := by
  intro p _ C _ _ _ v O _ iA hv iF iC iZ P h₄ g hg OE _ _ o F X hX α hα
  subst hg
  haveI : IsDomain O := Function.Injective.isDomain _ hv.hom_inj
  haveI : IsLocalRing O := Ainf.O_local O hv
  obtain ⟨R, P₀, φ, hft, hg₀, h₁, h₂⟩ := GlobalTheory.KeyTf.exists_polAV_finiteType_subring O P
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hvp : v (p : C) < 1 := by
    have h := lt_of_le_of_ne (hv.map_le_one (p : O)) fun h => iF.out (hv.isUnit_iff_valuation_eq_one.2 h)
    simpa using h
  obtain ⟨ε, hε⟩ := exists_eps (p := p) C v O hv
  exact ⟨_, GlobalTheory.T.hodgeTate_datum_hypotheses_period_tower p O hv ε hε OE,
    @htd_of_tower p _ C _ _ _ v O _ _ _ _ hv ε hε _ rfl iA hv iF
      iC iZ hvp R _ _ P₀ R.subtype P φ h₁ h₂ hg₀.symm h₄ OE _ _ o F X hX α hα⟩

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDeterminantLogDifferentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_determinant_log_different : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x : I → D.La) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x).det‖ = -(Fintype.card I : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.GramDet.log_norm_det_gramE | exact GlobalTheory.CompanionTheory.Ar.Fl.GramDet.log_norm_det_gramE | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.GramDet.log_norm_det_gramE <;> assumption)
end

