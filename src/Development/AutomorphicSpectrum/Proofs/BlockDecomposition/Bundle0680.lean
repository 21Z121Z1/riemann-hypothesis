import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveVectorsContentDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0653
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionRegularOnNonvanishingChart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0663
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.Bundle0001
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.HasFDerivAtPm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0665
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import GroundTheory.GlobalFields.TateThesis.Bundle0001
import GroundTheory.GlobalFields.TateThesis.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictGradedPullNatural
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0666
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveVectorsContentDecompositionStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_vectors_content_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (ι : Type) (c : ι → Fv F v ⊗[F] E) (w : ι → ℕ), IsContent σ b v c w → MeasurableSet (primV σ J b v) ∧ (∀ i, ∀ y ∈ primV σ J b v, scalT (c i) y ∈ latV b v) ∧ (∀ i j, ∀ y ∈ primV σ J b v, ∀ y' ∈ primV σ J b v, scalT (c i) y = scalT (c j) y' → i = j) ∧ (∀ y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ (hypOne J) y = 0 → y ∈ latV b v → ∃ i, ∃ y₀ ∈ primV σ J b v, y = scalT (c i) y₀) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypMass.PrimDec.eventually_primV_decomposition | exact GlobalTheory.CompanionTheory.WeilSiegel.HypMass.PrimDec.eventually_primV_decomposition | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypMass.PrimDec.eventually_primV_decomposition <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProfileIntegrable
section
open MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Parseval.OneDim

open GlobalTheory.CompanionTheory.Parseval

lemma profile_integrable : Integrable (fun t : ℝ => ((1 + |t|) ^ 2)⁻¹) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  have hp : (0 : ℝ) < 1 + |t| := by positivity
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg hp.le, Real.rpow_two]

lemma wt_eq_comp (a l ζ : ℝ) (ha : 0 < a) :
    wt a l ζ = (fun t : ℝ => (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹) (t / a)) (ζ - l) := by
  simp only [wt, abs_div, abs_of_pos ha]

lemma wt_integrable (a l : ℝ) (ha : 0 < a) : Integrable (wt a l) := by
  have h1 := profile_integrable.comp_div ha.ne'
  have h2 := h1.comp_sub_right l
  exact h2.congr (Filter.Eventually.of_forall fun ζ => (wt_eq_comp a l ζ ha).symm)

lemma wt_integral (a l : ℝ) (ha : 0 < a) :
    ∫ ζ, wt a l ζ = a * ∫ t : ℝ, ((1 + |t|) ^ 2)⁻¹ := by
  have h : wt a l = fun ζ => (fun t : ℝ => (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹) (t / a)) (ζ - l) :=
    funext fun ζ => wt_eq_comp a l ζ ha
  rw [h, integral_sub_right_eq_self (fun t : ℝ => (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹) (t / a)) l,
    Measure.integral_comp_div (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹) a, abs_of_pos ha, smul_eq_mul]

lemma wt_le_near {a l ζ : ℝ} (ha : 0 < a) (hl : l ≠ 0) (h : |ζ| < |l| / 2) :
    wt a l ζ ≤ 2 * a / |l| := by
  have hlp : 0 < |l| := abs_pos.2 hl
  have h1 : |l| / 2 ≤ |ζ - l| := by
    have := abs_sub_abs_le_abs_sub l ζ
    rw [abs_sub_comm l ζ] at this
    linarith
  have hy : |l| / (2 * a) ≤ |ζ - l| / a := by
    rw [div_le_div_iff₀ (by positivity) ha]
    nlinarith
  have hy0 : 0 < |l| / (2 * a) := by positivity
  set y := |ζ - l| / a with hydef
  have hypos : 0 < y := lt_of_lt_of_le hy0 hy
  have h2 : ((1 + y) ^ 2)⁻¹ ≤ y⁻¹ := by
    apply inv_anti₀ hypos
    nlinarith
  have h3 : y⁻¹ ≤ (|l| / (2 * a))⁻¹ := inv_anti₀ hy0 hy
  have h4 : (|l| / (2 * a))⁻¹ = 2 * a / |l| := inv_div _ _
  calc wt a l ζ = ((1 + y) ^ 2)⁻¹ := rfl
    _ ≤ 2 * a / |l| := by rw [← h4]; exact h2.trans h3

lemma gau_le_far {ε l ζ : ℝ} (hε : 0 < ε) (hl : l ≠ 0) (h : |l| / 2 ≤ |ζ|) :
    gau ε ζ ≤ 1 / |l| := by
  have hlp : 0 < |l| := abs_pos.2 hl
  set x := |l| / ε with hx
  have hxp : 0 < x := by positivity
  have hpi := Real.pi_gt_three
  set u := Real.pi * x ^ 2 / 4 with hu
  have h1 : x ≤ Real.exp u := by
    have := Real.add_one_le_exp u
    have hx2 : 3 * x ^ 2 / 4 ≤ u := by
      rw [hu]
      have : 0 ≤ x ^ 2 := sq_nonneg x
      nlinarith
    nlinarith [sq_nonneg (x - 1), sq_nonneg x]
  have h2 : Real.exp (-u) ≤ x⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hxp h1
  have h3 : -Real.pi * ζ ^ 2 / ε ^ 2 ≤ -u := by
    have hz : |l| ^ 2 / 4 ≤ ζ ^ 2 := by
      rw [← sq_abs ζ]
      nlinarith
    have hux : u = Real.pi * (|l| ^ 2 / 4) / ε ^ 2 := by
      rw [hu, hx]; field_simp
    rw [hux, neg_mul, neg_div, neg_le_neg_iff]
    gcongr
  have h4 : Real.exp (-Real.pi * ζ ^ 2 / ε ^ 2) ≤ x⁻¹ := (Real.exp_le_exp.2 h3).trans h2
  unfold gau
  calc ε⁻¹ * Real.exp (-Real.pi * ζ ^ 2 / ε ^ 2) ≤ ε⁻¹ * x⁻¹ := by gcongr
    _ = 1 / |l| := by rw [hx]; field_simp

lemma wt_mul_gau_le {ε a l : ℝ} (hε : 0 < ε) (ha : 0 < a) (hl : l ≠ 0) (ζ : ℝ) :
    wt a l ζ * gau ε ζ ≤ 2 * a / |l| * gau ε ζ + 1 / |l| * wt a l ζ := by
  have hlp : 0 < |l| := abs_pos.2 hl
  have hw := wt_nonneg a l ζ
  have hg := gau_nonneg ε ζ hε
  by_cases h : |ζ| < |l| / 2
  · have h1 := mul_le_mul_of_nonneg_right (wt_le_near ha hl h) hg
    have h2 : 0 ≤ 1 / |l| * wt a l ζ := by positivity
    linarith
  · have h1 := mul_le_mul_of_nonneg_left (gau_le_far hε hl (not_lt.1 h)) hw
    have h2 : 0 ≤ 2 * a / |l| * gau ε ζ := by positivity
    rw [mul_comm (wt a l ζ) (1 / |l|)] at h1
    have : wt a l ζ * gau ε ζ ≤ 1 / |l| * wt a l ζ := by
      rw [mul_comm (1 / |l|)]; rw [mul_comm (1 / |l|)] at h1; exact h1
    linarith

theorem wt_gau_bound :
    ∃ C : ℝ, ∀ ε a l : ℝ, 0 < ε → 0 < a → l ≠ 0 →
      ∫ ζ : ℝ, GlobalTheory.CompanionTheory.Parseval.wt a l ζ * GlobalTheory.CompanionTheory.Parseval.gau ε ζ ≤ C * (a / |l|) := by
  refine ⟨2 + ∫ t : ℝ, ((1 + |t|) ^ 2)⁻¹, fun ε a l hε ha hl => ?_⟩
  have hlp : 0 < |l| := abs_pos.2 hl
  have hgi := gau_integrable ε hε
  have hwi := wt_integrable a l ha
  have hR : Integrable (fun ζ => 2 * a / |l| * gau ε ζ + 1 / |l| * wt a l ζ) :=
    (hgi.const_mul _).add (hwi.const_mul _)
  have hL : Integrable (fun ζ => wt a l ζ * gau ε ζ) := by
    refine hR.mono' ?_ (Filter.Eventually.of_forall fun ζ => ?_)
    · exact (hwi.aestronglyMeasurable).mul hgi.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (wt_nonneg a l ζ) (gau_nonneg ε ζ hε))]
      exact wt_mul_gau_le hε ha hl ζ
  have hmono := integral_mono hL hR (fun ζ => wt_mul_gau_le hε ha hl ζ)
  have hval : ∫ ζ, (2 * a / |l| * gau ε ζ + 1 / |l| * wt a l ζ)
      = (2 + ∫ t : ℝ, ((1 + |t|) ^ 2)⁻¹) * (a / |l|) := by
    rw [integral_add (hgi.const_mul _) (hwi.const_mul _), integral_const_mul, integral_const_mul,
      gau_integral ε hε, wt_integral a l ha]
    ring
  exact hmono.trans_eq hval

end GlobalTheory.CompanionTheory.Parseval.OneDim
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionRegularOnNonvanishingChartStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_regular_on_nonvanishing_chart : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (N : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog N a →
    ∀ (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ),
      y ∈ c.e.source → GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z → eval z (map (Int.castRingHom ℂ) N) ≠ 0 → Ψ (segre z) 0 ≠ 0 →
      GlobalTheory.CompanionTheory.MixZ.ArchEq.IsRegAt i Ψ c y → y ∈ GlobalTheory.CompanionTheory.MixZ.ArchEq.pieceSet i Ψ N := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.PieceAt.mem_pieceSet | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.PieceAt.mem_pieceSet | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.PieceAt.mem_pieceSet <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackCoverStarCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_cover_star_compat : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι)
    (hτ : ∀ n (i : Fin (n + 1) → U.ι), capO U.U i ≤ u ⁻¹ᵁ capO W.U (τ ∘ i)) (a : ℕ),
    ∃ hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T),
      ∀ α T, Vk q U a α T → Vk p W a (τ α) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T) := by
  first | exact @GlobalTheory.CompanionTheory.OmGlobPush.push_kc | exact GlobalTheory.CompanionTheory.OmGlobPush.push_kc | (intros; apply GlobalTheory.CompanionTheory.OmGlobPush.push_kc <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Qf
section
noncomputable section

open MeasureTheory Matrix Ad3.LR Ad3.LR.DTr

namespace GlobalTheory.CompanionTheory.DInt2

def al (h : M22) : ℂ := (h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I

def be (h : M22) : ℂ := (h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I

def dd (h X : M22) : ℝ := X 0 0 * h 1 1 + h 0 0 * X 1 1 - X 0 1 * h 1 0 - h 0 1 * X 1 0

def uu (h : M22) : ℝ := (Matrix.of h).det / ‖al h‖ ^ 2

def tt (h : M22) : ℂ := (((Matrix.of h).det : ℝ) : ℂ) / al h ^ 2

def rho (c d : Fin 2) (h : M22) : ℂ := al (rpol c d h) / al h

def kap (a b : Fin 2) : ℂ := (if b = 0 then 1 else Complex.I) * (if a = 0 then -Complex.I else 1)

def ell (k : ℕ) (h X : M22) : ℂ :=
  ((k : ℂ) - 1) * (dd h X : ℂ) / (((Matrix.of h).det : ℝ) : ℂ) + (1 - 2 * (k : ℂ)) * al X / al h +
    2 * Real.pi * Complex.I * (be X * al h - be h * al X) / al h ^ 2

def Qf (k : ℕ) (v : ℂ) (c d : Fin 2) (h : M22) : ℂ :=
  (if c = d then v - 2 - ((k : ℂ) - 1) else 0) + (2 * (k : ℂ) - 1) * rho c d h -
    2 * Real.pi * Complex.I * kap c d * tt h

end GlobalTheory.CompanionTheory.DInt2
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalElementIntegralAlmostAllStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_element_integral_almost_all : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (δ : GL (Fin n) E), ∀ᶠ w : Pl E in cofinite, ratW n w δ ∈ GlobalTheory.LFun.KGL w n := by
  first | exact @GlobalTheory.CompanionTheory.LocalHypotheses.ratW_mem_KGL_eventually | exact GlobalTheory.CompanionTheory.LocalHypotheses.ratW_mem_KGL_eventually | (intros; apply GlobalTheory.CompanionTheory.LocalHypotheses.ratW_mem_KGL_eventually <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealTateLocalFactor
section
noncomputable section
open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C
namespace GlobalTheory.CompanionTheory.TateR

theorem chR_mul (e : Bool) (s : ℂ) (t b : ℝˣ) :
    chR e (1 - s) (t * b) * chR e s b = chR e (1 - s) t * ((|(b : ℝ)| : ℝ) : ℂ) := by
  have hb : ((|(b : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr b.ne_zero
  have hc : (((|((t * b : ℝˣ) : ℝ)| : ℝ) : ℂ)) ^ (1 - s) * ((|(b : ℝ)| : ℝ) : ℂ) ^ s
      = ((|(t : ℝ)| : ℝ) : ℂ) ^ (1 - s) * ((|(b : ℝ)| : ℝ) : ℂ) := by
    rw [Units.val_mul, abs_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (abs_nonneg _), mul_assoc, ← cpow_add _ _ hb]
    simp
  have hsg : (if e = true ∧ ((t * b : ℝˣ) : ℝ) < 0 then (-1 : ℂ) else 1)
      * (if e = true ∧ (b : ℝ) < 0 then (-1 : ℂ) else 1)
      = (if e = true ∧ (t : ℝ) < 0 then (-1 : ℂ) else 1) := by
    cases e
    · simp
    · have hb0 := b.ne_zero
      have ht0 := t.ne_zero
      rcases lt_or_gt_of_ne hb0 with h1 | h1 <;> rcases lt_or_gt_of_ne ht0 with h2 | h2
      · simp [h1, h2, mul_pos_of_neg_of_neg h2 h1, not_lt.mpr (mul_pos_of_neg_of_neg h2 h1).le]
      · simp [h2, h1, mul_neg_of_pos_of_neg h2 h1, not_lt.mpr h2.le]
      · simp [h1, h2, mul_neg_of_neg_of_pos h2 h1, not_lt.mpr h1.le]
      · simp [h1, h2, not_lt.mpr h1.le, not_lt.mpr h2.le, not_lt.mpr (mul_pos h2 h1).le]
  simp only [chR]
  calc _ = ((if e = true ∧ ((t * b : ℝˣ) : ℝ) < 0 then (-1 : ℂ) else 1)
      * (if e = true ∧ (b : ℝ) < 0 then (-1 : ℂ) else 1))
      * ((((|((t * b : ℝˣ) : ℝ)| : ℝ) : ℂ)) ^ (1 - s) * ((|(b : ℝ)| : ℝ) : ℂ) ^ s) := by ring
    _ = _ := by rw [hsg, hc]; ring

theorem tate_zeta_product (F G : ℝ → ℂ) (e : Bool) (s : ℂ)
    (hF : Integrable (fun a : ℝˣ => F a * chR e (1 - s) a) mulR)
    (hG : Integrable (fun a : ℝˣ => G a * chR e s a) mulR) :
    z1 F e (1 - s) * z1 G e s = ∫ t : ℝˣ, chR e (1 - s) t * (∫ x : ℝ, G x * F (t * x)) ∂mulR := by
  set A : ℝˣ → ℂ := fun a => F a * chR e (1 - s) a with hA
  set B : ℝˣ → ℂ := fun a => G a * chR e s a with hB
  have hP : Integrable (fun p : ℝˣ × ℝˣ => A p.1 * B p.2) (mulR.prod mulR) := hF.mul_prod hG
  have hT := measurePreserving_mul_prod (mulR) (mulR)
  have hP' : Integrable (fun p : ℝˣ × ℝˣ => A (p.1 * p.2) * B p.2) (mulR.prod mulR) :=
    hT.integrable_comp_of_integrable hP
  have h1 : z1 F e (1 - s) * z1 G e s = ∫ b, ∫ t, A (t * b) * B b ∂mulR ∂mulR := by
    change (∫ a, A a ∂mulR) * (∫ b, B b ∂mulR) = _
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    simp only
    rw [integral_mul_const, integral_mul_right_eq_self A b]
  rw [h1, ← integral_integral_swap (f := fun t b => A (t * b) * B b) hP']
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  have h2 : ∀ b : ℝˣ, A (t * b) * B b
      = chR e (1 - s) t * (((|(b : ℝ)| : ℝ) : ℂ) * (G b * F (t * b))) := by
    intro b
    have := chR_mul e s t b
    simp only [hA, hB, Units.val_mul]
    calc _ = F (t * b) * G b * (chR e (1 - s) (t * b) * chR e s b) := by
          ring
      _ = _ := by rw [this]; ring
  simp only [h2]
  rw [integral_const_mul]
  congr 1
  rw [integral_mulR (fun x : ℝ => ((|x| : ℝ) : ℂ) * (G x * F (t * x)))]
  refine integral_congr_ae ?_
  have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
  filter_upwards [h0] with x hx
  have : ((|x|⁻¹ : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (abs_ne_zero.mpr hx)]
    simp
  rw [← mul_assoc, this, one_mul]

theorem fourier_scaled_swap (f g : SchwartzMap ℝ ℂ) (t : ℝ) :
    ∫ x : ℝ, g x * (SchwartzMap.fourierTransformCLM ℂ f) (t * x)
      = ∫ x : ℝ, f x * (SchwartzMap.fourierTransformCLM ℂ g) (t * x) := by
  have hL : Continuous fun p : ℝ × ℝ => (t • LinearMap.mul ℝ ℝ) p.1 p.2 := by
    simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    fun_prop
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (L := t • LinearMap.mul ℝ ℝ)
    (f := (f : ℝ → ℂ)) (g := (g : ℝ → ℂ)) Real.continuous_fourierChar hL f.integrable g.integrable
  have hF : ∀ (h : SchwartzMap ℝ ℂ) (y : ℝ), (SchwartzMap.fourierTransformCLM ℂ h) (t * y)
      = VectorFourier.fourierIntegral Real.fourierChar volume (t • LinearMap.mul ℝ ℝ) (h : ℝ → ℂ) y := by
    intro h y
    rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe, Real.fourier_real_eq,
      VectorFourier.fourierIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    congr 3
    ring
  have hF' : ∀ (h : SchwartzMap ℝ ℂ) (y : ℝ), (SchwartzMap.fourierTransformCLM ℂ h) (t * y)
      = VectorFourier.fourierIntegral Real.fourierChar volume (t • LinearMap.mul ℝ ℝ).flip (h : ℝ → ℂ) y := by
    intro h y
    rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe, Real.fourier_real_eq,
      VectorFourier.fourierIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    congr 3
    ring
  simp only [hF f, hF' g]
  simp only [smul_eq_mul] at key
  rw [← key]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

theorem tate_zeta_symmetric (hI : TateInt) (f g : SchwartzMap ℝ ℂ) (e : Bool) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    z1 (SchwartzMap.fourierTransformCLM ℂ f) e (1 - s) * z1 g e s
      = z1 (SchwartzMap.fourierTransformCLM ℂ g) e (1 - s) * z1 f e s := by
  have h1' : 0 < (1 - s).re := by simpa using h1
  rw [tate_zeta_product _ _ e s (hI _ e _ h1') (hI _ e _ h0), tate_zeta_product _ _ e s (hI _ e _ h1') (hI _ e _ h0)]
  simp only [fourier_scaled_swap f g]

theorem tate_integral_eq_plane_integral (F : ℝ → ℂ) (e : Bool) (s : ℂ) : z1 F e s =
    ∫ x : ℝ, ((|x|⁻¹ : ℝ) : ℂ) * (F x * ((if e = true ∧ x < 0 then (-1 : ℂ) else 1) * ((|x| : ℝ) : ℂ) ^ s)) :=
  integral_mulR (fun x : ℝ => F x * ((if e = true ∧ x < 0 then (-1 : ℂ) else 1) * ((|x| : ℝ) : ℂ) ^ s))

theorem tate_zeta_gaussian (s : ℂ) (hs : 0 < s.re) : z1 GroundTheory.Global.realGaussian false s = Gammaℝ s := by
  rw [tate_integral_eq_plane_integral, ← GroundTheory.Global.integral_realGaussian_mul_abs_cpow hs]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Bool.false_eq_true, false_and, if_false, one_mul, Complex.ofReal_inv]
  rw [div_eq_mul_inv]
  ring

theorem tate_integral_odd_gaussian (s : ℂ) (hs : 0 < s.re) : z1 GroundTheory.Global.realGaussianOdd true s = Gammaℝ (s + 1) := by
  rw [tate_integral_eq_plane_integral, ← GroundTheory.Global.integral_realGaussianOdd_mul_sign_mul_abs_cpow (s := s) (by linarith)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [true_and, Complex.ofReal_inv]
  rcases lt_trichotomy x 0 with h | h | h
  · rw [if_pos h, Real.sign_of_neg h, div_eq_mul_inv]
    push_cast
    ring
  · subst h
    simp
  · rw [if_neg (not_lt.mpr h.le), Real.sign_of_pos h, div_eq_mul_inv]
    push_cast
    ring

theorem gaussS_coe : (GroundTheory.Global.gaussianSchwartz ℝ : ℝ → ℂ) = GroundTheory.Global.realGaussian := by
  funext x
  rw [GroundTheory.Global.gaussianSchwartz_apply, GroundTheory.Global.realGaussian_eq_ofReal]
  simp

theorem gaussEven : ∃ g : SchwartzMap ℝ ℂ, ∀ s : ℂ, 0 < s.re →
    z1 g false s = Gammaℝ s ∧ z1 (SchwartzMap.fourierTransformCLM ℂ g) false s = Gammaℝ s := by
  refine ⟨GroundTheory.Global.gaussianSchwartz ℝ, fun s hs => ?_⟩
  have h : ((SchwartzMap.fourierTransformCLM ℂ (GroundTheory.Global.gaussianSchwartz ℝ) : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = GroundTheory.Global.realGaussian := by
    rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe, gaussS_coe,
      GroundTheory.Global.fourier_realGaussian]
  rw [h, gaussS_coe]
  exact ⟨tate_zeta_gaussian s hs, tate_zeta_gaussian s hs⟩

theorem gaussOdd : ∃ g : SchwartzMap ℝ ℂ, ∀ s : ℂ, 0 < s.re →
    z1 g true s = Gammaℝ (s + 1) ∧
      z1 (SchwartzMap.fourierTransformCLM ℂ g) true s = -I * Gammaℝ (s + 1) := by
  set g₁ : SchwartzMap ℝ ℂ :=
    (-(1 / (2 * Real.pi)) : ℂ) • SchwartzMap.derivCLM ℂ ℂ (GroundTheory.Global.gaussianSchwartz ℝ) with hg₁
  have hc : (g₁ : ℝ → ℂ) = GroundTheory.Global.realGaussianOdd := by
    funext x
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [hg₁, SchwartzMap.smul_apply, SchwartzMap.derivCLM_apply, gaussS_coe,
      (GroundTheory.Global.hasDerivAt_realGaussian x).deriv, GroundTheory.Global.realGaussianOdd,
      ← GroundTheory.Global.realGaussian, smul_eq_mul]
    field_simp
  have hf : ((SchwartzMap.fourierTransformCLM ℂ g₁ : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = fun y => -I * GroundTheory.Global.realGaussianOdd y := by
    rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe, hc,
      GroundTheory.Global.fourier_realGaussianOdd]
  refine ⟨g₁, fun s hs => ?_⟩
  rw [hf, hc]
  refine ⟨tate_integral_odd_gaussian s hs, ?_⟩
  rw [← tate_integral_odd_gaussian s hs]
  simp only [z1, mul_assoc]
  rw [integral_const_mul]

theorem tateR_of_int (hI : TateInt) : TateR := by
  intro f e s h0 h1
  have h1' : 0 < (1 - s).re := by simpa using h1
  cases e
  · obtain ⟨g, hg⟩ := gaussEven
    have key := tate_zeta_symmetric hI f g false s h0 h1
    rw [(hg s h0).1, (hg _ h1').2] at key
    have hne := Gammaℝ_ne_zero_of_re_pos h0
    simp only [gT, Bool.false_eq_true, if_false, add_zero, one_mul]
    field_simp
    linear_combination key
  · obtain ⟨g, hg⟩ := gaussOdd
    have key := tate_zeta_symmetric hI f g true s h0 h1
    rw [(hg s h0).1, (hg _ h1').2] at key
    have hne : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    simp only [gT, if_true]
    field_simp
    linear_combination key

theorem tateR : TateR := tateR_of_int GlobalTheory.T.archimedean_tate_integral

end GlobalTheory.CompanionTheory.TateR
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictGradedPullNaturalStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrict_graded_pull_natural : ∀ (K : Type) [CommRing K], ∃ m : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a : ℕ),
    CH.Mor ((KS (V.ι ≫ q) s {⊤}).ι ⋙ HT.grT (smFun V.toScheme (V.ι ≫ q)) a) ((KS q s {V}).ι ⋙ HT.grT (smFun X q) a)
      (RingHom.id K),
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a n : ℕ), Function.Bijective ((m q V s a).pull n)) ∧
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q)
      (V : X.Opens) (W : Y.Opens) (h : V ≤ u ⁻¹ᵁ W) (hh : u.resLE W V h ≫ (W.ι ≫ p) = V.ι ≫ q) (s a : ℕ)
      (hG : ∀ T, KS q s {V} T → KS p s {W} ((pullM u hu a).G.obj T))
      (hG' : ∀ T, KS (V.ι ≫ q) s {⊤} T → KS (W.ι ≫ p) s {⊤} ((pullM (u.resLE W V h) hh a).G.obj T)) (n : ℕ) x,
      (m q V s a).pull n ((morU (pullM (u.resLE W V h) hh a) (U := KS (W.ι ≫ p) s {⊤}) (U' := KS (V.ι ≫ q) s {⊤}) hG').pull n x) =
        (morU (pullM u hu a) (U := KS p s {W}) (U' := KS q s {V}) hG).pull n ((m p W s a).pull n x) := by
  first | exact @GlobalTheory.CompanionTheory.OpenThick.open_thick | exact GlobalTheory.CompanionTheory.OpenThick.open_thick | (intros; apply GlobalTheory.CompanionTheory.OpenThick.open_thick <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Row1
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel
noncomputable section

namespace GlobalTheory.CompanionTheory.GJTwo

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def mx (r : Fin 2 → F) : ℝ := max (modulus (r 0) : ℝ) (modulus (r 1) : ℝ)

def row1 (r₂ : Fin 2 → F) (x y : F) : Fin 2 → F := ![y / r₂ 1 + x * r₂ 0, x * r₂ 1]

def cM (ψ : AddChar F Circle) : Measure ((Fin 2 → F) × F × F) :=
  (LFS.vol2 ψ).prod ((selfDualMeasure ψ).prod (selfDualMeasure ψ))

open Classical in

def Ff (f : GL (Fin 2) F → ℂ) (p : (Fin 2 → F) × F × F) : ℂ :=
  if h : p.2.2 = 0 ∨ p.1 1 = 0 then 0 else
    f (uni2 p.2.1 * dg2 (Units.mk0 p.2.2 (fun e => h (Or.inl e))) 1 * hr p.1) *
      (((modulus p.2.2 : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ)

def zI (W : GL (Fin 2) F → ℂ) (μ : Fˣ →* ℂˣ) (s : ℂ) (g : GL (Fin 2) F) : F → ℂ :=
  onU fun a => W (dg2 a 1 * g) * ((μ a : ℂˣ) : ℂ) * mp a (s - 3 / 2)

end D

end GlobalTheory.CompanionTheory.GJTwo
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowRepsDistinctCosetsStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_reps_distinct_cosets : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a b : Σ _ : ℕ, Σ j : ℕ, (Fin j → 𝓀[F])),
  rowRep a.1 a.2.1 a.2.2 * (rowRep b.1 b.2.1 b.2.2)⁻¹ ∈ integralGL F 2 → a = b := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.rowRep_unique | exact GlobalTheory.CompanionTheory.LFUDom.rowRep_unique | (intros; apply GlobalTheory.CompanionTheory.LFUDom.rowRep_unique <;> assumption)
end

