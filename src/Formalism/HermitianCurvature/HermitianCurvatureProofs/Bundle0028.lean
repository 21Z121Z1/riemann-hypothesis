import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeightedL2ConstMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Markov
import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CharacterOrthogonalityDual
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelQuotientFinite
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelNonzeroModulusDeterminantEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelPropertiesOfHypotheses
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AddedBlockKernelSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelExplicitFormula
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0026
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TripleForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ColumnOperationTripleForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LatticeAverageIdentity

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.EnergyEstimateFromParts
section
namespace Formalism.FourierDecayAlt.P

theorem le_thetaForm_proof : Formalism.FourierDecayAlt.LE.ThetaForm := by
  intro ε σ hε v
  simp only [LE.th]
  have hv := Real.exp_pos v
  have h1 : Real.exp v / (Real.exp v + ε) = (1 + ε * Real.exp (-v))⁻¹ := by
    rw [Real.exp_neg]
    field_simp
    try ring
  rw [h1, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]

theorem le_thetaRange_proof : Formalism.FourierDecayAlt.LE.ThetaRange := by
  intro ε σ x hε hσ hx
  simp only [LE.th]
  have hb : 0 < x / (x + ε) := by positivity
  exact ⟨Real.rpow_pos_of_pos hb σ, Real.rpow_le_one hb.le ((div_le_one (by linarith)).mpr (by linarith)) hσ⟩

theorem le_thetaSmooth_proof : Formalism.FourierDecayAlt.LE.ThetaSmooth := Formalism.FourierDecayAlt.P.LEx1.thetaSmooth

theorem le_thetaBound_proof : Formalism.FourierDecayAlt.LE.ThetaBound := Formalism.FourierDecayAlt.P.LEx1.thetaBound

theorem theta_limit : Formalism.FourierDecayAlt.LE.ThetaLimit := Formalism.FourierDecayAlt.P.LEx1.thetaLimit

theorem le_thetaMono_proof : Formalism.FourierDecayAlt.LE.ThetaMono := by
  intro σ ε ε' x hσ hε hεε' hx
  simp only [LE.th]
  have hε' : 0 < ε' := by linarith
  have hb : 0 < x / (x + ε') := by positivity
  exact Real.rpow_le_rpow hb.le (by gcongr) hσ

theorem cutoff_bound : Formalism.FourierDecayAlt.LE.CutBound := Formalism.FourierDecayAlt.P.LEx1.cutBound

theorem cutoff_theta : Formalism.FourierDecayAlt.LE.CutTheta := Formalism.FourierDecayAlt.P.LEx1.cutTheta

theorem leibniz_rule : Formalism.FourierDecayAlt.LE.Leibniz := Formalism.FourierDecayAlt.P.LEx1.leibniz

theorem le_termZero_proof : Formalism.FourierDecayAlt.LE.TermZero := Formalism.FourierDecayAlt.P.LEx1.termZero

theorem measure_measurable : Formalism.FourierDecayAlt.LE.DsMeas := Formalism.FourierDecayAlt.P.LEx1.dsMeas

theorem coefficient_integrable : Formalism.FourierDecayAlt.LE.CoefIntegrable := Formalism.FourierDecayAlt.P.LEx1.coefIntegrable

theorem adjoint_identity : Formalism.FourierDecayAlt.LE.Adj := Formalism.FourierDecayAlt.P.LEx1.adj

theorem energy_finite : Formalism.FourierDecayAlt.LE.EFinite := Formalism.FourierDecayAlt.P.LEx1.eFinite

theorem cauchy_schwarz_term : Formalism.FourierDecayAlt.LE.CSTerm := Formalism.FourierDecayAlt.P.LEx1.csTerm

theorem le_shiftBound_proof : Formalism.FourierDecayAlt.LE.ShiftBound := Formalism.FourierDecayAlt.P.LEx1.shiftBound

theorem markov_term : Formalism.FourierDecayAlt.LE.MarkovTerm := Formalism.FourierDecayAlt.P.LEx1.markovTerm

theorem le_termBound_proof : Formalism.FourierDecayAlt.LE.TermBound := Formalism.FourierDecayAlt.P.LEx1.termBound

theorem geometric_sum_bound : Formalism.FourierDecayAlt.LE.GeomSum := by
  intro c x R hc hx hx1
  have ha0 : 0 ≤ Real.exp 1 * √c := by positivity
  have hden : 0 < 2 * (1 + 2 * Real.exp 1 * √c) := by positivity
  have hx1' : x * (2 * (1 + 2 * Real.exp 1 * √c)) ≤ 1 := by
    rw [le_div_iff₀ hden] at hx1
    exact hx1
  have hxlt : x < 1 := by nlinarith [mul_nonneg ha0 hx]
  have hgeom : ∑ p ∈ Finset.Icc 1 R, x ^ p ≤ x / (1 - x) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 1) (n := R + 1) hx hxlt
    rw [pow_one] at h
    have hI : Finset.Ico 1 (R + 1) = Finset.Icc 1 R := by
      ext p
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rwa [hI] at h
  have h2 : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg ha0 hx]
  rw [← Finset.mul_sum]
  calc Real.exp 1 * √c * ∑ p ∈ Finset.Icc 1 R, x ^ p ≤ Real.exp 1 * √c * (2 * x) :=
        mul_le_mul_of_nonneg_left (hgeom.trans h2) ha0
    _ ≤ 1 / 2 := by nlinarith [mul_nonneg ha0 hx]

theorem energy_estimate : Formalism.FourierDecayAlt.LE.EnergyStep := Formalism.FourierDecayAlt.P.LEx1.energyStep

theorem absorb_term : Formalism.FourierDecayAlt.LE.Absorb := Formalism.FourierDecayAlt.P.LEx1.absorb

theorem le_uniformBound_proof : Formalism.FourierDecayAlt.LE.UniformBound := Formalism.FourierDecayAlt.P.LEx1.uniformBound

theorem fatou_estimate : Formalism.FourierDecayAlt.LE.FatouStep := Formalism.FourierDecayAlt.P.LEx1.fatouStep

theorem dominated_convergence : Formalism.FourierDecayAlt.LE.DomConv := Formalism.FourierDecayAlt.P.LEx1.domConv

theorem energy_estimate_from_parts : Formalism.FourierDecayAlt.LE.StepClaimFromSteps := Formalism.FourierDecayAlt.P.LEx1.stepClaimFromSteps_full

theorem energy_estimate_of_lemmas : Formalism.FourierDecayAlt.LE.StepClaim :=
  Formalism.FourierDecayAlt.P.LEx1.stepClaimFromSteps_full Formalism.FourierDecayAlt.P.cauchy_theta_identity Formalism.FourierDecayAlt.P.markov_inequality_vector
    Formalism.FourierDecayAlt.P.LEx1.thetaForm Formalism.FourierDecayAlt.P.LEx1.thetaRange Formalism.FourierDecayAlt.P.LEx1.thetaSmooth Formalism.FourierDecayAlt.P.LEx1.thetaBound
    Formalism.FourierDecayAlt.P.LEx1.thetaLimit Formalism.FourierDecayAlt.P.LEx1.cutTheta Formalism.FourierDecayAlt.P.LEx1.leibniz Formalism.FourierDecayAlt.P.LEx1.termZero
    Formalism.FourierDecayAlt.P.LEx1.coefIntegrable Formalism.FourierDecayAlt.P.LEx1.adj Formalism.FourierDecayAlt.P.LEx1.eFinite Formalism.FourierDecayAlt.P.LEx1.csTerm
    Formalism.FourierDecayAlt.P.LEx1.shiftBound Formalism.FourierDecayAlt.P.LEx1.markovTerm Formalism.FourierDecayAlt.P.LEx1.termBound Formalism.FourierDecayAlt.P.LEx1.geomSum
    Formalism.FourierDecayAlt.P.LEx1.energyStep Formalism.FourierDecayAlt.P.LEx1.absorb Formalism.FourierDecayAlt.P.LEx1.uniformBound Formalism.FourierDecayAlt.P.LEx1.fatouStep
    Formalism.FourierDecayAlt.P.LEx1.domConv

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelProperties
section
namespace Formalism.FourierDecayAlt.P

theorem second_gram_property : Formalism.FourierDecayAlt.A5.BlockKernelPosSemidef := second_gram_of_gram_and_modulus kernel_gram_property modulus_positive_multiplicative

namespace FirstKernelProperties

theorem first_kernel_periodic_gram_parseval :
    Formalism.FourierDecayAlt.A5.SingleBlockPeriodic ∧ Formalism.FourierDecayAlt.A5.SingleBlockPosSemidef ∧ Formalism.FourierDecayAlt.A5.SingleBlockParseval :=
  first_kernel_properties_of_hypotheses first_kernel_explicit_formula integral_points_finite characterOrthogonalityDual
    characterOrthogonality cokernel_card_inverse_modulus second_gram_property

end FirstKernelProperties

theorem first_kernel_periodic : Formalism.FourierDecayAlt.A5.SingleBlockPeriodic := A5x6.first_kernel_periodic_of_formula first_kernel_explicit_formula

theorem first_kernel_gram_property : Formalism.FourierDecayAlt.A5.SingleBlockPosSemidef := A5x6.first_kernel_gram_of_second second_gram_property

theorem first_kernel_parseval : Formalism.FourierDecayAlt.A5.SingleBlockParseval := FirstKernelProperties.first_kernel_periodic_gram_parseval.2.2

namespace FirstKernelProperties

theorem th1All : Formalism.FourierDecayAlt.A5.Th1Eq ∧ Formalism.FourierDecayAlt.A5.SingleBlockThetaProps := ⟨A5x6.first_theta_eq_of_equality (A5x6.first_theta_equality_of_kernel_facts first_kernel_periodic first_kernel_gram_property first_kernel_parseval
    added_block_kernel_support added_block_kernel_block_diagonal),
    A5x6.first_theta_equality_of_kernel_facts first_kernel_periodic first_kernel_gram_property first_kernel_parseval
      added_block_kernel_support added_block_kernel_block_diagonal⟩

end FirstKernelProperties

theorem first_theta_kernel_equality : Formalism.FourierDecayAlt.A5.Th1Eq := A5x6.first_theta_eq_of_equality (A5x6.first_theta_equality_of_kernel_facts first_kernel_periodic first_kernel_gram_property first_kernel_parseval
    added_block_kernel_support added_block_kernel_block_diagonal)

theorem first_theta_equals_first_kernel : Formalism.FourierDecayAlt.A5.SingleBlockThetaProps := A5x6.first_theta_equality_of_kernel_facts first_kernel_periodic first_kernel_gram_property first_kernel_parseval
    added_block_kernel_support added_block_kernel_block_diagonal

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NeZeroOfAn
section
open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

def uu (TT : ℝ) (α : ℂ → ℂ) (ζ : ℂ) : ℂ := Complex.exp (I * (th TT α (Complex.log ζ) : ℂ))

theorem ne_zero_of_An (hTT : 0 ≤ TT) {ζ : ℂ} (hζ : ζ ∈ An TT) : ζ ≠ 0 := by
  rintro rfl
  simp [An] at hζ
  linarith

def br (s : Bool) (ζ : ℂ) : ℂ := if s then Complex.log ζ else Complex.log (-ζ) + Real.pi * I

def brD (s : Bool) : Set ℂ := if s then Complex.slitPlane else {ζ | -ζ ∈ Complex.slitPlane}

theorem isOpen_brD (s : Bool) : IsOpen (brD s) := by
  cases s
  · simp only [brD, Bool.false_eq_true, ↓reduceIte]
    exact Complex.isOpen_slitPlane.preimage continuous_neg
  · simp only [brD, ↓reduceIte]
    exact Complex.isOpen_slitPlane

theorem exp_br (s : Bool) {ζ : ℂ} (hζ : ζ ≠ 0) : Complex.exp (br s ζ) = ζ := by
  cases s
  · simp only [br, Bool.false_eq_true, ↓reduceIte]
    rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.mpr hζ), Complex.exp_pi_mul_I]
    ring
  · simp only [br, ↓reduceIte]
    exact Complex.exp_log hζ

theorem exists_br {ζ : ℂ} (hζ : ζ ≠ 0) : ∃ s, ζ ∈ brD s := by
  by_cases h : ζ ∈ Complex.slitPlane
  · exact ⟨true, by simpa [brD] using h⟩
  · refine ⟨false, ?_⟩
    simp only [brD, Bool.false_eq_true, ↓reduceIte, Set.mem_setOf_eq]
    rw [Complex.mem_slitPlane_iff] at h ⊢
    push_neg at h
    left
    rcases h with ⟨h1, h2⟩
    have h3 : ζ.re ≠ 0 := fun h0 => hζ (Complex.ext (by simpa using h0) (by simpa using h2))
    have h4 : ζ.re < 0 := lt_of_le_of_ne h1 h3
    simp only [Complex.neg_re]
    linarith

theorem hasDerivAt_br (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) : HasDerivAt (br s) ζ⁻¹ ζ := by
  cases s
  · simp only [brD, Bool.false_eq_true, ↓reduceIte, Set.mem_setOf_eq] at hs
    have e1 : br false = fun z : ℂ => Complex.log (-z) + Real.pi * I := by
      funext z
      simp [br]
    have h1 : HasDerivAt (fun z : ℂ => Complex.log (-z)) ((-ζ)⁻¹ * (-1)) ζ :=
      (Complex.hasDerivAt_log hs).comp ζ (hasDerivAt_neg ζ)
    have h2 := h1.add_const ((Real.pi : ℂ) * I)
    have e2 : (-ζ)⁻¹ * (-1) = ζ⁻¹ := by rw [inv_neg, neg_mul_neg, mul_one]
    rw [e2] at h2
    rw [e1]
    exact h2
  · simp only [brD, ↓reduceIte] at hs
    have e1 : br true = Complex.log := by
      funext z
      simp [br]
    rw [e1]
    exact Complex.hasDerivAt_log hs

theorem contDiffAt_br (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) : ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (br s) ζ := by
  have hd : DifferentiableOn ℂ (br s) (brD s) := fun z hz =>
    (hasDerivAt_br s hz).differentiableAt.differentiableWithinAt
  exact (hd.contDiffOn (isOpen_brD s)).contDiffAt ((isOpen_brD s).mem_nhds hs)

theorem br_mem_Hh (s : Bool) (hTT : 0 ≤ TT) {ζ : ℂ} (hζ : ζ ∈ An TT) : br s ζ ∈ Hh TT := by
  show Complex.exp (br s ζ) ∈ An TT
  rw [exp_br s (ne_zero_of_An hTT hζ)]
  exact hζ

theorem uu_eq_br (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) (s : Bool) {ζ : ℂ} (hζ : ζ ∈ An TT) :
    uu TT α ζ = Complex.exp (I * (th TT α (br s ζ) : ℂ)) := by
  unfold uu
  have h0 := ne_zero_of_An hTT hζ
  exact expI_th_eq hTT hα hcurv hhol (br_mem_Hh true hTT hζ) (br_mem_Hh s hTT hζ)
    (by rw [Complex.exp_log h0, exp_br s h0])

theorem norm_uu (ζ : ℂ) : ‖uu TT α ζ‖ = 1 := by
  rw [uu, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondVanishingOffRing
section
namespace Formalism.FourierDecayAlt.P

theorem second_gram_and_vanishing : Formalism.FourierDecayAlt.A5.A2 :=
  second_gram_vanishing_of_parts kernel_gram_property modulus_positive_multiplicative tripleForm
    lattice_average_identity triple_form_end_identity

theorem second_vanishing_off_ring : Formalism.FourierDecayAlt.A5.BlockKernelSupport := second_gram_and_vanishing.2

end Formalism.FourierDecayAlt.P
end

