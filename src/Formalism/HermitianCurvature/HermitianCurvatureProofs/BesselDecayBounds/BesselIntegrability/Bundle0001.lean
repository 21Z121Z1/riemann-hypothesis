import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.DecayZeroRight.NormDec
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.UnitNorm.UnrealifyRealify

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.DoubleCosetDecomposition
section
open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.QuantumDeterminants

theorem norm_inverse_bound : Formalism.FourierDecayAlt.ThreeDimData.NormInv := fun k r =>
  ⟨(Formalism.MainNotions.InverseNormDecayBounds.normInvP k r).2, (Formalism.MainNotions.InverseNormDecayBounds.normInvP k r).1⟩

theorem double_coset_decomposition : Formalism.FourierDecayAlt.ThreeDimData.DecDD := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS x hx y hy
  obtain ⟨hHC, hσ, hgap, hOK, hw0, -⟩ := hS
  have hσ' : Formalism.MainNotions.S.IsDSHpk k r ε lam σ := hσ
  obtain ⟨P, hP, hw⟩ := hw0
  obtain ⟨C, hC⟩ := hIn.1 k r hOK.1 ε lam h H σ hHC hσ hgap hOK.2.1 P hP w0 w0 hw.2 hw.2
  have hD : Formalism.MainNotions.InverseNormDecayBounds.DiagonalMatrixCoefficientPowerDecay σ w0 (Formalism.FourierDecayAlt.ThreeDimData.aOf r h) := ⟨C, fun g hg => hC g hg⟩
  have hh : 0 ≤ h := le_trans (by positivity) hOK.2.1
  have ha : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h := div_nonneg hh (by positivity)
  exact Formalism.MainNotions.InverseNormDecayBounds.decDD hσ' ha hD x hx y hy

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.Growth
section
open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.GrowthW

open Formalism.QuantumDeterminants Formalism.MainNotions.S

def hsN {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, Complex.normSq (g i j))

theorem hsN_nonneg {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ hsN g :=
  Real.sqrt_nonneg _

def GrowthG : Prop :=
  ∀ (k r : ℕ) (μG : Measure (Mt k r)) (A : ℝ), Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B.GV k r) μG → Formalism.FourierDecayAlt.B.AB k r ≤ A →
    (∫⁻ g : Mt k r, ENNReal.ofReal (hsN (Matrix.of g) ^ (-A)) ∂μG) < ∞

def UWBound : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∃ C : ℝ, ∀ h ∈ UWset k r z, hsN h ≤ C

def SUpper {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Prop := ∀ i j : Fin m, j ≤ i → X i j = 0

def LieNUpper : Prop := ∀ (k r : ℕ) (X : Formalism.FourierDecayAlt.B.Mat k r), PI.WUN.InLieN k r X → SUpper X

def ExpUpper : Prop :=
  ∀ m : ℕ, 0 < m → ∃ C D : ℝ, 0 < D ∧ ∀ X : Matrix (Fin m) (Fin m) ℂ, SUpper X →
    1 + hsN X ≤ C * hsN (NormedSpace.exp X) ^ D

def GrowthS : Prop :=
  ∀ k r : ℕ, ∃ A0 : ℝ, 0 ≤ A0 ∧ ∀ (z : Fin (2 * r + k + 1) → ℂ) (μW : Measure (Mt k r)) (κN : ℝ≥0∞) (A : ℝ),
    inWb k r z → 0 < Tz k r z → μW {x | Matrix.of x ∉ UWset k r z} = 0 → IsFiniteMeasure μW → κN ≠ ∞ → A0 < A →
    (∫⁻ p : Mt k r × Mt k r, ENNReal.ofReal (hsN (Matrix.of p.1 * Matrix.of p.2) ^ (-A))
      ∂(μW.prod (haarLie (Nset k r) κN))) < ∞

section Assembly

variable {k r : ℕ}

theorem norm_le_hsN (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) :
    ‖x‖ ≤ hsN (unrealify x) := by
  rw [EuclideanSpace.norm_eq]
  unfold hsN
  apply le_of_eq
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [unrealify, Complex.normSq_mk, Real.norm_eq_abs, sq_abs]
  ring

abbrev EE (k r : ℕ) := EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)

end Assembly

end Formalism.MainNotions.GrowthW
end
end

