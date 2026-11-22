import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0024
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0050
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CutEffectiveDivisor
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Num.CutClosed

open GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.AutoClose

theorem verticalPush : BlowUpVerticalPush.Statement.{0} :=
  BlowUpVerticalPush.proof (BlowUpVerticalFibre.proof BlowUpModel.full
    (BlowUpFibreDegree.proof NumbersDVR_HomLocRingLocal NumbersDVR_DivCycleHomLoc
      FiniteBirationalLength.full GlobalTheory.T.blow_up_fibre_semilocal) GlobalTheory.T.projection_formula_degree)

theorem main : CutByEffectiveDivisor.Statement.{0} :=
  CutByEffectiveDivisor.of_steps NumbersDVR_C3NoCommon
    (CommonFactorInduction.of_open ReesAlgebraDim.full BlowUpStrictTransform.proof
      NumbersDVR_C3BlowUpExcessDrop verticalPush (BlowUpDivisorPush.proof verticalPush)
      NumbersDVR_BlowUpHorizontalCorresp HorizontalComponentModel.proof)

end GlobalTheory.CompanionTheory.Ar.Num.CutClosed
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix

open scoped ENNReal

noncomputable section

variable {m n : ℕ}

def ptsOver (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin m → Fin n → ℂ)
    (w : EuclideanSpace ℂ (Fin m)) : Set (EuclideanSpace ℂ (Fin n)) :=
  {y | y ∈ S ∧ linProj π y = w}

def cntOver (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin m → Fin n → ℂ)
    (w : EuclideanSpace ℂ (Fin m)) : ℝ≥0∞ :=
  (((ptsOver S π w).encard : ℕ∞) : ℝ≥0∞)

def IsScaleStable (S : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  ∀ y ∈ S, ∀ t : ℂ, t ≠ 0 → t • y ∈ S

def gaussM (m n : ℕ) : Measure (Fin m → Fin n → ℂ) :=
  (volume : Measure (Fin m → Fin n → ℂ)).withDensity matGauss

def planeMass (n e : ℕ) : ℝ≥0∞ :=
  Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
    {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}

def fibrePts {e : ℕ} (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  ptsOver S π (firstCoordVec (e + 1))

def fsSum {e : ℕ} (h : HermNorm n) (u : Fin n → ℂ) (S : Set (EuclideanSpace ℂ (Fin n)))
    (π : Fin (e + 1) → Fin n → ℂ) : ℝ :=
  ∑ᶠ y ∈ fibrePts S π, fsLog h u (h.pointOf y)

def coefRows {e : ℕ} (h : HermNorm n) (π : Fin (e + 1) → Fin n → ℂ) : Fin e × Fin n → ℂ :=
  fun ij => ((h.mat)⁻¹ *ᵥ π ij.1.succ) ij.2

open Classical in

def logGap (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) : ℝ≥0∞ :=
  if y = 0 then 0
  else if ∑ j, u j * h.pointOf y j = 0 then ⊤
  else ENNReal.ofReal (Real.log (h.norm u) - fsLog h u (h.pointOf y))

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

