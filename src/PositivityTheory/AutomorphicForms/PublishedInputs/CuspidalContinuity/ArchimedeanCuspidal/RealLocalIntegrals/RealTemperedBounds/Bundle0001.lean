import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.StepsD
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealSharpBounds.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.RotationScalingMulVecSnd
section
noncomputable section

open MeasureTheory Matrix Complex

namespace Ad3.LR.DK

def al (h : M22) : ℂ := (h 0 0 : ℂ) + (h 1 0 : ℂ) * I

def sq4 (h : M22) : ℝ := ∑ r, ∑ c, h r c ^ 2

def Gc (k : ℕ) (c0 c1 : Fin 2 → ℝ) : ℂ :=
  if 0 < c0 0 * c1 1 - c1 0 * c0 1 then
    (((c0 0 * c1 1 - c1 0 * c0 1 : ℝ)) : ℂ) ^ (k - 2) *
      cexp (2 * Real.pi * I * (((c1 0 : ℂ) + (c1 1 : ℂ) * I) / ((c0 0 : ℂ) + (c0 1 : ℂ) * I)) -
        Real.pi * ((c0 0 ^ 2 + c0 1 ^ 2 + c1 0 ^ 2 + c1 1 ^ 2 : ℝ) : ℂ) -
        Real.pi * (((c0 0 ^ 2 + c0 1 ^ 2) / (c0 0 * c1 1 - c1 0 * c0 1) ^ 2 : ℝ) : ℂ))
  else 0

def Mc (c0 : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c0 0, -c0 1; c0 1, c0 0]

def Fr (k : ℕ) (s t : ℝ) : ℝ :=
  if 0 < t then (s * t) ^ (k - 2) * s⁻¹ ^ (1 / 2 : ℝ) *
    Real.exp (-2 * Real.pi * t - Real.pi * s - Real.pi * s * t ^ 2 - Real.pi / (s * t ^ 2) - Real.pi / s)
  else 0

def colE : M22 ≃ᵐ (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  (MeasurableEquiv.piCongrRight (fun _ : Fin 2 => MeasurableEquiv.finTwoArrow)).trans
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 2))

def sI (k : ℕ) (Φ : Sw) (h : M22) : ℂ :=
  Wm k (Matrix.of h)⁻¹ * inn Φ 1 (Matrix.of h) * sg (Matrix.of h).det *
    ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)

end Ad3.LR.DK

namespace Ad3.LR

open DK

end Ad3.LR
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.TrDefs
section
noncomputable section

open MeasureTheory Matrix

namespace Ad3.LR.DTr

def TrLim : Prop := ∀ (Ψ : Sw) (g : GL (Fin 3) ℝ) (a b : Fin 2) (w : M22 → ℂ),
  (∀ h : M22, (Matrix.of h).det < 0 → w h = 0) → ContDiffOn ℝ 1 w {h : M22 | 0 < (Matrix.of h).det} →
  Integrable (fun h : M22 => w h * inn Ψ g (Matrix.of h)) →
  Integrable (fun h : M22 => w h * inn (Rp a b Ψ) g (Matrix.of h)) →
  Integrable (fun h : M22 => Lop a b w h * inn Ψ g (Matrix.of h)) →
  ∫ h, w h * inn (Rp a b Ψ) g (Matrix.of h) = ∫ h, Lop a b w h * inn Ψ g (Matrix.of h)

def WeightVanishesNegDetSmoothPosDet : Prop := ∀ k : ℕ, 3 ≤ k →
  (∀ h : M22, (Matrix.of h).det < 0 → w0 k h = 0) ∧ ContDiffOn ℝ (⊤ : ℕ∞) (w0 k) {h : M22 | 0 < (Matrix.of h).det}

def DInt1 : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (v : ℂ) (a b : Fin 2) (Φ : Sw) (g : GL (Fin 3) ℝ),
  Integrable (fun h : M22 => Lt v a b (w0 k) h * inn Φ g (Matrix.of h))

end Ad3.LR.DTr
end
end

