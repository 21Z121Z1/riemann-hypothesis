import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGLStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_smooth_admissible_GL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.IrreducibleAdmissible k := by
  first | exact @GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible | exact GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible | (intros; apply GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasureInvertibleIntegralMatricesStatement
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_invertible_integral_matrices : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ r : ℕ, ∀ (dx : Measure (Matrix (Fin r) (Fin r) F)), dx.IsAddLeftInvariant → dx (intMat O r r) = 1 → MeasurableSet (Jset (GLint O r)) ∧ dx (Jset (GLint O r)) = ENNReal.ofReal (qE q 1 r) := by
  first | exact @GlobalTheory.CompanionTheory.QL.VolK.vol_GLint | exact GlobalTheory.CompanionTheory.QL.VolK.vol_GLint | (intros; apply GlobalTheory.CompanionTheory.QL.VolK.vol_GLint <;> assumption)
end

