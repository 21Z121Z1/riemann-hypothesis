import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBasisIntegralOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0048
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBasisIntegralUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0635
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0636
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergEulerProductPartial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0637
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalFourth

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBasisIntegralOrderStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_basis_integral_order : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (b₂ : Module.Basis (Fin 2) F E) (D : F), b₂ 0 = 1 → σ (b₂ 1) = -b₂ 1 → b₂ 1 * b₂ 1 = algebraMap F E D → ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (Fv F v) D) = 1 → Valued.v (algebraMap F (Fv F v) 2) = 1 → (∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈ v.adicCompletionIntegers F) → (∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈ v.adicCompletionIntegers F) → ∀ e : Fv F v, e ^ 2 = algebraMap F (Fv F v) D → ¬ IsField (Fv F v ⊗[F] E) ∧ ∃ c : ℕ × ℕ → Fv F v ⊗[F] E, (∀ i, IsUnit (c i) ∧ c i ∈ intK b v) ∧ (∀ i, ∃ t : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ (c i) * c i ∧ ‖t‖ = ((qv v : ℝ) ^ (i.1 + i.2))⁻¹) ∧ (∀ x ∈ intK b v, IsUnit x → ∃ i, ∃ u ∈ intK b v, ∃ u' ∈ intK b v, u * u' = 1 ∧ x = c i * u) ∧ (∀ i j, ∀ u ∈ intK b v, ∀ u' ∈ intK b v, u * u' = 1 → c i = c j * u → i = j) := by
  first | exact @GlobalTheory.CompanionTheory.SW.SplitIdeals.split_content | exact GlobalTheory.CompanionTheory.SW.SplitIdeals.split_content | (intros; apply GlobalTheory.CompanionTheory.SW.SplitIdeals.split_content <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBasisIntegralUnramifiedStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_basis_integral_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (b₂ : Module.Basis (Fin 2) F E) (D : F), b₂ 0 = 1 → σ (b₂ 1) = -b₂ 1 → b₂ 1 * b₂ 1 = algebraMap F E D → ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (Fv F v) D) = 1 → Valued.v (algebraMap F (Fv F v) 2) = 1 → (∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈ v.adicCompletionIntegers F) → (∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈ v.adicCompletionIntegers F) → (¬ ∃ e : v.adicCompletionIntegers F, Valued.v ((e : Fv F v) ^ 2 - algebraMap F (Fv F v) D) < 1) → IsField (Fv F v ⊗[F] E) ∧ ∃ c : ℕ → Fv F v ⊗[F] E, (∀ i, IsUnit (c i) ∧ c i ∈ intK b v) ∧ (∀ i, ∃ t : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ (c i) * c i ∧ ‖t‖ = ((qv v : ℝ) ^ (2 * i))⁻¹) ∧ (∀ x ∈ intK b v, IsUnit x → ∃ i, ∃ u ∈ intK b v, ∃ u' ∈ intK b v, u * u' = 1 ∧ x = c i * u) ∧ (∀ i j, ∀ u ∈ intK b v, ∀ u' ∈ intK b v, u * u' = 1 → c i = c j * u → i = j) := by
  first | exact @GlobalTheory.CompanionTheory.SW.QuadField.inert_content | exact GlobalTheory.CompanionTheory.SW.QuadField.inert_content | (intros; apply GlobalTheory.CompanionTheory.SW.QuadField.inert_content <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetCapelliOperatorStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_det_capelli_operator : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (u : ℂ) (φ : π.V), (Formalism.REAL.qdet (EopV π τ) (u + ((a : ℂ) - 1) / 2) φ).1 = cap τ u φ.1 := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.qdet_EopV_val | exact GlobalTheory.CompanionTheory.Clozel.qdet_EopV_val | (intros; apply GlobalTheory.CompanionTheory.Clozel.qdet_EopV_val <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergArchimedeanFactorStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_archimedean_factor : Ad3.R.HalfPlaneAnalyticIdentities := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.x1a | exact GlobalTheory.CompanionTheory.RankinSelberg.x1a | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.x1a <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergEulerProductPartialStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_euler_product_partial : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.A10 → Ad3.R.M0 → Ad3.R.E4 → Ad3.R.E0 → Ad3.R.E1 → Ad3.R.E2 → Ad3.R.UnramifiedEulerProductIntegral := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergEulerProduct.e6a | exact GlobalTheory.CompanionTheory.RankinSelbergEulerProduct.e6a | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergEulerProduct.e6a <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergEulerProductStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_euler_product : Ad3.Loc2 → Ad3.R.B0 → Ad3.R.A10 → Ad3.R.E2 → Ad3.R.E3 → Ad3.R.E5 → Ad3.R.UnramifiedEulerProductIntegral → Ad3.R.F2 → Ad3.R.E6 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.Unfolded.e6 | exact GlobalTheory.CompanionTheory.RankinSelberg.Unfolded.e6 | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.Unfolded.e6 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergFunctionalEquationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_functional_equation : Ad3.R.A1 → Ad3.R.A6 → Ad3.R.A8 → Ad3.R.LocalGammaFunctionalEquation → Ad3.R.A9 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.a9_of_a0_a1_eigenbasis_a6 | exact GlobalTheory.CompanionTheory.RankinSelberg.a9_of_a0_a1_eigenbasis_a6 | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.a9_of_a0_a1_eigenbasis_a6 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGammaBoundStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_gamma_bound : Ad3.R.RealPlaceGammaFactors := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.RealGamma.main | exact GlobalTheory.CompanionTheory.RankinSelberg.RealGamma.main | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.RealGamma.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGammaFactorStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_gamma_factor : Ad3.R.LocalGammaFunctionalEquation := by
  first | exact @GlobalTheory.CompanionTheory.TateGamma.gam_strip | exact GlobalTheory.CompanionTheory.TateGamma.gam_strip | (intros; apply GlobalTheory.CompanionTheory.TateGamma.gam_strip <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergGlobalIdentityStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_global_identity : Ad3.R.B0 → Ad3.R.A1 → Ad3.R.G0 → Ad3.R.G2a → Ad3.R.G4 → Ad3.R.G5 → Ad3.R.GS → Ad3.R.FT → Ad3.R.F2 → Ad3.R.F5 → Ad3.R.F6 → Ad3.R.ConstantTermVanishingAlt → Ad3.R.E6 → Ad3.R.G6 → Ad3.R.X0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.globalIdentity | exact GlobalTheory.CompanionTheory.RankinSelberg.globalIdentity | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.globalIdentity <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalFirstStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_local_first : Ad3.R.A1 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergRotation.a1 | exact GlobalTheory.CompanionTheory.RankinSelbergRotation.a1 | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergRotation.a1 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergLocalFourthStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_local_fourth : Ad3.R.A4 := by
  first | exact @GlobalTheory.CompanionTheory.RankinKernel.kernel_integrable | exact GlobalTheory.CompanionTheory.RankinKernel.kernel_integrable | (intros; apply GlobalTheory.CompanionTheory.RankinKernel.kernel_integrable <;> assumption)
end

