import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.RemovableLogGrowthSingularityStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_sum_tensor_product : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', boxFun φ₁ φ₂ ∈ schA F (κ ⊕ κ') ∧ thetaSum F (boxFun φ₁ φ₂) = thetaSum F φ₁ * thetaSum F φ₂ := by
  first | exact @GlobalTheory.CompanionTheory.ThetaBox.theta_box | exact GlobalTheory.CompanionTheory.ThetaBox.theta_box | (intros; apply GlobalTheory.CompanionTheory.ThetaBox.theta_box <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaHeisenbergTranslatesSeparateStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_units_haar_character_one : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (a : Fˣ), distribHaarChar (AdeleRing (𝓞 F) F) (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.AdeleModule.distribHaarChar_principal | exact GlobalTheory.CompanionTheory.AdeleModule.distribHaarChar_principal | (intros; apply GlobalTheory.CompanionTheory.AdeleModule.distribHaarChar_principal <;> assumption)
end

