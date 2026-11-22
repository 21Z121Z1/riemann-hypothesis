import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0285
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0294
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0283
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0284
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0309
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0275
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0330
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0352
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertPrimeOrderParitySignRadicalIntegralForm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointLocalHeightEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfied
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem inp_all : ∀ D, Inp D := fun D =>
  { g1 := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
    perm := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).2
    uni := GlobalTheory.T.intertwinerUnitary_all D
    mu := GlobalTheory.T.admissible_characters_exist D
    curve := GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D
    gal := GlobalTheory.T.thetaTranslate_galoisRationality_cmPoints D
    galEx := GlobalTheory.T.galois_data_exists D
    t0Ex := GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates D
    use1 := GlobalTheory.T.forall_use1 D
    alg := GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication D
    conj := GlobalTheory.T.thetaVacua_conjugates_cmPoints D
    nrm := GlobalTheory.T.vacuumNorm_conj_cmPoints_all_embeddings D
    bar := GlobalTheory.T.cmTheta_complexConjugation_compatible D
    odd3 := GlobalTheory.T.weilRepresentation_vacuum_sign_inert_places D
    odd4 := GlobalTheory.T.oddness_condition_holds D
    rep := GlobalTheory.T.exists_unitaryClass_rep_trivial_at_cm D
    model := GlobalTheory.T.datum_curve_integral_unitDisc_model D
    transl := GlobalTheory.T.cm_theta_torsion_translate_integral_series D
    two := GlobalTheory.T.cm_theta_functions_over_two_unit_and_integral D
    jets := GlobalTheory.T.cm_normalized_theta_jets_integral D
    split := GlobalTheory.T.cm_theta_values_vanish_at_odd_split_prime D
    eqv := GlobalTheory.OddRank.exact_equivariance D }

end GlobalTheory.NormSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateLatticeMeansPosLogAreaThetaBoundedStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_lattice_means_posLog_area_theta_bounded : ∃ C : ℝ, 0 < C ∧ ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ L : ℝ, 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → wpF (lamOf D cc δ) t0 ∈ M → ∀ t : (M →ₐ[ℚ] ℂ) → ℂ, (∀ ρ, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) (t ρ)) → (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹) / (Module.finrank ℚ M : ℝ) ≤ C * L ∧ (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ)))) / (Module.finrank ℚ M : ℝ) ≤ C * L := by
  first | exact @GlobalTheory.ArchFree.means.means_le | exact GlobalTheory.ArchFree.means.means_le | (intros; apply GlobalTheory.ArchFree.means.means_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointLocalHeightEqOneStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_localHeight_eq_one : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → ∀ v : ℂ, InRationalLattice g.abelian₂ v → v ∉ g.abelian₂ → ‖GlobalTheory.ThetaTransl.cval g v‖ ^ 2 * max 1 ‖xAt g v‖ = 1 := by
  first | exact @GlobalTheory.TorsionHeight.height_one | exact GlobalTheory.TorsionHeight.height_one | (intros; apply GlobalTheory.TorsionHeight.height_one <;> assumption)
end

