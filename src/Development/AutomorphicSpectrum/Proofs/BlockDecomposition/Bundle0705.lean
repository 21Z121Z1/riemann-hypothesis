import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0692
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0675
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0061
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0691
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0693
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0680
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0688
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0595
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0651
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0694
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0452
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0617
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodIntegrandMajorantStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_integrand_majorant : ∀ (k : ℕ), 3 ≤ k → ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ N : ℕ, 8 ≤ N → ∃ C : ℝ, ∀ h : Ad3.LR.M22, (Matrix.of h).det ≠ 0 →
    ‖Ad3.LR.Wm k (Matrix.of h)⁻¹‖ * |(Matrix.of h).det| ^ (-(3 : ℝ) / 2) * ‖Ad3.LR.B.eta h‖ ^ (σ - 1) / (1 + ‖h‖) ^ N ≤
      C * (GlobalTheory.CompanionTheory.PerUInt.gk k σ ((Matrix.of h).det / (h 0 0 ^ 2 + h 1 0 ^ 2)) * (h 0 0 ^ 2 + h 1 0 ^ 2) ^ (-1 - σ / 2) *
        (GlobalTheory.CompanionTheory.PerUInt.phi (h 0 0) * GlobalTheory.CompanionTheory.PerUInt.phi (h 1 0) * (GlobalTheory.CompanionTheory.PerUInt.phi (h 0 1) * GlobalTheory.CompanionTheory.PerUInt.phi (h 1 1)))) := by
  first | exact @GlobalTheory.CompanionTheory.PerUInt.pointwise_gamma_bound | exact GlobalTheory.CompanionTheory.PerUInt.pointwise_gamma_bound | (intros; apply GlobalTheory.CompanionTheory.PerUInt.pointwise_gamma_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhaseCocycleBimultiplicativeStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phase_cocycle_bimultiplicative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (b : HermR (Af F) σ n)
    (X Y : Fin n → Fin M → Af F ⊗[F] E),
    phaseB σ J (psiFin F ψ) b (X + Y) =
      phaseB σ J (psiFin F ψ) b X * phaseB σ J (psiFin F ψ) b Y * pairB σ J (psiFin F ψ) b X Y := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd.phaseB_add | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd.phaseB_add | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd.phaseB_add <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhaseContinuousUnitaryStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phase_continuous_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (b : HermR (Af F) σ n),
    Continuous (phaseB σ J (psiFin F ψ) b) ∧ (∀ X, ‖phaseB σ J (psiFin F ψ) b X‖ = 1) ∧
    ∀ X, Continuous (pairB σ J (psiFin F ψ) b X) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.phaseB_pairB_props | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.phaseB_pairB_props | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.phaseB_pairB_props <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarizationCoordinateDerivativeBoundsStatement
section
open Ad3.LR Ad3.LR.DTr GlobalTheory.CompanionTheory.DInt2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_coordinate_derivative_bounds : ∀ (a b c d : Fin 2) (h : M22), 0 < (Matrix.of h).det → DifferentiableAt ℝ (rho c d) h ∧ DifferentiableAt ℝ tt h ∧ ‖fderiv ℝ (rho c d) h (rpol a b h)‖ ≤ 2 ∧ ‖fderiv ℝ tt h (rpol a b h)‖ ≤ 3 * uu h := by
  first | exact @GlobalTheory.CompanionTheory.DInt2.Drho.main | exact GlobalTheory.CompanionTheory.DInt2.Drho.main | (intros; apply GlobalTheory.CompanionTheory.DInt2.Drho.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackSchwartzLinearIndependentStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_schwartz_linear_independent : PositivityTheory.GramSchwartzFunctions.PullSchLI := by
  first | exact @GlobalTheory.CompanionTheory.PullSch.pullSchLI | exact GlobalTheory.CompanionTheory.PullSch.pullSchLI | (intros; apply GlobalTheory.CompanionTheory.PullSch.pullSchLI <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Purity
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.ClozelPurity

theorem purity : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, (∀ τ : E →+* ℂ, ∃ m, π.HasInfChar τ m) → (∀ τ, ∀ z ∈ (CG.mk π).infChar τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) → ∃ w₀ : ℤ, ∀ τ : E →+* ℂ, (CG.mk π).infChar ((starRingEnd ℂ).comp τ) = ((CG.mk π).infChar τ).map fun z => (w₀ : ℂ) - z := by
  intro hB E _ _ _ a ha π hinf hint
  obtain ⟨μ, h1, h2⟩ := GlobalTheory.T.exists_right_haar_measure E a
  haveI := h1
  haveI := h2
  obtain ⟨s, hs⟩ := GlobalTheory.T.aux_statement_20 E a ha π hinf
  obtain ⟨B, hH⟩ := GlobalTheory.T.exists_invariant_hermitian_form hB E a μ (π.twist (GlobalTheory.CuspRep.Model.absC E s)) hs
  have hm : ∀ τ, π.HasInfChar τ ((CG.mk π).infChar τ) := fun τ => by
    obtain ⟨m, h⟩ := hinf τ
    have e : (CG.mk π).infChar τ = m := CG.HasInfChar.infChar_eq (π := CG.mk π) h
    rw [e]
    exact h
  have hreal : ∀ τ, ∀ z ∈ (CG.mk π).infChar τ, (starRingEnd ℂ) z = z := fun τ z hz => by
    obtain ⟨n, rfl⟩ := hint τ z hz
    have c2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
    simp [c2]
  have key : ∀ τ : E →+* ℂ, (CG.mk π).infChar (NumberField.ComplexEmbedding.conjugate τ) =
      ((CG.mk π).infChar τ).map fun z => (-(starRingEnd ℂ) s - s) - z := fun τ => by
    have t1 := (hm τ).twist (GlobalTheory.CuspRep.Model.absC E s)
    have t2 := (hm (NumberField.ComplexEmbedding.conjugate τ)).twist (GlobalTheory.CuspRep.Model.absC E s)
    rw [GlobalTheory.CuspRep.Model.expo_absC] at t1 t2
    have e := GlobalTheory.T.infinitesimal_character_conjugate E a _ B hH τ _ _ t1 t2
    have e2 := congrArg (Multiset.map fun z => z - s) e
    simp only [Multiset.map_map, Function.comp_def, add_sub_cancel_right, Multiset.map_id'] at e2
    rw [e2]
    refine Multiset.map_congr rfl fun z hz => ?_
    rw [map_add, hreal τ z hz]
    ring
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨z, hz⟩ : ∃ z, z ∈ (CG.mk π).infChar τ₀ := by
    apply Multiset.card_pos_iff_exists_mem.1
    rw [CG.card_infChar]
    exact ha
  have hz' : (-(starRingEnd ℂ) s - s) - z ∈ (CG.mk π).infChar (NumberField.ComplexEmbedding.conjugate τ₀) := by
    rw [key]
    exact Multiset.mem_map_of_mem _ hz
  obtain ⟨n, hn⟩ := hint _ z hz
  obtain ⟨n', hn'⟩ := hint _ _ hz'
  refine ⟨n + n' + (a : ℤ) - 1, fun τ => ?_⟩
  have e : (-(starRingEnd ℂ) s - s) = (((n + n' + (a : ℤ) - 1 : ℤ)) : ℂ) := by
    push_cast
    linear_combination hn' + hn
  have e2 : (starRingEnd ℂ).comp τ = NumberField.ComplexEmbedding.conjugate τ := RingHom.ext fun _ => rfl
  rw [e2, key, e]

end GlobalTheory.CompanionTheory.ClozelPurity
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalCharacterKernelScalingStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_character_kernel_scaling : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ),
    IsCharAF F ψ → ∀ N : ℕ, 0 < N → ∀ D : ℕ, 0 < D → (∀ f : F,
      (∀ r : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F (f * (r : F)) = m) → ∃ o : 𝓞 F, (o : F) = (D : F) * f) →
    ∃ t : F, t ≠ 0 ∧ ∀ w : E, (∀ x : Af F ⊗[F] E, InNOh b N x →
        psiFin F ψ (Algebra.trace (Af F) (Af F ⊗[F] E) (sigR (Af F) σ x * inclR (Af F) w)) = 1) →
      ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = t • w := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest.rat_test | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest.rat_test | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest.rat_test <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalTupleInLatticeLevelStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_tuple_in_lattice_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n N : ℕ), 0 < N →
    ∃ s : ℕ, 0 < s ∧ ∀ ρ : Fin M → Fin n → 𝓞 E, ratTuple J s ρ ∈ latN b n M N := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem.ratTuple_mem_latN | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem.ratTuple_mem_latN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem.ratTuple_mem_latN <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealReadLevi
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2
open PositivityTheory.Rg.BcB.F.Tail
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.CompanionTheory.ReadLevel

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ g ∈ K, ρ g v = v :=
  ⟨fun h k hk => by simpa using h ⟨k, hk⟩, fun h k => by simpa using h k k.2⟩

theorem extTensor_twRep {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (χ : G →* ℂˣ) (ψ : H →* ℂˣ)
    (m : G × H) (x : V ⊗[ℂ] W) :
    GlobalTheory.SmGL.extTensor (twRep ρ χ) (twRep σ ψ) m x =
      ((χ m.1 * ψ m.2 : ℂˣ) : ℂ) • GlobalTheory.SmGL.extTensor ρ σ m x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v u =>
    rw [GlobalTheory.SmGL.extTensor_tmul, GlobalTheory.SmGL.extTensor_tmul, twRep_apply, twRep_apply,
      TensorProduct.smul_tmul_smul, Units.val_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

theorem isSpherical_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) {K : Subgroup G}
    (h : fixed σ K ≠ ⊥) : GlobalTheory.LGrp.IsSpherical ρ K := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine (Submodule.ne_bot_iff _).2 ⟨φ.toLinearEquiv.symm v, ?_, fun e => hv0 (by
    have h2 := congrArg φ.toLinearEquiv e
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h2)⟩
  refine mem_fixed_iff.2 fun g hg => φ.toLinearEquiv.injective ?_
  have h1 : φ.toLinearEquiv (ρ g (φ.toLinearEquiv.symm v)) = σ g (φ.toLinearEquiv (φ.toLinearEquiv.symm v)) :=
    LinearMap.congr_fun (φ.isIntertwining' g) _
  rw [h1, LinearEquiv.apply_symm_apply]
  exact mem_fixed_iff.1 hv g hg

theorem fixed_ind₂_ne_bot (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b n : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin a) k × GL (Fin b) k) W) (K : Subgroup (GL (Fin n) k))
    (hK : IsOpen (K : Set (GL (Fin n) k))) (x : W) (hx : x ≠ 0)
    (hfix : ∀ p : GlobalTheory.SmGL.parab k (GlobalTheory.SmGL.two e), (p : GL (Fin n) k) ∈ K →
      ((GlobalTheory.SmGL.deltaHalf k (GlobalTheory.SmGL.Two (Fin a) (Fin b)) (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p) : ℂˣ) : ℂ) •
        ρ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)) x = x) :
    fixed (GlobalTheory.SmGL.ind₂ e ρ) K ≠ ⊥ :=
  GlobalTheory.T.induced_fixed_nonzero _ _ _ _ K hK x hx hfix

theorem exists_fixed_of_sep {G V X : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G V} {S : Submodule ℂ V} {τ : Representation ℂ G X}
    (hs : Sep ρ S τ) {L : Subgroup G} (hL : IsOpen (L : Set G)) {v : V} (hv : v ∈ S) (hv0 : v ≠ 0)
    (hfix : v ∈ fixed ρ L) : ∃ x : X, x ≠ 0 ∧ ∀ m ∈ L, τ m x = x := by
  obtain ⟨-, J, Lj, hLj, hsep⟩ := hs
  have hsm : SmVec ρ v := ⟨L, hL, hfix⟩
  obtain ⟨j, hj⟩ : ∃ j, Lj j v ≠ 0 := by
    by_contra hc
    exact hv0 (hsep v hv hsm fun j => by_contra fun hj => hc ⟨j, hj⟩)
  refine ⟨Lj j v, hj, fun m hm => ?_⟩
  rw [← hLj j m v hv hsm, mem_fixed_iff.1 hfix m hm]

theorem fixed_ind₂_twist (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b n : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin a) k) V) (σ : Representation ℂ (GL (Fin b) k) W)
    (χ : GL (Fin a) k →* ℂˣ) (ψ : GL (Fin b) k →* ℂˣ)
    (K : Subgroup (GL (Fin n) k)) (hKo : IsOpen (K : Set (GL (Fin n) k))) (hKc : IsCompact (K : Set (GL (Fin n) k)))
    (x : V ⊗[ℂ] W) (hx : x ≠ 0)
    (hfix : ∀ p : GlobalTheory.SmGL.parab k (GlobalTheory.SmGL.two e), (p : GL (Fin n) k) ∈ K →
      GlobalTheory.SmGL.extTensor ρ σ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)) x = x ∧
      χ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)).1 *
        ψ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)).2 = 1) :
    fixed (GlobalTheory.SmGL.ind₂ e (GlobalTheory.SmGL.extTensor (twRep ρ χ) (twRep σ ψ))) K ≠ ⊥ := by
  refine fixed_ind₂_ne_bot k e _ K hKo x hx fun p hp => ?_
  obtain ⟨h1, h2⟩ := hfix p hp
  rw [GlobalTheory.T.modulus_trivial_on_compact_parabolic k a b n e K hKc p hp, Units.val_one, one_smul, extTensor_twRep, h1, h2, Units.val_one, one_smul]

theorem isSpherical_of_join (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b n : ℕ} (e : Fin a ⊕ Fin b ≃ Fin n) {U V W : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) k) U)
    (ρ : Representation ℂ (GL (Fin a) k) V) (σ : Representation ℂ (GL (Fin b) k) W)
    (χ : GL (Fin a) k →* ℂˣ) (ψ : GL (Fin b) k →* ℂˣ)
    (φ : π.Equiv (GlobalTheory.SmGL.ind₂ e (GlobalTheory.SmGL.extTensor (twRep ρ χ) (twRep σ ψ))))
    (K : Subgroup (GL (Fin n) k)) (hKo : IsOpen (K : Set (GL (Fin n) k))) (hKc : IsCompact (K : Set (GL (Fin n) k)))
    (x : V ⊗[ℂ] W) (hx : x ≠ 0)
    (hfix : ∀ p : GlobalTheory.SmGL.parab k (GlobalTheory.SmGL.two e), (p : GL (Fin n) k) ∈ K →
      GlobalTheory.SmGL.extTensor ρ σ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)) x = x ∧
      χ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)).1 *
        ψ ((GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm (GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.two e) p)).2 = 1) :
    GlobalTheory.LGrp.IsSpherical π K :=
  isSpherical_of_equiv φ (fixed_ind₂_twist k e ρ σ χ ψ K hKo hKc x hx hfix)

theorem loc_pow {E : Type} [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (w : Pl E) (k : ℕ)
    (x : (w.adicCompletion E)ˣ) : (μ ^ k).loc w x = μ.loc w (x ^ k) := by
  rw [map_pow]
  induction k with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ k ih => rw [pow_succ, pow_succ, ← ih]; rfl

theorem twist_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (μ : HChar E) (w : Pl E)
    (m : GLw a w × GLw b w)
    (h : μ.loc w (GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) = 1) :
    (((μ ^ b).loc w).comp GeneralLinearGroup.det) m.1 * (((μ ^ a).loc w).comp GeneralLinearGroup.det) m.2 = 1 := by
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, loc_pow, loc_pow, ← map_mul, h]

theorem levi_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)
    (K : Subgroup (GLw n w)) (Q : GLw a w × GLw b w → Prop) (hKQ : ∀ m X, blk h w m X ∈ K → Q m)
    (p : GlobalTheory.SmGL.parab (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))) (hp : (p : GLw n w) ∈ K) :
    Q ((GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm
      (GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) p)) := by
  obtain ⟨X, hX⟩ := GlobalTheory.T.parabolic_element_block_form E n a b h w p
  exact hKQ _ X (hX ▸ hp)

set_option maxHeartbeats 1000000 in
theorem rReadLev : RReadLev := by
  intro hR hJ E _ _ _ n a b h μ s₁ s₂ Pa Pb D c w K L G hKo hKc hLo hKL hG hG0 hGL
  obtain ⟨x, hx0, hx⟩ := exists_fixed_of_sep (hR E a b s₁ s₂ Pa Pb w c.g₁ c.g₂ c.u₁ c.u₂ c.t₁ c.t₂) hLo hG hG0 hGL
  obtain ⟨φ⟩ := hJ E n a b h (μ ^ b) (μ ^ a) Pa Pb D w c.join
  exact isSpherical_of_join (w.adicCompletion E) (GlobalTheory.SmGL.stdSum h) (lp D w) (lp Pa w) (lp Pb w)
    (((μ ^ b).loc w).comp GeneralLinearGroup.det) (((μ ^ a).loc w).comp GeneralLinearGroup.det)
    φ K hKo hKc x hx0 fun p hp =>
      have hq := levi_of_mem h w K _ hKL p hp
      ⟨hx _ hq.1, twist_eq_one μ w _ hq.2⟩

end GlobalTheory.CompanionTheory.ReadLevel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueRingStructureStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_ring_structure : PositivityTheory.SiegelWeilFormula.Gunr.RvRing := by
  first | exact @GlobalTheory.CompanionTheory.RvRingPf.rvRing | exact GlobalTheory.CompanionTheory.RvRingPf.rvRing | (intros; apply GlobalTheory.CompanionTheory.RvRingPf.rvRing <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReversedProductSameSubquotientsStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reversed_product_same_subquotients : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x (Fin.rev a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Fin.rev a)) hd') := by
  first | exact @GlobalTheory.CompanionTheory.GenRev.isSubquotient_prodIrr_rev | exact GlobalTheory.CompanionTheory.GenRev.isSubquotient_prodIrr_rev | (intros; apply GlobalTheory.CompanionTheory.GenRev.isSubquotient_prodIrr_rev <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakeEigenvaluePairDecomposition
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS.SatConv

theorem esymm_cons_succ' (a : ℂ) (s : Multiset ℂ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

theorem coeff_prod_one_add (s : Multiset ℂ) (n : ℕ) :
    ((s.map fun a => (1 + Polynomial.C a * Polynomial.X : Polynomial ℂ)).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, Polynomial.coeff_add,
      Polynomial.coeff_C_mul]
    cases n with
    | zero => simp [ih, Multiset.esymm]
    | succ n => rw [Polynomial.coeff_X_mul, ih, ih, esymm_cons_succ']

theorem esymm_add_antidiagonal (s t : Multiset ℂ) (k : ℕ) :
    (s + t).esymm k = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, s.esymm p.1 * t.esymm p.2 := by
  rw [← coeff_prod_one_add, Multiset.map_add, Multiset.prod_add, Polynomial.coeff_mul]
  simp only [coeff_prod_one_add]

theorem esymm_map_mul_unit (B : Multiset ℂˣ) (z : ℂˣ) (j : ℕ) :
    ((B.map (· * z)).map fun b : ℂˣ => (b : ℂ)).esymm j =
      (z : ℂ) ^ j * (B.map fun b : ℂˣ => (b : ℂ)).esymm j := by
  have h := Multiset.pow_smul_esymm (z : ℂ) j (B.map fun b : ℂˣ => (b : ℂ))
  simp only [smul_eq_mul, Multiset.map_map, Function.comp_def] at h
  simp only [Multiset.map_map, Function.comp_def, Units.val_mul, mul_comm _ (z : ℂ)]
  exact h.symm

theorem esymm_eq_zero_of_card_lt (s : Multiset ℂ) {k : ℕ} (h : s.card < k) : s.esymm k = 0 := by
  simp [Multiset.esymm, Multiset.powersetCard_eq_empty k h]

theorem satEig_join : ∀ (q n a b : ℕ) (c : ℂˣ) (Ba Bb : Multiset ℂˣ), q ≠ 0 → a + b = n → Ba.card = a → Bb.card = b → ∀ k ≤ n, satEig q n (Ba.map (· * c ^ b) + Bb.map (· * c ^ a)) k = ∑ p ∈ pairs a b k, coef q c a b p.1 p.2 * (satEig q a Ba p.1 * satEig q b Bb p.2) := by
  intro q n a b c Ba Bb hq hab hBa hBb k _
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  subst hab
  rw [pairs, Finset.sum_filter]
  simp only [satEig]
  rw [Multiset.map_add, esymm_add_antidiagonal, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, j⟩ hp
  have hk : i + j = k := by simpa using hp
  subst hk
  simp only [esymm_map_mul_unit]
  split_ifs with h
  · have hpow : (q : ℂ) ^ ((((i + j : ℕ) : ℂ) * (((a + b : ℕ) : ℂ) - ((i + j : ℕ) : ℂ))) / 2) =
        (q : ℂ) ^ (((i : ℂ) * b + (j : ℂ) * a) / 2 - (i : ℂ) * j) *
          ((q : ℂ) ^ (((i : ℂ) * ((a : ℂ) - i)) / 2) * (q : ℂ) ^ (((j : ℂ) * ((b : ℂ) - j)) / 2)) := by
      rw [← Complex.cpow_add _ _ hq', ← Complex.cpow_add _ _ hq']
      congr 1
      push_cast
      ring
    rw [hpow, coef]
    simp only [Units.val_pow_eq_pow_val]
    rw [pow_add, pow_mul, pow_mul, pow_right_comm (c : ℂ) i b, pow_right_comm (c : ℂ) j a]
    ring
  · have hz : (Ba.map fun x : ℂˣ => (x : ℂ)).esymm i = 0 ∨ (Bb.map fun x : ℂˣ => (x : ℂ)).esymm j = 0 := by
      by_cases hi : i ≤ a
      · right
        refine esymm_eq_zero_of_card_lt _ ?_
        rw [Multiset.card_map, hBb]
        by_contra hj
        exact h ⟨hi, by omega⟩
      · left
        refine esymm_eq_zero_of_card_lt _ ?_
        rw [Multiset.card_map, hBa]
        omega
    rcases hz with hz | hz <;> simp [hz]

end GlobalTheory.CompanionTheory.CtS.SatConv
end
end

