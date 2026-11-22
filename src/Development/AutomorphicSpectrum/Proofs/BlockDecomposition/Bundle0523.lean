import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0509
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0149
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0167
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0486
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0148
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0154
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0176
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0140
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFiltrationViaTruncation
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0510
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianScalarSequenceTendsZero
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path

variable {F : Type} [Field F] [NumberField F]

def invInf (F : Type) [Field F] [NumberField F] (n : ℕ) : Ainf F :=
  fun w => ((n : w.Completion) + 1)⁻¹

omit [NumberField F] in
theorem norm_natCast_add_one (w : NumberField.InfinitePlace F) (n : ℕ) :
    ‖((n : w.Completion) + 1)‖ = (n : ℝ) + 1 := by
  have h := (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
    (map_zero _) ((n : w.Completion) + 1)
  rw [← h, map_add, map_natCast, map_one]
  have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_natCast]
  push_cast; ring

theorem natCast_add_one_ne_zero (w : NumberField.InfinitePlace F) (n : ℕ) :
    ((n : w.Completion) + 1) ≠ 0 := by
  intro h
  have := norm_natCast_add_one w n
  rw [h, norm_zero] at this
  have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem mul_invInf (n : ℕ) : ((n : Ainf F) + 1) * invInf F n = 1 := by
  have key : ((n : ∀ w : NumberField.InfinitePlace F, w.Completion) + 1) *
      (fun w : NumberField.InfinitePlace F => ((n : w.Completion) + 1)⁻¹) = 1 := by
    funext w
    simp only [Pi.mul_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
    exact mul_inv_cancel₀ (natCast_add_one_ne_zero w n)
  exact key

theorem tendsto_invInf : Filter.Tendsto (invInf F) Filter.atTop (nhds 0) := by
  refine tendsto_pi_nhds.2 fun w => ?_
  have key : Filter.Tendsto (fun n : ℕ => ((n : w.Completion) + 1)⁻¹) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : ∀ n : ℕ, ‖((n : w.Completion) + 1)⁻¹‖ = 1 / ((n : ℝ) + 1) := fun n => by
      rw [norm_inv, norm_natCast_add_one, one_div]
    simp only [e]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  exact key

def seqA (F : Type) [Field F] [NumberField F] (n : ℕ) : AF F := pairA F (invInf F n) 0

theorem tendsto_seqA : Filter.Tendsto (seqA F) Filter.atTop (nhds 0) := by
  have : Filter.Tendsto (fun n => (invInf F n, (0 : Af F))) Filter.atTop (nhds ((0 : Ainf F), (0 : Af F))) :=
    tendsto_invInf.prodMk_nhds tendsto_const_nhds
  exact this

def seqE (D : D7) (r n : ℕ) : Mx D r r :=
  Matrix.diagonal fun _ => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)

theorem seqE_mem (D : D7) (r n : ℕ) : seqE D r n ∈ hermA D r := by
  show GlobalTheory.MixModel.adj (seqE D r n) = seqE D r n
  ext i j
  by_cases h : i = j
  · subst h
    simp [GlobalTheory.MixModel.adj, seqE, sigR]
  · simp [GlobalTheory.MixModel.adj, seqE, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

theorem tendsto_seqE (D : D7) (r : ℕ) : Filter.Tendsto (seqE D r) Filter.atTop (nhds 0) := by
  have hc : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  have h1 : Filter.Tendsto (fun n => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) Filter.atTop (nhds (0 : AE D)) := by
    have h2 : Filter.Tendsto (fun n => seqA D.host.F n • (1 : AE D)) Filter.atTop (nhds ((0 : AF D.host.F) • (1 : AE D))) :=
      tendsto_seqA.smul_const _
    rw [zero_smul] at h2
    refine h2.congr fun n => ?_
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  show Filter.Tendsto (fun n => seqE D r n i j) Filter.atTop (nhds (0 : AE D))
  by_cases h : i = j
  · subst h
    refine h1.congr fun n => ?_
    exact (Matrix.diagonal_apply_eq (fun _ => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) i).symm
  · refine (tendsto_const_nhds (x := (0 : AE D))).congr fun n => ?_
    exact (Matrix.diagonal_apply_ne (fun _ => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) h).symm

theorem theta_seqE (D : D7) (θ : InfFam D) (ρ : D.what₂.Tau) (n : ℕ) :
    θ ρ (infPart D (seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E))) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) := by
  have e1 : infPart D (seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) = invInf D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [e1]
  have e2 : (((n : Ainf D.host.F) + 1) ⊗ₜ[D.host.F] (1 : D.host.E)) * (invInf D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_invInf, mul_one]; rfl
  have e3 : (((n : Ainf D.host.F) + 1) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((n : Ainf D.host.F ⊗[D.host.F] D.host.E) + 1) := by
    rw [TensorProduct.add_tmul, ← Algebra.TensorProduct.one_def]
    congr 1
  have e4 := congrArg (θ ρ) e2
  rw [e3, map_mul, map_add, map_natCast, map_one] at e4
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp
  linear_combination e4

theorem exists_herm_seq : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ r : ℕ, ∃ e : ℕ → Mx D r r, (∀ n, e n ∈ hermA D r) ∧ Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∀ (n : ℕ) (ρ : D.what₂.Tau), compAt θ ρ (e n) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
  intro D θ _ r
  refine ⟨seqE D r, seqE_mem D r, tendsto_seqE D r, fun n ρ => ?_⟩
  ext i j
  by_cases h : i = j
  · subst h
    simp only [compAt, seqE, Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq]
    rw [theta_seqE]; simp
  · simp [compAt, seqE, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFiltrationVanishesAboveDimensionStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_filtration_vanishes_above_dimension : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → KH.KIso → KH.GrAff → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsProper q] (d : ℕ)
    [SmoothOfRelativeDimension d q] (j : ℕ), ∀ x ∈ FilR q j (d + 1), x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FilTop.fil_top_vanish | exact GlobalTheory.CompanionTheory.FilTop.fil_top_vanish | (intros; apply GlobalTheory.CompanionTheory.FilTop.fil_top_vanish <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFiltrationViaTruncationStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_filtration_via_truncation : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → KH.GrAff → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (s : ℕ)
    (hs : ∀ α, U.d α < s) (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (j : ℕ), Function.Bijective (resK q (KS q s 𝒱) j) ∧
      ∀ r ≤ s, ∀ x : HdR q j, x ∈ FilR q j r ↔ quoK q (KS q s 𝒱) r j x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.KIso.k_iso | exact GlobalTheory.CompanionTheory.KIso.k_iso | (intros; apply GlobalTheory.CompanionTheory.KIso.k_iso <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteEmbeddingMemStandardOpenSubgroup
section
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem infiniteEmbedding_mem_standardOpenSubgroup {F : Type*} [Field F] [NumberField F]
    (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    infiniteEmbedding w a ∈ standardOpenSubgroup F := by
  refine (mem_standardOpenSubgroup F).2 fun v ↦ ?_
  have h1 : ((infiniteEmbedding w a : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    rw [coe_infiniteEmbedding]
    rfl
  have h2 : (((infiniteEmbedding w a)⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    rw [← map_inv, coe_infiniteEmbedding]
    rfl
  rw [h1, h2]
  exact ⟨one_mem _, one_mem _⟩

theorem infiniteParams_eq_zero {F : Type*} [Field F] [NumberField F] (χ : HeckeCharacter F)
    (hχ : standardOpenSubgroup F ≤ χ.toIdele.ker) (w : InfinitePlace F) :
    χ.infiniteParams w = (0, 0) := by
  refine (χ.infiniteParams_unique w (p := (0, 0)) (fun _ ↦ ⟨le_rfl, by norm_num⟩) fun a ↦ ?_).symm
  have h : χ.toIdele (infiniteEmbedding w a) = 1 :=
    hχ (infiniteEmbedding_mem_standardOpenSubgroup w a)
  simp [HeckeCharacter.infiniteComponent_apply, h]

theorem gammaFactor_eq_of_unramified : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (χ : HeckeCharacter F), standardOpenSubgroup F ≤ χ.toIdele.ker →
    ∀ s : ℂ, χ.gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F := by
  intro F _ _ _ χ hχ s
  have hw : ∀ w : InfinitePlace F, χ.infiniteGamma w s = Complex.Gammaℝ s := fun w ↦ by
    have hr : w.IsReal := IsTotallyReal.isReal w
    have hp := infiniteParams_eq_zero χ hχ w
    simp [HeckeCharacter.infiniteGamma, hr, HeckeCharacter.infiniteTau,
      HeckeCharacter.infiniteWeight, hp]
  have hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    have h3 := IsTotallyReal.nrComplexPlaces_eq_zero F
    omega
  rw [HeckeCharacter.gammaFactor, Finset.prod_congr rfl fun w _ ↦ hw w, Finset.prod_const,
    Finset.card_univ, hcard]

end GlobalTheory.CompanionTheory.PartialZeta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableDescendOfCover
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

namespace GlobalTheory.CompanionTheory.AutCover

open scoped Pointwise

theorem integrable_descend_of_cover : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (S : Set (GA D V)),
    MeasurableSet S → (∀ g, ∃ γ ∈ GQ V, ∃ s ∈ S, g = γ * s) → ∀ φ : GA D V → ℂ, GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ →
      Measurable φ → IntegrableOn φ S μ → Integrable (descend (GQ V) φ) (autMeasure V μ) := by
  intro D V μ _ S hS hcov φ hinv hφ hint
  have hmeas : AEStronglyMeasurable (descend (GQ V) φ) (autMeasure V μ) :=
    (GlobalTheory.AutomorphicL2Unitary.aestronglyMeasurable_quotMeasure_iff_lift).2 (by
      rw [hinv.lift_descend]
      exact hφ.aestronglyMeasurable)
  refine ⟨hmeas, ?_⟩
  have hfin : ∫⁻ g in S, ‖φ g‖ₑ ∂μ < ⊤ := hint.2
  have hmf : AEMeasurable (S.indicator fun g => ‖φ g‖ₑ) μ := (hφ.enorm.indicator hS).aemeasurable
  have key := GlobalTheory.AutomorphicL2Unitary.lintegral_eq_lintegral_tsum (Γ := GQ V) (μ := μ) hmf
  rw [lintegral_indicator hS] at key
  show ∫⁻ q, ‖descend (GQ V) φ q‖ₑ ∂(autMeasure V μ) < ⊤
  refine lt_of_le_of_lt ?_ hfin
  rw [key]
  apply lintegral_mono
  intro q
  obtain ⟨γ, hγ, s, hs, hq⟩ := hcov q.out
  have e : (((⟨γ, hγ⟩ : GQ V)⁻¹ : GQ V) : GA D V) * q.out = s := by
    show γ⁻¹ * q.out = s
    rw [hq, inv_mul_cancel_left]
  have hmem : (((⟨γ, hγ⟩ : GQ V)⁻¹ : GQ V) : GA D V) * q.out ∈ S := by
    rw [e]
    exact hs
  have h1 : S.indicator (fun g => ‖φ g‖ₑ) ((((⟨γ, hγ⟩ : GQ V)⁻¹ : GQ V) : GA D V) * q.out) = ‖φ q.out‖ₑ := by
    rw [Set.indicator_of_mem hmem, hinv _ (((⟨γ, hγ⟩ : GQ V)⁻¹ : GQ V)).2]
  show ‖φ q.out‖ₑ ≤ _
  rw [← h1]
  exact ENNReal.le_tsum (f := fun γ : GQ V => S.indicator (fun g => ‖φ g‖ₑ) ((γ : GA D V) * q.out)) _

end GlobalTheory.CompanionTheory.AutCover
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOperatorRepOpRcuspZero
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspRank

theorem isCompactOperator_repOp_Rcusp_zero (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (μ : Measure (GA E 0)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E 0 → ℂ) :
    IsCompactOperator (repOp (Rcusp μ) μ f) := by
  have := SpecModel.finiteDimensional_zero μ
  have : FiniteDimensional ℂ (L2cusp μ) := inferInstance
  have : ProperSpace (L2cusp μ) := FiniteDimensional.proper ℂ _
  exact isCompactOperator_of_locallyCompactSpace_rng _

end GlobalTheory.CompanionTheory.CuspRank
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIsoFrameFirstCols
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.CompanionTheory.RegInt

variable {D : D7} {V : HSp D} {r : ℕ}

def firstCols (X : Matrix (Fin V.rank) (Fin r) D.host.E) (j : Fin r) :
    Matrix (Fin V.rank) (Fin (j.val + 1)) D.host.E := X.submatrix id (Fin.castLE j.2)

def root (t : Fin r → ℝ) (j : Fin r) : ℝ := if h : j.val + 1 < r then t j / t ⟨j.val + 1, h⟩ else t j

theorem isIsoFrame_firstCols {X Y : Matrix (Fin V.rank) (Fin r) D.host.E}
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r) : IsIsoFrame V (firstCols X j) := by
  refine ⟨Nat.succ_pos _, ?_, ?_⟩
  · have h1 : LinearIndependent D.host.E (fun i : Fin r => fun a : Fin V.rank => X a i) := by
      refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
      have h3 : ∀ a, ∑ l, g l * X a l = 0 := fun a => by
        have := congrFun hg a
        simpa [Finset.sum_apply, mul_comm] using this
      have h4 : (fun l => (D.sp.cm.sig : D.host.E →+* D.host.E) (g l)) ᵥ*
          Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X = 0 := by
        funext a
        have := congrArg (D.sp.cm.sig : D.host.E →+* D.host.E) (h3 a)
        simp only [map_sum, map_mul, map_zero] at this
        simpa [Matrix.vecMul, dotProduct, Formalism.UG.cT] using this
      have h5 := congrArg (fun v => v ᵥ* (V.gram * Y)) h4
      simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul, ← Matrix.mul_assoc, hW.xy, Matrix.vecMul_one] at h5
      have h6 := congrFun h5 i
      simpa using h6
    have h2 : (firstCols X j).transpose = (fun i : Fin r => fun a : Fin V.rank => X a i) ∘ Fin.castLE j.2 := by
      funext i a; rfl
    change LinearIndependent D.host.E (firstCols X j).transpose
    rw [h2]
    exact h1.comp _ (Fin.castLE_injective _)
  · have h := hW.xx
    refine Matrix.ext fun a b => ?_
    have := congrFun (congrFun h (Fin.castLE j.2 a)) (Fin.castLE j.2 b)
    simpa [Matrix.mul_apply, Formalism.UG.cT, firstCols] using this

end GlobalTheory.CompanionTheory.RegInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.CompanionTheory.MPDict

open GlobalTheory.ArithmeticHeightTower ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

abbrev Bk (n : Fin (m + 1) → ℕ) : Fin (m + 1) → Type := fun c => Fin (n c + 1)

abbrev σ₀ : ℤ →+* ℂ := Int.castRingHom ℂ

abbrev prB (n : Fin (m + 1) → ℕ) (k : Fin (m + 1)) : MP ℤ m n ⟶ PSpace ℤ (n k) := pr ℤ m n k

abbrev blockChart (n : Fin (m + 1) → ℕ) (k : Fin (m + 1)) (i : Bk n k) : (MP ℤ m n).Opens :=
  prB n k ⁻¹ᵁ chart ℤ (n k) i

def mchart (c : ∀ k, Bk n k) : (MP ℤ m n).Opens :=
  ⟨⋂ k, (blockChart n k (c k) : Set (MP ℤ m n)),
    isOpen_iInter_of_finite fun k => (blockChart n k (c k)).isOpen⟩

theorem mchart_le (c : ∀ k, Bk n k) (k : Fin (m + 1)) : mchart c ≤ blockChart n k (c k) :=
  fun _ hx => Set.mem_iInter.1 hx k

def blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) : Γ(MP ℤ m n, W)ˣ :=
  res h (pullU (prB n k) _ (ratioUnit _ i j inf_le_left inf_le_right))

def ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : Bk n k :=
  (exists_mem_chart ℤ (n k) (prB n k x)).choose

theorem mem_ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : x ∈ blockChart n k (ptChart x k) :=
  (exists_mem_chart ℤ (n k) (prB n k x)).choose_spec

def ptCoord (x : MP ℤ m n) (p : Σ k, Bk n k) : (MP ℤ m n).residueField x :=
  ((MP ℤ m n).evaluation (blockChart n p.1 (ptChart x p.1)) x (mem_ptChart x p.1)).hom
    (pullRatio (prB n p.1) _ (ptChart x p.1) le_rfl p.2)

def ptIdeal (x : MP ℤ m n) : Ideal (Geo.MRing (Bk n)) := Geo.mCoordIdeal (ptCoord x)

def IsUnder (y : CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ) : Prop :=
  ∀ (k : Fin (m + 1)) (i : Bk n k), (y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) ↔ z ⟨k, i⟩ ≠ 0) ∧
    ∀ j : Bk n k, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) →
      CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y = z ⟨k, j⟩ / z ⟨k, i⟩

def IsHermRep (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)) : Prop :=
  ∃ u : ∀ (i : M.B.ι) (c : ∀ k, Bk n k), Γ(MP ℤ m n, M.B.U i ⊓ mchart c)ˣ,
    (∀ i j c,
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U j ⊓ mchart c) (u j c) =
        res (inf_le_left : M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U i ⊓ M.B.U j) (M.B.g i j) *
          res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            M.B.U i ⊓ M.B.U j ⊓ mchart c ≤ M.B.U i ⊓ mchart c) (u i c)) ∧
    (∀ i c c',
      res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ mchart c) (u i c) =
        res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ M.B.U i ⊓ mchart c') (u i c') *
        ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
          ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
            M.B.U i ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ A.a k) ∧
    ∀ (i : M.B.ι) (c : ∀ k, Bk n k) (y : CxPts (mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ), IsUnder y z →
      y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) →
      A.h z = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) *
        ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) y‖ *
          Real.exp ((M.φ σ₀).φ i y / 2)

abbrev consN (n' : ℕ) (n : Fin (m + 1) → ℕ) : Fin (m + 2) → ℕ := Fin.cons n' n

def sv (n' : ℕ) (n : Fin (m + 1) → ℕ) : (Σ k, Bk n k) → Σ k', Bk (consN n' n) k' :=
  fun p => ⟨p.1.succ, p.2⟩

theorem isBlockMap_sv (n' : ℕ) (n : Fin (m + 1) → ℕ) :
    IsBlockMap (ι := Bk n) (ι' := Bk (consN n' n)) Fin.succ (sv n' n) := by
  refine ⟨Fin.succ_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', j⟩ h
    have hk : k.succ = k'.succ := congrArg Sigma.fst h
    obtain rfl : k = k' := Fin.succ_injective _ hk
    have h' : (⟨k.succ, i⟩ : Σ k', Bk (consN n' n) k') = ⟨k.succ, j⟩ := h
    have hij : i = j := sigma_mk_injective (β := Bk (consN n' n)) (i := k.succ) h'
    rw [hij]
  · rintro ⟨k', j⟩ ⟨k, rfl⟩
    exact ⟨⟨k, j⟩, rfl⟩

def pullLine (n' : ℕ) (A : Geo.HermLine (Bk n)) : Geo.HermLine (Bk (consN n' n)) where
  a := pullDeg Fin.succ A.a
  h z := A.h fun p => z (sv n' n p)
  pos z hz := A.pos _ fun k => hz k.succ
  smul c z hc := by
    have e := A.smul (fun k => c k.succ) (fun p => z (sv n' n p)) fun k => hc k.succ
    refine e.trans ?_
    have h0 : pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) A.a 0 = 0 := by
      unfold pullDeg
      rw [Function.extend_apply']
      · rfl
      · rintro ⟨k, hk⟩
        exact Fin.succ_ne_zero k hk
    have hs (k : Fin (m + 1)) : pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) A.a k.succ = A.a k :=
      (Fin.succ_injective _).extend_apply _ _ _
    rw [Fin.prod_univ_succ (fun k' => ‖c k'‖ ^ pullDeg Fin.succ A.a k'), h0, zpow_zero, one_mul]
    simp only [hs]

theorem isPullHerm_pullLine (n' : ℕ) (A : Geo.HermLine (Bk n)) :
    IsPullHerm Fin.succ (sv n' n) A (pullLine n' A) :=
  ⟨rfl, fun _ => rfl⟩

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetHeckeCompatHoldsStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_hecke_compat_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C2 k := by
  first | exact @GlobalTheory.CompanionTheory.Lbc.jacquet_hecke_operator_compat | exact GlobalTheory.CompanionTheory.Lbc.jacquet_hecke_operator_compat | (intros; apply GlobalTheory.CompanionTheory.Lbc.jacquet_hecke_operator_compat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionHeckeHoldsStatement
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_projection_hecke_holds : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A2 G := by
  first | exact @GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines | exact GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines | (intros; apply GlobalTheory.CompanionTheory.Cass.jacquet_projection_hecke_intertwines <;> assumption)
end

