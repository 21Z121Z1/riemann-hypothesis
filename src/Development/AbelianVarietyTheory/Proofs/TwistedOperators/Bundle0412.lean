import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVanishesSingleCoefficientOfKernelKills
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0401
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0403

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledVacuumLatticeStabilizerBlocksKeepLatticeStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuumLatticeStabilizer_blocks_keep_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F), ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₁₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₁₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₂₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₂₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₁₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₁₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₂₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₂₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) := by
  first | exact @GlobalTheory.DblVac.KD_blocks_keep | exact GlobalTheory.DblVac.KD_blocks_keep | (intros; apply GlobalTheory.DblVac.KD_blocks_keep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualIrreducibleCoefficientSpaceRealPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_irreducible_coefficientSpace_realPlaces : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is → ∀ N : Submodule ℂ (Module.Dual ℂ c.W), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ f ∈ N, (c.ρ (atTau θ V τ g)⁻¹).dualMap f ∈ N) → N = ⊥ ∨ N = ⊤ := by
  first | exact @GlobalTheory.DualIrr.dual_irr | exact GlobalTheory.DualIrr.dual_irr | (intros; apply GlobalTheory.DualIrr.dual_irr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainFiniteDimensionalAndPeterssonProduStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaChain_finiteDimensional_and_peterssonProducts : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D ∧ MetEx D := by
  first | exact @GlobalTheory.EvenMetric.finDim_and_metEx | exact GlobalTheory.EvenMetric.finDim_and_metEx | (intros; apply GlobalTheory.EvenMetric.finDim_and_metEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainLValuesNeZeroAndParamsInjectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaChain_LValues_ne_zero_and_params_injective : ∀ D : D7, ChainL D ∧ ∀ (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E)), chainPar c B k w = chainPar c B' k w → B w = B' w := by
  first | exact @GlobalTheory.EvenOnto.chainL_and_inj | exact GlobalTheory.EvenOnto.chainL_and_inj | (intros; apply GlobalTheory.EvenOnto.chainL_and_inj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainStageLevelMeasurePeterssonCoefficiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaChainStage_levelMeasure_peterssonCoefficient : ∀ D : D7, ForStage D fun c _ s => (MeasurableSet (intOff c s) ∧ MeasurableSet s.big ∧ s.big ⊆ intOff c s ∧ ∃ mR : Measure (GinfC s.V), mR.IsHaarMeasure ∧ ∀ (f : GinfC s.V → ℂ) (F : GA D s.V → ℂ), Integrable f mR → (∀ (b : GinfC s.V), ∀ κ ∈ s.J, F ((b : GA D s.V) * κ) = f b) → IntegrableOn F s.big s.ν ∧ ∫ g in s.big, F g ∂s.ν = ∫ b, f b ∂mR) ∧ ∀ ipD ip, IsMet c s ipD ip → ∀ (u : s.CC c) (v : s.M.Vec) (b : GinfC s.V), ∀ κ ∈ s.J, s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = ip u u * ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  first | exact @GlobalTheory.EvenOnto.MeasPet.meas_petco | exact GlobalTheory.EvenOnto.MeasPet.meas_petco | (intros; apply GlobalTheory.EvenOnto.MeasPet.meas_petco <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainStepFockVectorsSphericalLatticeVacStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaChainStep_fockVectors_spherical_latticeVacua : ∀ D : D7, ForStep D fun c _ s s' p => ∀ φ, IsThetaFunO c.ψ s.V s'.V (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) ∧ ∀ v ∉ c.S, GlobalTheory.FinZeta.VacFin c.ψ s.V s'.V v (p.pt φ) := by
  first | exact @GlobalTheory.EvenOnto.fock_sph_vac | exact GlobalTheory.EvenOnto.fock_sph_vac | (intros; apply GlobalTheory.EvenOnto.fock_sph_vac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStabStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicUnitary_prod_localPoints_mul_latticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'), G.IsGood B →
    ∀ h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h - 1) = 0) →
    ∀ T₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∃ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F))
      (l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J),
    T₀ ⊆ S ∧ (∀ x ∈ l, x.1 ∈ S ∧ x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F x.1)) ∧
    h = (l.map Prod.snd).prod * k ∧
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) ∧
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) := by
  first | exact @GlobalTheory.FinDecomp.exists_prod_local_mul_latStab | exact GlobalTheory.FinDecomp.exists_prod_local_mul_latStab | (intros; apply GlobalTheory.FinDecomp.exists_prod_local_mul_latStab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleLiftSplitPlaceConjugatePairStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_lift_splitPlaceConjugatePair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F), (∀ i j, σ (W.J j i) = -W.J i j) →
  ∀ (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z, π₁ (cA σ z) = π₂ z) → (∀ z, π₂ (cA σ z) = π₁ z) → (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) → (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F),
  S.map (fun x => (x : Fv F v)) = (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) →
  ∀ X₁ X₂ : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), X₁ᵀ * S + S * X₂ = 0 →
  ∃ Y : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Y ∧
    Y.map π₁ = (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) * X₁.map (fun x => (x : Fv F v)) * ((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) ∧
    Y.map π₂ = (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) * X₂.map (fun x => (x : Fv F v)) * ((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) ∧
    Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 := by
  first | exact @GlobalTheory.AdmLift.exists_admissible_lift | exact GlobalTheory.AdmLift.exists_admissible_lift | (intros; apply GlobalTheory.AdmLift.exists_admissible_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairing
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical TensorProduct

namespace GlobalTheory.WrongSignPair

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_tmul {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (e : E) :
    piInf τ (a ⊗ₜ[F] e) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 e := rfl

private theorem star_extensionEmbedding_eq (h : IsCMExt F E σ) {w : InfinitePlace F} (x : w.Completion) :
    star (InfinitePlace.Completion.extensionEmbedding w x) = InfinitePlace.Completion.extensionEmbedding w x := by
  have h' := h
  obtain ⟨hF, -⟩ := h'
  have hw : w.IsReal := hF.isReal w
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
  exact Complex.conj_ofReal _

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  have hconj := h
  obtain ⟨-, -, -, hconj⟩ := hconj
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have hz : cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [cA]
    rw [hz, piInf_tmul, piInf_tmul, star_mul', star_extensionEmbedding_eq h, hconj]
  | add x y hx hy => simp only [map_add, hx, hy, star_add]

private theorem trace_pi_real_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) :
    Algebra.trace ℝ (ι → ℝ) f = ∑ i, f i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun ℝ ι), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  simp

theorem trace_evI [IsTotallyReal F] (a : AF F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) =
      ∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (a.1 w)).re := by
  have hreal : ∀ v : InfinitePlace F, v.IsReal := IsTotallyReal.isReal
  haveI : IsEmpty {v : InfinitePlace F // v.IsComplex} :=
    ⟨fun v => (InfinitePlace.not_isReal_iff_isComplex.2 v.2) (hreal v.1)⟩
  rw [Algebra.trace_prod_apply]
  have h2 : (evI F a).2 = 0 := Subsingleton.elim _ _
  rw [h2, map_zero, add_zero, trace_pi_real_eq_sum]
  rw [← Fintype.sum_equiv (Equiv.subtypeUnivEquiv hreal) (fun v => (evI F a).1 v)
    (fun w => (InfinitePlace.Completion.extensionEmbedding w (a.1 w)).re) (fun v => ?_)]
  simp only [evI, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  show _ = (InfinitePlace.Completion.extensionEmbedding v.1 (a.1 v.1)).re
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply v.2, Complex.ofReal_re]

theorem trace_evI_trace (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : AE F E) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (Algebra.trace (AF F) (AE F E) z)) =
      ∑ w : InfinitePlace F, 2 * (piInf (τ w) z).re := by
  have hF : IsTotallyReal F := by
    have h' := h
    obtain ⟨hF, -⟩ := h'
    exact hF
  rw [trace_evI]
  refine Finset.sum_congr rfl fun w _ => ?_
  set t := Algebra.trace (AF F) (AE F E) z with ht
  have key : piInf (τ w) (algebraMap (AF F) (AE F E) t) = piInf (τ w) z + star (piInf (τ w) z) := by
    rw [ht, ← GlobalTheory.GaussMean.OneVec.add_sigR (AF F) h z, map_add, ← piInf_cA h]
    congr 2
  have hal : piInf (τ w) (algebraMap (AF F) (AE F E) t) =
      InfinitePlace.Completion.extensionEmbedding w (t.1 w) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, piInf_tmul, map_one,
      mul_one]
  rw [hal] at key
  rw [key, Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

private theorem piInf_inclR_twisted_operators {w : InfinitePlace F} (τ : EmbOver E w) (e : E) :
    piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  have h1 : inclR (F := F) (AF F) e = (1 : AF F) ⊗ₜ[F] e := rfl
  have h2 : (1 : AF F).1 w = 1 := rfl
  rw [h1, piInf_tmul, h2, map_one, one_mul]

theorem piInf_hTens (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {n d : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) (u u' : Matrix (Fin n) (Fin d) (AE F E)) :
    piInf τ (GlobalTheory.WeilM.hTens (cA σ) (incM F J) (incM F K) u u') =
      ∑ i, ∑ j, ∑ k, ∑ l, u.map (piInf τ) i j * J.map τ.1 i k * K.map τ.1 j l * star (u'.map (piInf τ) k l) := by
  simp only [GlobalTheory.WeilM.hTens, incM, Matrix.map_apply, map_sum, map_mul, piInf_cA h, piInf_inclR_twisted_operators]

theorem sum_rank_one {n d : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (x x' : Fin n → ℂ)
    (y y' : Fin d → ℂ) :
    ∑ i, ∑ j, ∑ k, ∑ l, vecMulVec x y i j * G i k * H j l * star (((-Complex.I) • vecMulVec x' y') k l) =
      (x ⬝ᵥ G *ᵥ star x') * (y ⬝ᵥ (Complex.I • H) *ᵥ star y') := by
  have hI : star (-Complex.I) = Complex.I := by
    rw [star_neg]
    exact (congrArg Neg.neg Complex.conj_I).trans (neg_neg _)
  simp only [dotProduct, mulVec, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul, star_mul', hI,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem star_dotProduct_mulVec_star_comm {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : ∀ i j, star (G j i) = G i j)
    (u v : Fin n → ℂ) : star (u ⬝ᵥ G *ᵥ star v) = v ⬝ᵥ G *ᵥ star u := by
  simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
  first
  | (rw [Finset.sum_comm]
     refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
     rw [hG]; ring)
  | (refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
     rw [hG]; ring)

private theorem dotProduct_mulVec_star_invariant {n : ℕ} {G θ : Matrix (Fin n) (Fin n) ℂ} (hθ : θᵀ * G * θ.map star = G)
    (u v : Fin n → ℂ) : (θ *ᵥ u) ⬝ᵥ G *ᵥ star (θ *ᵥ v) = u ⬝ᵥ G *ᵥ star v := by
  have hs : star (θ *ᵥ v) = θ.map star *ᵥ star v := by
    ext i
    simp [mulVec, dotProduct, star_sum, star_mul']
  rw [hs, ← Matrix.vecMul_transpose θ u, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [hθ]

theorem majorant_im {n : ℕ} {G θ : Matrix (Fin n) (Fin n) ℂ} (hG : ∀ i j, star (G j i) = G i j) (h : IsCartan G θ)
    (x : Fin n → ℂ) : ((θ *ᵥ x) ⬝ᵥ G *ᵥ star x).im = 0 := by
  obtain ⟨h1, h2, -⟩ := h
  have e1 : (θ *ᵥ x) ⬝ᵥ G *ᵥ star x = x ⬝ᵥ G *ᵥ star (θ *ᵥ x) := by
    conv_lhs => rw [← dotProduct_mulVec_star_invariant h2 (θ *ᵥ x) x, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [← star_dotProduct_mulVec_star_comm hG (θ *ᵥ x) x] at e1
  exact Complex.conj_eq_iff_im.mp e1.symm

private theorem mul_vecMulVec_mul_transpose' {n d : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin d) (Fin d) ℂ)
    (x : Fin n → ℂ) (y : Fin d → ℂ) : A * vecMulVec x y * Cᵀ = vecMulVec (A *ᵥ x) (C *ᵥ y) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  first
  | (rw [Finset.sum_comm]
     exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)
  | exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private theorem re_pos_im_zero_of_isCartan {n : ℕ} {G θ : Matrix (Fin n) (Fin n) ℂ} (hG : ∀ i j, star (G j i) = G i j)
    (h : IsCartan G θ) {x : Fin n → ℂ} (hx : x ≠ 0) :
    0 < (x ⬝ᵥ G *ᵥ star (θ *ᵥ x)).re ∧ (x ⬝ᵥ G *ᵥ star (θ *ᵥ x)).im = 0 := by
  have hi := majorant_im hG h x
  have hp := h.2.2 x hx
  rw [← star_dotProduct_mulVec_star_comm hG (θ *ᵥ x) x, Complex.star_def, Complex.conj_re, Complex.conj_im, hi, neg_zero]
  exact ⟨hp, rfl⟩

theorem exists_neg_pair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → 0 < n → 0 < d →
    ∀ (ε' : InfinitePlace F → ℤˣ) (w : InfinitePlace F), ε' w = -1 →
    ∃ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u ∧ At (evI F) u' ∧
      (∀ w', u'.map (piInf (B.emb w')) =
        (((ε' w' : ℤ) : ℂ) * Complex.I) • (X.θ w' * u.map (piInf (B.emb w')) * (W.θ w')ᵀ)) ∧
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (GlobalTheory.WeilM.symp (cA σ) (-1) (incM F X.J) (incM F W.J) u u')) < 0 := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW hn hd ε' w hw
  have h : IsCMExt F E σ := hB.cm
  have hconj : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x) := by
    have h' := h
    obtain ⟨-, -, -, hconj⟩ := h'
    exact hconj
  have lift : ∀ c : InfinitePlace F → Matrix (Fin n) (Fin d) ℂ, ∃ z : Matrix (Fin n) (Fin d) (AE F E),
      At (evI F) z ∧ ∀ w', z.map (piInf (B.emb w')) = c w' := by
    intro c
    have hz := fun i j => GlobalTheory.ThK.exists_at_evI_piInf_eq F E σ h B.emb (fun w' => c w' i j)
    choose z hz1 hz2 using hz
    refine ⟨z, ?_, ?_⟩
    · intro a ha
      ext i j
      exact hz1 i j a ha
    · intro w'
      ext i j
      exact hz2 i j w'
  let x : Fin n → ℂ := Pi.single ⟨0, hn⟩ 1
  let y : Fin d → ℂ := Pi.single ⟨0, hd⟩ 1
  have hx : x ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hn⟩
    simp [x] at this
  have hy : y ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hd⟩
    simp [y] at this
  obtain ⟨u, hu1, hu2⟩ := lift (fun w' => if w' = w then vecMulVec x y else 0)
  obtain ⟨u', hu'1, hu'2⟩ := lift (fun w' => (((ε' w' : ℤ) : ℂ) * Complex.I) •
    (X.θ w' * (if w' = w then vecMulVec x y else 0) * (W.θ w')ᵀ))
  have hu : ∀ w', u.map (piInf (B.emb w')) = if w' = w then vecMulVec x y else 0 := fun w' => hu2 w'
  have hu' : ∀ w', u'.map (piInf (B.emb w')) = (((ε' w' : ℤ) : ℂ) * Complex.I) •
      (X.θ w' * (if w' = w then vecMulVec x y else 0) * (W.θ w')ᵀ) := fun w' => hu'2 w'
  refine ⟨u, u', hu1, hu'1, fun w' => by rw [hu' w', hu w'], ?_⟩
  have hJ : ∀ i j, star ((X.J.map (B.emb w).1) j i) = (X.J.map (B.emb w).1) i j := by
    intro i j
    simp only [Matrix.map_apply]
    rw [← hconj, hX.herm]
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have hK : ∀ i j, star ((Complex.I • W.J.map (B.emb w).1) j i) = (Complex.I • W.J.map (B.emb w).1) i j := by
    intro i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [star_mul', hI, ← hconj, hW.skew, map_neg]
    ring
  obtain ⟨hPr, hPi⟩ := re_pos_im_zero_of_isCartan hJ (hX.cartan w) hx
  obtain ⟨hQr, hQi⟩ := re_pos_im_zero_of_isCartan hK (hW.cartan w) hy
  have hs : (((ε' w : ℤ) : ℂ) * Complex.I) = -Complex.I := by
    rw [hw]
    simp
  have hmain : piInf (B.emb w) (GlobalTheory.WeilM.hTens (cA σ) (incM F X.J) (incM F W.J) u u') =
      (x ⬝ᵥ (X.J.map (B.emb w).1) *ᵥ star (X.θ w *ᵥ x)) *
        (y ⬝ᵥ (Complex.I • W.J.map (B.emb w).1) *ᵥ star (W.θ w *ᵥ y)) := by
    rw [piInf_hTens h, hu w, hu' w, if_pos rfl, hs, mul_vecMulVec_mul_transpose', sum_rank_one]
  have hzero : ∀ w', w' ≠ w → piInf (B.emb w') (GlobalTheory.WeilM.hTens (cA σ) (incM F X.J) (incM F W.J) u u') = 0 := by
    intro w' hne
    rw [piInf_hTens h, hu w', if_neg hne]
    simp
  simp only [GlobalTheory.WeilM.symp]
  rw [trace_evI_trace h B.emb, Finset.sum_eq_single w]
  · rw [map_mul, map_neg, map_one, neg_one_mul, hmain, Complex.neg_re, Complex.mul_re, hPi, zero_mul, sub_zero]
    nlinarith [mul_pos hPr hQr]
  · intro w' _ hne
    rw [map_mul, hzero w' hne, mul_zero, Complex.zero_re, mul_zero]
  · intro hw'
    exact absurd (Finset.mem_univ w) hw'

end GlobalTheory.WrongSignPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRepIntertwinerImageRowsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuousRep_intertwinerImage_rows : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → ∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ := by
  first | exact @GlobalTheory.ConjRowRepR.exists_contRep_rows | exact GlobalTheory.ConjRowRepR.exists_contRep_rows | (intros; apply GlobalTheory.ConjRowRepR.exists_contRep_rows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLeviStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_piExteriorTensor_blockLevi : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (τ : GlobalTheory.SmGL.IrrRep (GlobalTheory.SmGL.Levi k c)), ∃ s : ∀ j, GlobalTheory.SmGL.IrrRep (GL (c j) k), Nonempty (τ.ρ.Equiv (GlobalTheory.SmGL.piTensor fun j => (s j).ρ)) := by
  first | exact @GlobalTheory.LeviFactor.exists_equiv_piTensor_levi | exact GlobalTheory.LeviFactor.exists_equiv_piTensor_levi | (intros; apply GlobalTheory.LeviFactor.exists_equiv_piTensor_levi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLeftInverseLiftingSplitPlaceInversesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_leftInverse_lifting_splitPlaceInverses : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl F) (π₁ π₂ : AE F E →+* Fv F v), (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) → (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ K : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) (K - 1) →
  ∀ N₁ N₂ : Matrix (Fin d) (Fin d) (Fv F v), N₁ * K.map π₁ = 1 → N₂ * K.map π₂ = 1 →
  ∃ M : Matrix (Fin d) (Fin d) (AE F E), M * K = 1 ∧ M.map π₁ = N₁ ∧ M.map π₂ = N₂ := by
  first | exact @GlobalTheory.MatrixLeftInverseLift.matrix_left_inverse_lift | exact GlobalTheory.MatrixLeftInverseLift.matrix_left_inverse_lift | (intros; apply GlobalTheory.MatrixLeftInverseLift.matrix_left_inverse_lift <;> assumption)
end

