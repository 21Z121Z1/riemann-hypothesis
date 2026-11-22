import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0431
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0430
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0417
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0116
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0053
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0428
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0432
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0433
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0015
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0343
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0096
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0090
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0077
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0073
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0425
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0081

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitVectorOrthogonalInstanceRankThreeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_vector_orthogonal_instance_rank_three : ∀ (I : AutInst) (P Q : ℕ), HasSig I P Q → 3 ≤ I.n → ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) → ∃ (I' : AutInst) (e : I'.E ≃+* I.E) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf ∧ HasSig I' (if s then P - 1 else P) (if s then Q else Q - 1) := by
  first | exact @GlobalTheory.PerpInst.exists_isPerpInst | exact GlobalTheory.PerpInst.exists_isPerpInst | (intros; apply GlobalTheory.PerpInst.exists_isPerpInst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamiliesHaveLargeGapOfNumericalHypothesesStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.families_have_largeGap_of_numericalHypotheses : (∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r), Num k r lam u b bv ga h q0 → IsFam lam q0 R → IsFamG lam q0 R) ∧ ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg ↔ SetupG lam u b bv ga h q0 z π μW μN μG νq R lb dg := by
  first | exact @GlobalTheory.GapSetup.families_gap | exact GlobalTheory.GapSetup.families_gap | (intros; apply GlobalTheory.GapSetup.families_gap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeRatioEqHarishChandraRatioLargeGapStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_ratio_eq_harishChandra_ratio_largeGap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (W : LocW D.R.k D.R.rS) (l l' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A A' : LocS W) (h : ℝ), GoodS D l A → GoodS D l' A' → GapAtLeast (epsSH D.R) l h → GapAtLeast (epsSH D.R) l' h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → A'.deg / A.deg = Formalism.QuantumDeterminants.fdegHC l' / Formalism.QuantumDeterminants.fdegHC l := by
  first | exact @GlobalTheory.GapDegreeRatio.deg_ratio | exact GlobalTheory.GapDegreeRatio.deg_ratio | (intros; apply GlobalTheory.GapDegreeRatio.deg_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameGramMulEqConjTransposeMulFrameMatricesStatement
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameGram_mul_eq_conjTranspose_mul_frameMatrices : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (g γ h : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (C B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), GlobalTheory.LoopAct.IsMatOn (uMat (g⁻¹ v)) (Formalism.L2.SG.RealObj.frm X u 1 v) C → GlobalTheory.LoopAct.IsMatOn (uMat (h v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) B → Formalism.L2.SG.RealObj.ZX X u u' 1 (g * γ * h) v = Cᴴ * Formalism.L2.SG.RealObj.ZX X u u' 1 γ v * B := by
  first | exact @GlobalTheory.ZxMul.zx_mul | exact GlobalTheory.ZxMul.zx_mul | (intros; apply GlobalTheory.ZxMul.zx_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMatrixMemUnipotentStabilizerFrameGramStatement
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrix_mem_unipotentStabilizer_frameGram : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ y : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), y ∈ Formalism.L2.SG.RealObj.StInf X u u' γ → IsUpUni M → GlobalTheory.LoopAct.IsMatOn (uMat ((γ⁻¹ * y * γ) v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) M → IsUnit (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v).det → M ∈ GlobalTheory.LoopV.stabU (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v) := by
  first | exact @GlobalTheory.FrameStab.frameMat_mem_stabU | exact GlobalTheory.FrameStab.frameMat_mem_stabU | (intros; apply GlobalTheory.FrameStab.frameMat_mem_stabU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapNearPlaceParameterHalfNoncompactGapStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gap_near_placeParameter_half_noncompactGap : ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → m₀ ≤ D.R.m → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r → GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2) := by
  first | exact @GlobalTheory.GapNear.gap_near | exact GlobalTheory.GapNear.gap_near | (intros; apply GlobalTheory.GapNear.gap_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianVolumeDependsOnlyOnFieldSignatureStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_volume_depends_only_on_field_signature : VolumeInvariant := by
  first | exact @GlobalTheory.VolInvariant.volumeInvariant | exact GlobalTheory.VolInvariant.volumeInvariant | (intros; apply GlobalTheory.VolInvariant.volumeInvariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableCellOrbitalIntegralRankOneKFiniteStatement
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_cellOrbitalIntegral_rankOne_kFinite : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.κN ≠ ⊤ → CellData L μG γ μR νR ν → (∀ᵐ p ∂ν, Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧ Matrix.of p.2.2 ∈ Nset k r) ∧ ∀ b : ℝ, 0 ≤ b → b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 → Integrable (pairMaj γ b) ν → ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' → ∀ (ξ : L.Wp) (ξ' : L.Wq), Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
  first | exact @GlobalTheory.CellOrbIntG.orbInt_integrable | exact GlobalTheory.CellOrbIntG.orbInt_integrable | (intros; apply GlobalTheory.CellOrbIntG.orbInt_integrable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentEqLatticeUnipotentCoordsStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotent_eq_latticeUnipotent_coords : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), (∀ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, (GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) → ∃ s ∈ NOinf X u, ∀ w, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w)) ∧ (∀ s ∈ NOinf X u, ∃ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, (GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) ∧ ∀ w, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w)) := by
  first | exact @GlobalTheory.CovDomGrp.nO_eq_nLam_coords | exact GlobalTheory.CovDomGrp.nO_eq_nLam_coords | (intros; apply GlobalTheory.CovDomGrp.nO_eq_nLam_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFiniteCoefAndTorusTranslateIsBesselCoefLargeGapStatement
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFiniteCoef_and_torusTranslate_isBesselCoef_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → ∀ f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp), Formalism.MainNotions.S.IsKFinCoefH L.σ f → (∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' f s) ∧ ∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s := by
  first | exact @GlobalTheory.AmpTKGap.isCoef_kfin_and_torus_translate | exact GlobalTheory.AmpTKGap.isCoef_kfin_and_torus_translate | (intros; apply GlobalTheory.AmpTKGap.isCoef_kfin_and_torus_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralAmplitudeNormSqBigCellGapStatement
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_amplitudeNormSq_bigCell_gap : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ (k r : ℕ) (L : LocBessel k r) (μG : Measure (Mt k r)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 2 ≤ k → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsSection k r L.z L.z' μsec → ∃ c : ℝ, 0 < c ∧ ∀ (R : Rep k r) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (w : R.H), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') q * hsNormSq (amp R l l' w μG (bigCell k r q.1 (μsec q.2)))) = ENNReal.ofReal (c / PI.BesselPeriodGGP.fdegH μG R.σ w ^ 3) := by
  first | exact @GlobalTheory.AmpNormGap.lintegral_hsNormSq_amp_gap | exact GlobalTheory.AmpNormGap.lintegral_hsNormSq_amp_gap | (intros; apply GlobalTheory.AmpNormGap.lintegral_hsNormSq_amp_gap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusCyclicDiscriminantSplitPrime
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.CyclicDisc

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem nondeg_of_pd (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · by_contra hne
    have := hp τ x hne
    rw [hx x] at this
    simp at this
  · by_contra hne
    have := hp τ x hne
    rw [hx x] at this
    simp at this

omit [IsScalarTower (𝓞 K) K V] in
theorem pd_of_ortho (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K) (I : Submodule (𝓞 K) V) (n : ℕ)
    (hI : IsOrthoLattice h I n) : PD h := by
  obtain ⟨e, -, hsp, -, he⟩ := hI
  intro τ x hx
  have hx' : x ∈ Submodule.span K (Set.range e) := by rw [hsp]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx'
  have hc : ∃ i, c i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hx (by simp [hn])
  have e1 : h (∑ i, c i • e i) (∑ i, c i • e i) = ∑ i, star (c i) * c i := by
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, he,
      smul_eq_mul, RingHom.id_apply, starRingEnd_apply]
    simp [mul_comm]
  rw [e1, map_sum, Complex.re_sum]
  have e2 : ∀ i, (τ (star (c i) * c i)).re = Complex.normSq (τ (c i)) := fun i => by
    rw [map_mul, hK.2.1, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  simp only [e2]
  obtain ⟨i, hi⟩ := hc
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 ((map_ne_zero τ).2 hi)⟩

omit [NumberField K] in
theorem star_mem_range (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := by
  have : IsIntegral ℤ (starRingEnd K (algebraMap (𝓞 K) K r)) :=
    map_isIntegral_int _ (RingOfIntegers.isIntegral_coe r)
  exact ⟨⟨_, this⟩, rfl⟩

def Over (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (L M : Submodule (𝓞 K) V) : Prop :=
  Submodule.IsLattice K M ∧ IsUnimodular h M ∧ L ≤ M ∧
    Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓))

omit [NumberField K] in
theorem over_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (g : isom h) (L M : Submodule (𝓞 K) V)
    (H : Over h 𝔓 L M) : Over h 𝔓 (g • L) (g • M) := by
  obtain ⟨h1, h2, h3, ⟨e⟩⟩ := H
  have A := final_isomAct (𝓞 K) K V h g.1 g.2 M
  refine ⟨A.2.2.2.2.2 h1, A.2.2.2.1.2 h2, Submodule.map_mono h3, ⟨?_⟩⟩
  let g' : V ≃ₗ[𝓞 K] V := (g : V ≃ₗ[K] V).restrictScalars (𝓞 K)
  let f : M ≃ₗ[𝓞 K] ↥(g • M) := g'.submoduleMap M
  refine (Submodule.Quotient.equiv _ _ f ?_).symm.trans e
  ext ⟨x, hx⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y.1, hy, congrArg Subtype.val hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨⟨y, h3 hy⟩, hy, Subtype.ext hxy⟩

omit [NumberField K] in
theorem over_smul_iff (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (g : isom h) (L M : Submodule (𝓞 K) V) :
    Over h 𝔓 (g • L) (g • M) ↔ Over h 𝔓 L M :=
  ⟨fun H => by simpa using over_smul h 𝔓 g⁻¹ _ _ H, over_smul h 𝔓 g L M⟩

noncomputable def up (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Submodule (𝓞 K) V := sSup {M | Over h 𝔓 L M}

omit [NumberField K] in
theorem up_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (g : isom h) (L : Submodule (𝓞 K) V) :
    up h 𝔓 (g • L) = g • up h 𝔓 L := by
  have key : ∀ (g : isom h) (L : Submodule (𝓞 K) V), g • up h 𝔓 L ≤ up h 𝔓 (g • L) := by
    intro g L
    change Submodule.map _ _ ≤ _
    rw [Submodule.map_le_iff_le_comap]
    refine sSup_le fun M hM => ?_
    rw [← Submodule.map_le_iff_le_comap]
    exact le_sSup (over_smul h 𝔓 g L M hM)
  refine le_antisymm ?_ (key g L)
  have h1 := key g⁻¹ (g • L)
  rw [inv_smul_smul] at h1
  have h2 : g • g⁻¹ • up h 𝔓 (g • L) ≤ g • up h 𝔓 L := Submodule.map_mono h1
  rwa [smul_inv_smul] at h2

omit [NumberField K] in
theorem up_eq (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (L M : Submodule (𝓞 K) V)
    (hu : ∃! M, Over h 𝔓 L M) (hM : Over h 𝔓 L M) : up h 𝔓 L = M := by
  have : {M | Over h 𝔓 L M} = {M} := by
    ext N
    exact ⟨fun hN => hu.unique hN hM, fun hN => by rw [Set.mem_singleton_iff.1 hN]; exact hM⟩
  rw [up, this, sSup_singleton]

end

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → 1 ≤ Module.finrank K V → ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K), h'.IsSymm → ∀ I : Submodule (𝓞 K) V', IsOrthoLattice h' I (Module.finrank K V) → ∀ T : ℕ, T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → mass h L = mass h' I * (((T : ℝ) ^ Module.finrank K V - 1) / ((T : ℝ) - 1)) ^ fDeg K := by
  intro hMM K V _ _ _ _ _ _ _ _ h hK hs hp hn V' _ _ _ _ _ h' hs' I hI T hT hsp L hL hLq
  have hnd := nondeg_of_pd h hp
  have hp' := pd_of_ortho hK h' I _ hI
  have hnd' := nondeg_of_pd h' hp'
  obtain ⟨⟨s, hcard, hsP, hcop, hprod⟩, hgen⟩ := GlobalTheory.T.cyclicDiscriminant_lattices_form_one_genus K V h hK hs hnd T hT hsp
  have hT0 : (T : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hT.ne_zero
  have hP0 : (∏ P ∈ s, P) ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at hprod
    exact hT0 hprod
  obtain ⟨o1, o2⟩ := GlobalTheory.T.exists_unimodular_overlattice_cyclic_split_discriminant K V h hK hs hnd _ hP0 hcop
  rw [hprod] at o1 o2
  have hex : ∀ N ∈ genus h L, ∃! M, Over h (∏ P ∈ s, P) N M := fun N hN =>
    o1 N ((hgen L N hL hLq).1 hN).1 ((hgen L N hL hLq).1 hN).2
  obtain ⟨M0, hM0, -⟩ := o1 L hL hLq
  obtain ⟨-, m2, -⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V h hK hs hnd
  obtain ⟨-, m2', m3'⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V' h' hK hs' hnd'
  obtain ⟨c, hc⟩ := hMM K hK _ hn
  obtain ⟨iL, iU, iR⟩ := m3' I _ hI
  have e0 : mass h M0 = mass h' I := by
    rw [hc V h hs hp rfl M0 (m2 M0 hM0.1 hM0.2.1).1, (m2 M0 hM0.1 hM0.2.1).2.2,
      hc V' h' hs' hp' iR I (m2' I iL iU).1, (m2' I iL iU).2.2]
  obtain ⟨b1, b2, b3, b4, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp L hL.1
  obtain ⟨a1, a2, a3, -, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M0 hM0.1
  have hmaps : Set.MapsTo (up h (∏ P ∈ s, P)) (genus h L) (genus h M0) := by
    intro N hN
    obtain ⟨M, hM, -⟩ := hex N hN
    rw [up_eq h _ N M (hex N hN) hM]
    exact (GlobalTheory.T.mem_genus_iff_maximalIntegralHermitianLattice K V h hK hs hp M0 M (m2 M0 hM0.1 hM0.2.1).1).2 (m2 M hM.1 hM.2.1).1
  have hfib := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ (genus h L) (genus h M0) (up h (∏ P ∈ s, P))
    (up_smul h _) b3 a3 hmaps (fun y hy => b4 y hy.1)
  set B : ℕ := (∑ i ∈ Finset.range (Module.finrank K V), T ^ i) ^ s.card with hB
  have hconst : ∀ M ∈ genus h M0,
      ((((genus h L) ∩ (up h (∏ P ∈ s, P)) ⁻¹' {M}).encard : ℕ∞) : ℝ≥0∞) = (B : ℝ≥0∞) := by
    intro M hM
    have hU : IsUnimodular h M :=
      (((final_genusBasic (𝓞 K) K V h hs star_mem_range).2.2 M0 M hM0.1.fg hM.1.fg hM.2).1).1 hM0.2.1
    have hset : (genus h L) ∩ (up h (∏ P ∈ s, P)) ⁻¹' {M} = {N : Submodule (𝓞 K) V | N ≤ M ∧
        Nonempty ((↥M ⧸ N.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ P ∈ s, P))} := by
      ext N
      constructor
      · rintro ⟨hN, hNM⟩
        obtain ⟨M1, hM1, -⟩ := hex N hN
        have : M1 = M := (up_eq h _ N M1 (hex N hN) hM1).symm.trans hNM
        subst this
        exact hM1.2.2
      · rintro ⟨h1, h2⟩
        have hN : N ∈ genus h L := (hgen L N hL hLq).2 (o2 M N hM.1 hU h1 h2)
        exact ⟨hN, up_eq h _ N M (hex N hN) ⟨hM.1, hU, h1, h2⟩⟩
    rw [hset, GlobalTheory.T.card_sublattices_quotient_prod_degree_one_primes K V M hM.1 T s hT hsP]
    exact ENat.toENNReal_coe _
  obtain ⟨p1, p2, -⟩ := GlobalTheory.T.orbitWeightedStabilizerSum_mono_subadditive (isom h) (Submodule (𝓞 K) V)
  have hsum : orbMass (isom h) (genus h L) = (B : ℝ≥0∞) * orbMass (isom h) (genus h M0) := by
    rw [hfib, ← p2]
    exact le_antisymm (p1 _ _ _ _ subset_rfl fun x hx => (hconst x hx).le)
      (p1 _ _ _ _ subset_rfl fun x hx => (hconst x hx).ge)
  rw [← b1, ← a1, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_eq_ofReal_iff b2.le (by positivity)] at hsum
  have hT1 : (T : ℝ) ≠ 1 := by exact_mod_cast hT.one_lt.ne'
  rw [hsum, e0, hB, hcard, mul_comm, ← geom_sum_eq hT1]
  push_cast
  rfl

end GlobalTheory.Mass.CyclicDisc
end

