import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0465
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0076
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0253
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0267
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0111
import Formalism.UnipotentAdelicQuotients.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
import Formalism.PeriodIntegrals.Bundle0022
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsGenericTermIffNoLocalDefectBaseFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0466
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0027
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0406
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0404
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0386
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0020
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0064
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EquivPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0275
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0078
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0299
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0292

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOnePairsNonGenericRowBoundOfRemainingPremiStatement
section
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.corankOnePairsNonGenericRowBound_of_remaining_premises : StepChoiceConstantsC → StepPinExists → Formalism.L2.SG.NGVanish.FormNGC → StepThmBPinnedP → Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric → Formalism.L2.SG.FamDefs.WeightsNG → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric → Formalism.L2.SG.FamDefs.ExistNG → RowNGP := by
  first | exact @GlobalTheory.rowNGP_of_leaves | exact GlobalTheory.rowNGP_of_leaves | (intros; apply GlobalTheory.rowNGP_of_leaves <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientSmoothDecayCapelliEigen
section
open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory

theorem eigDec_of_isKFinCoefT_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (f : B.Mat k r → (Wq →L[ℂ] Wp)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f) → EigDec f (aOf r h - 1) mu := by
  intro hH k r ε mu h R Wp Wq _ _ _ _ _ _ f hDS hgap hok hf
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  have hsm : PI.KFinSmooth := hH.1.1.2.2.1
  have hDG : R.IsDG ε mu := ⟨hDS.1, hDS.2, h, hgap, hok⟩
  obtain ⟨s, hs⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hsm k r ε mu R Wp Wq (fun _ => 0) (fun _ => 0) hDS).1 f hf
  obtain ⟨h1, h2⟩ := Gp91.GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hH.1 k r ε mu h R Wp Wq (fun _ => 0) (fun _ => 0) f s hDG hgap hok hs
  refine ⟨h1, h2, fun y g hg => ?_⟩
  have hE := GlobalTheory.CapelliEigenvalue.capEig hsm GlobalTheory.capelliDiscreteSeriesInfChar k r ε mu R.H R.σ Wp Wq hDS.1 hDS.2 f hf (y : ℂ) g hg
  rw [(GlobalTheory.ThA.centredCapelli_forms_agree k r _ (y : ℂ) f).1, hE]
  simp only [Formalism.QuantumDeterminants.capP, Complex.ofReal_prod, Complex.ofReal_add]

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalSettingStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.ColDict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_setting : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.BesselMapUniq.BesselMapUniq → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D → ∃ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (Y : Formalism.L2.SG.Full.Full X) (hF : FinX Y) (tr : ∀ u, Transport X u (F u)), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D ∧ (∀ x : X.B.I.E, HEq (X.ιE x) x) ∧ X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧ Formalism.L2.SG.LocVol.IsStdChar ψ ∧ Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ u, LevelMatch X (tr u) Y.hK ∧ ColDictInto X (tr u) Y.hK ∧ ColDictBij X (tr u) Y.hK ∧ ColDictIsom X (tr u) Y.hK (Y.cs u) (hF.shInj u) := by
  first | exact @GlobalTheory.St.SpectralData.exists_spectralData | exact GlobalTheory.St.SpectralData.exists_spectralData | (intros; apply GlobalTheory.St.SpectralData.exists_spectralData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTermLatticeBaseFramesOfBasePointStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_termLattice_baseFrames_of_basePoint : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ t : TauC Y u u', ptPN t = toPts w → ∃ Λ, TG F F' t Λ := by
  first | exact @GlobalTheory.Unfold.tg_of_base_point | exact GlobalTheory.Unfold.tg_of_base_point | (intros; apply GlobalTheory.Unfold.tg_of_base_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalTermLiesOverLocalDatumAfterIsometryStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalTerm_lies_over_localDatum_after_isometry : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' → Gval (lf D F0) F' ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), IsInCell (ZhatOM (ZhatL (lf D F0) F')) w → ZhatOM (ZhatL F00 F'0) = ptMat w → ∀ (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), AtBase Z p F00 F'0 (Tu D u) (Tu D u') P → ∃ d, Over P d (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) := by
  first | exact @GlobalTheory.LocOver.GlobOver.over_local | exact GlobalTheory.LocOver.GlobOver.over_local | (intros; apply GlobalTheory.LocOver.GlobOver.over_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsGenericTermIffNoLocalDefectBaseFramesStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGenericTerm_iff_no_localDefect_baseFrames : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → (t.generic ↔ ∀ p d τ, LocNG.IsTermOver (FP p) d τ → τ.abelian₂ = lattice₂ D Z.M p Λ → ¬ LocNG.BBne (H := locH Z p) τ) := by
  first | exact @GlobalTheory.Unfold.GenLoc.generic_iff_local | exact GlobalTheory.Unfold.GenLoc.generic_iff_local | (intros; apply GlobalTheory.Unfold.GenLoc.generic_iff_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTwoSidedHaarOfLeftInvariantProbabilityCompactUStatement
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTwoSidedHaar_of_leftInvariant_probability_compactUnitary : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ → μ Set.univ = 1 → B.IsHaarOn (UWset k r z) μ := by
  first | exact @GlobalTheory.ThA.haarW_twoSided_of_left | exact GlobalTheory.ThA.haarW_twoSided_of_left | (intros; apply GlobalTheory.ThA.haarW_twoSided_of_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabelsFixedByTupleOperatorOfTypeSeries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.LabPinTop

theorem kap_mem_GfC {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (k : X.B.I.Gf) : kap X h t k ∈ GfC (Yc D 0) := by
  have aux : ∀ (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (k : I.Gf),
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA hI.symm)).symm ((1, k) : I.GA) ∈ GfC (D.sp.Y 0) := by
    intro I hI k
    subst hI
    have e : ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)).symm (1, k) =
        (Formalism.IndefR.RationalEmbedding.iota D).symm (1, k) := rfl
    rw [e]
    exact (Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (D := D) (1, k)).2 rfl
  have hy : (iotaX X h).symm ((1, k) : X.B.I.GA) ∈ GfC (D.sp.Y 0) := aux X.B.I h k
  show (t⁻¹ * (iotaX X h).symm (1, k) * t : GA D (D.sp.Y 0)) ∈ GfC (D.sp.Y 0)
  unfold GfC at hy ⊢
  rw [MonoidHom.mem_ker] at hy ⊢
  rw [map_mul, map_mul, hy, mul_one, map_inv, inv_mul_cancel]

theorem R_translate_ae {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (Φ : GA D (D.sp.Y 0) → ℂ) (hinv : ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, Φ (γ * g) = Φ g) (f : L2X X)
    (hf : f =ᵐ[muX X] fun x => Φ ((iotaX X h).symm x * t)) (k : X.B.I.Gf) :
    ((X.B.R (1, k) f : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x =>
      Φ ((iotaX X h).symm x * t * (show GA D (D.sp.Y 0) from kap X h t k)) := by
  have hU : X.B.μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have := Formalism.MainNotions.LeviCoordinates.rr_muA_left X.B.I X.B.μf
  have hFD := Formalism.MainNotions.LeviCoordinates.rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec
  have hφinv : ∀ γ ∈ X.B.I.GFset, ∀ y : X.B.I.GA,
      Φ ((iotaX X h).symm (γ * y) * t) = Φ ((iotaX X h).symm y * t) := by
    intro γ hγ y
    rw [map_mul, mul_assoc]
    exact hinv _ (iotaX_symm_rat X h γ hγ) _
  have hP : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) ((1, k) : X.B.I.GA) :=
    Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k
  have hPi : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) (((1, k) : X.B.I.GA)⁻¹) := by
    have : ((1, k) : X.B.I.GA)⁻¹ = (1, k⁻¹) := Prod.ext inv_one rfl
    rw [this]; exact Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k⁻¹
  obtain ⟨h1, h2⟩ := Formalism.L2.SG.Pf.rp_map hFD hP hPi
  have e1 := X.B.R_spec (1, k) f
  have e3 : ∀ᵐ x ∂(muX X), (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) =
      Φ ((iotaX X h).symm (X.B.I.rep X.B.fund (x * (1, k))) * t) := by
    refine ae_of_ae_map (p := fun y => (f : X.B.I.GA → ℂ) y = Φ ((iotaX X h).symm y * t)) h1 ?_
    rw [h2]
    exact hf
  filter_upwards [e1, e3] with x a1 a3
  rw [a1]
  show (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) = _
  rw [a3]
  obtain ⟨γ, hγ, hrep, -⟩ := Formalism.MainNotions.LeviCoordinates.rr_rep_spec hFD (x * (1, k))
  rw [Formalism.MainNotions.LeviCoordinates.rr_rep_eq_rep, show (Formalism.MainNotions.LeviCoordinates.rr_rep X.B.I.GFset X.B.fund (x * (1, k))) = γ * (x * (1, k)) from hrep,
    hφinv γ hγ]
  congr 1
  unfold kap
  rw [map_mul]
  group

end GlobalTheory.LabPinTop

namespace GlobalTheory.LabPinTop

theorem labTie_of_series : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (C : Submodule ℂ (MMap (R.MY 0))), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ F, ι (D.sEE F) = conjHH X G (j F)) → RowJ R eE X h G t j → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotIn (actM PY (R.MY 0)) C (FinTyp.conjT (rep (D.what₂.ft σ)))) → (∀ σ, ∀ k ∈ X.B.I.Kg X.B.g, ∀ v y, R.HE.e (eE (D.what₂.onb σ)) v (y * kap X h t k) = R.HE.e (eE (D.what₂.onb σ)) v y) → (∀ σ v, ∀ γ ∈ Formalism.L2.Theta.GQ (Yc D 0), ∀ y, R.HE.e (eE (D.what₂.onb σ)) v (γ * y) = R.HE.e (eE (D.what₂.onb σ)) v y) → TypeLab D rep → (∀ σ, D.ntypes.goodTuple (labOf σ)) → LabTie X ι := by
  intro D X h t PY hF G' _ _ Pl0 T A Ks _ _ _ R eE G j ι rep C hStd hHEq hι hJ hiso hK hQ hTL hgood
  let _ : Fintype (G0g D.nd) := Formalism.MainNotions.PrimeDegreeVariant.finiteLevelGroupFintype D
  have hlab : ∀ σ k v, IsLabel D k (D.nd.lab k (D.what₂.ft σ) v) := fun σ k v => ((hTL (D.what₂.ft σ)) k v).1
  refine ⟨hlab, hgood, fun σ => ?_⟩
  obtain ⟨c, red, hFR⟩ := GlobalTheory.T.exists_maximalCompact_reduction_standardFrame D X h t PY hF hStd hHEq
  have hRH : IsRedHom X red := hFR.1
  choose sec hsec using hRH.2.2.1
  have hIS : IsSec X red sec := fun γ => hsec γ
  choose lf hlf using fun γ => PY.onto _ (kap_mem_GfC X h t (sec γ))
  have hser := GlobalTheory.T.sum_seriesIdempotentCoeff_rightTranslation D X h t PY c red sec lf hFR hIS hlf (rep (D.what₂.ft σ)) (labOf σ) (hTL (D.what₂.ft σ))
  have hS := GlobalTheory.T.fixedVectorIdentity_isotypic_conjugateType D D.R.r (MMap (R.MY 0)) (actM PY (R.MY 0)) C (rep (D.what₂.ft σ))
    {κ | ∃ k ∈ X.B.I.Kg X.B.g, PY.ψ κ = kap X h t k} (G0g D.nd) (serCoef (labOf σ)) lf
    (fun φ hφ hU => hser φ hφ (fun k hk κ hκ => hU κ ⟨k, hk, hκ⟩)) (R.HE.e (eE (D.what₂.onb σ))) (hiso σ)
    (by
      rintro κ ⟨k, hk, hκ⟩
      refine MultilinearMap.ext fun v => funext fun y => ?_
      rw [actM_apply, hκ]
      exact hK σ k hk v y)
  have hpt : ∀ v y, ∑ γ, star (serCoef (labOf σ) γ) * R.HE.e (eE (D.what₂.onb σ)) v (y * kap X h t (sec γ)) =
      R.HE.e (eE (D.what₂.onb σ)) v y := by
    intro v y
    have e := congrArg (fun T : MMap (R.MY 0) => T v y) hS
    simp only [finsum_eq_sum_of_fintype] at e
    rw [← e, sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [smul_apply, Pi.smul_apply, smul_eq_mul, actM_apply, hlf]
  obtain ⟨v₀, -, a, -, hj⟩ := hJ
  refine GlobalTheory.T.mem_rowsFixedByLabelTupleOp_of_sum_fixed D X red sec hRH hIS (labOf σ) (fun k v => hlab σ k v) (bRow X ι σ)
    (ι (D.sEE (D.what₂.onb σ))).2 ?_
  set Φ : GA D (D.sp.Y 0) → ℂ := fun y => star ((a : ℂ) * R.HE.e (eE (D.what₂.onb σ)) v₀ y) with hΦ
  have hΦinv : ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, Φ (γ * g) = Φ g := fun γ hγ g =>
    congrArg (fun z => star ((a : ℂ) * z)) (hQ σ v₀ γ hγ g)
  have hb : bRow X ι σ = star ((j (D.what₂.onb σ) : EEC X G) : L2X X) := by
    show ((ι (D.sEE (D.what₂.onb σ)) : HHX X) : L2X X) = _
    rw [hι]
    rfl
  have hbr : (bRow X ι σ : X.B.I.GA → ℂ) =ᵐ[muX X] fun x => Φ ((iotaX X h).symm x * t) := by
    rw [hb]
    filter_upwards [Lp.coeFn_star ((j (D.what₂.onb σ) : EEC X G) : L2X X), hj (D.what₂.onb σ)] with x b1 b2
    rw [b1, Pi.star_apply, b2]
    rfl
  have htr := fun γ => R_translate_ae X h t Φ hΦinv (bRow X ι σ) hbr (sec γ)
  rw [finsum_eq_sum_of_fintype]
  apply Lp.ext
  filter_upwards [coeFn_sum_smul (μ := muX X) (serCoef (labOf σ)) (fun γ => X.B.R ((1, sec γ) : X.B.I.GA) (bRow X ι σ)),
    ae_all_iff.2 htr, hbr] with x b1 b2 b3
  rw [b1, b3]
  simp only [b2, hΦ]
  rw [← hpt v₀ ((iotaX X h).symm x * t)]
  rw [Finset.mul_sum, star_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  have e : ∀ (c b s : ℂ), c * star (b * s) = star (b * (star c * s)) := fun c b s => by
    simp only [star_mul', star_star]; ring
  exact e _ _ _

end GlobalTheory.LabPinTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataGlobalTermIndependentOfRepresentativeStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localData_globalTerm_independent_of_representative : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), PD D Λ (lf D F0) u' F₁ → PD D Λ (lf D F0) u' F₂ → Gval (lf D F0) F₁ ≠ 0 → DCRel Λ (lf D F0) F₁ F₂ → ∀ (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), P.RelG (LocNG.theta (Z.M p)) → ∀ d, Over P d (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')) ↔ Over P d (locU Z p Λ (lf D F0) F₂ (Tu D u) (Tu D u')) := by
  first | exact @GlobalTheory.LocOver.RepIndep.rep_indep | exact GlobalTheory.LocOver.RepIndep.rep_indep | (intros; apply GlobalTheory.LocOver.RepIndep.rep_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalRealDataFunctionsEquivariantContinuous
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SlocTie

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem uh_mul {k r : ℕ} {a b : MatKR k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha', hb']

theorem b_eq_wT (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau) {m : MatKR D.R.k D.R.rS}
    (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    bOf hB u τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) = wT C u τ (m * C.y τ) := by
  have hmy : m * C.y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := uh_mul hm (C.y_mem τ)
  have hJ := Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hmy
  have hex : ∃ γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), uMat γ = C.Q τ * (m * C.y τ) * C.Qi τ :=
    ⟨Formalism.L2.SG.Pf.LocJEq.ujOf' _ hJ, rfl⟩
  unfold wT
  rw [dif_pos hex, Formalism.L2.SG.Pf.LocJEq.wloc_eq C hB u τ]
  have hc : Formalism.MainNotions.S.umat hex.choose = C.Q τ * (m * C.y τ) * C.Qi τ := hex.choose_spec
  rw [hc]
  unfold v0Of sigB
  rw [← Formalism.L2.SG.Pf.LocJEq.sig_mul τ (Formalism.L2.SG.Pf.LocJEq.transp_mem C τ hm)
    (Formalism.L2.SG.Pf.LocJEq.transp_mem C τ (C.y_mem τ))]
  congr 2
  have e : C.Q τ * m * C.Qi τ * (C.Q τ * C.y τ * C.Qi τ) = C.Q τ * m * (C.Qi τ * C.Q τ) * C.y τ * C.Qi τ := by
    simp only [Matrix.mul_assoc]
  rw [e, (C.isT τ).1, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

end GlobalTheory.SlocTie

namespace GlobalTheory.SlocTie

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem isSPsiEquiv_transl {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {W F : MatKR k r → Wp}
    {y : MatKR k r} (s : ℂ) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hW : IsSPsiEquiv z ψ π W)
    (hF : ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), F m = s • W (m * y)) : IsSPsiEquiv z ψ π F := by
  intro h hh n hn g hg
  have hhng : h * n * g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := uh_mul (uh_mul hh.1 hn.1) hg
  rw [hF _ hhng, hF g hg, Matrix.mul_assoc (h * n) g y, hW h hh n hn (g * y) (uh_mul hg hy), map_smul,
    smul_comm s (ψ n)]

theorem continuousOn_transl {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    {W F : MatKR k r → Wp} {y : MatKR k r} (s : ℂ) (hy : y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hW : ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)))
    (hF : ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), F m = s • W (m * y)) :
    ContinuousOn F (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  have h1 : ContinuousOn (fun m : MatKR k r => s • W (m * y)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :=
    (hW.comp (continuous_id.matrix_mul continuous_const).continuousOn fun m hm => uh_mul hm hy).const_smul s
  exact h1.congr hF

theorem phi_eq (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), (locS hB u u' τ).Φ m = (1 : ℂ) • wT C u τ (m * C.y τ) :=
  fun m hm => by rw [one_smul]; exact b_eq_wT C hB u τ hm

theorem phi'_eq (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) :
    ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
      (locS hB u u' τ).Φ' m = sclOf hB u u' τ • wT C u' τ (m * C.y τ) :=
  fun m hm => by
    show sclOf hB u u' τ • bOf hB u' τ (sigB X (C.Q τ) (C.Qi τ) τ m (v0Of C τ)) = _
    rw [b_eq_wT C hB u' τ hm]

theorem tie_of (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hc : ∀ u, ContinuousOn (wT C u τ) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)))
    (he : ∀ u, IsSPsiEquiv (zB X (C.Qi τ) u τ) (psiS D (zB X (C.Qi τ) u τ)) (piB X (C.Q τ) (C.Qi τ) u τ) (wT C u τ)) :
    IsSPsiEquiv (locW C u u' τ).z (psiS D (locW C u u' τ).z) (locW C u u' τ).π (locS hB u u' τ).Φ ∧
    IsSPsiEquiv (locW C u u' τ).z' (psiS D (locW C u u' τ).z') (locW C u u' τ).π' (locS hB u u' τ).Φ' ∧
    ContinuousOn (locS hB u u' τ).Φ (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
    ContinuousOn (locS hB u u' τ).Φ' (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :=
  ⟨isSPsiEquiv_transl 1 (C.y_mem τ) (he u) (phi_eq C hB u u' τ),
    isSPsiEquiv_transl _ (C.y_mem τ) (he u') (phi'_eq C hB u u' τ),
    continuousOn_transl 1 (C.y_mem τ) (hc u) (phi_eq C hB u u' τ),
    continuousOn_transl _ (C.y_mem τ) (hc u') (phi'_eq C hB u u' τ)⟩

end GlobalTheory.SlocTie

namespace GlobalTheory.SlocTie

theorem locS_phi_equiv_cont : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C)
    (u u' : D.what₂.Word) (τ : D.what₂.Tau), Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
    IsSPsiEquiv (locW C u u' τ).z (psiS D (locW C u u' τ).z) (locW C u u' τ).π (locS hB u u' τ).Φ ∧
    IsSPsiEquiv (locW C u u' τ).z' (psiS D (locW C u u' τ).z') (locW C u u' τ).π' (locS hB u u' τ).Φ' ∧
    ContinuousOn (locS hB u u' τ).Φ (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
    ContinuousOn (locS hB u u' τ).Φ' (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :=
  fun D X θ C hB u u' τ _ =>
    tie_of C hB u u' τ (fun u => Formalism.L2.SG.Pf.LocF.local_continuity_all D X θ C u τ)
      (fun u => Formalism.L2.SG.Pf.EquivPf.local_equivalence_all D X θ C u τ)

end GlobalTheory.SlocTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsGlobalTermPhase
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.MovedTermPhase

theorem exists_termFrame_admissibilityWitness : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : TauC Y u u'), ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), AdmWit t.lam (gS D) (lf D (X.Fu u)) t.frame ξ := by
  intro D X Y u u' t
  exact t.rep.2.2.2.2.2.1

theorem psiInf_exp : ∀ {E : Type} [Field E] [NumberField E] (g : ℕ) (x y : E), Complex.exp (-(2 * Real.pi * Complex.I * ((Algebra.trace ℚ E (x / g) : ℚ) : ℂ))) = (Formalism.L2.SG.PairVal.psiInf g x)⁻¹ ∧ Formalism.L2.SG.PairVal.psiInf g (x - y) = Formalism.L2.SG.PairVal.psiInf g x * (Formalism.L2.SG.PairVal.psiInf g y)⁻¹ := by
  intro E _ _ g x y
  refine ⟨?_, ?_⟩
  · have hx : x / (g : E) = ((g : ℚ)⁻¹) • x := by
      rw [Algebra.smul_def, div_eq_inv_mul]
      simp
    rw [Formalism.L2.SG.PairVal.psiInf, ← Complex.exp_neg, hx, LinearMap.map_smul, smul_eq_mul]
    congr 1
    push_cast
    ring
  · simp only [Formalism.L2.SG.PairVal.psiInf, map_sub]
    rw [← div_eq_mul_inv, ← Complex.exp_sub]
    congr 1
    push_cast
    ring

theorem main : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → G.IsTerm (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) ∧ ∀ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ → G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) = (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp U))⁻¹ * Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp U') * (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))))⁻¹ := by
  intro D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  obtain ⟨hg0, hcg⟩ := GlobalTheory.T.localScalar_mul_eq_differentGen_mul_theta D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  have hlat := GlobalTheory.T.movedRowLattice_term_isLattice D X Y u u' _ F00 F'0 FP G c t₀ ρ
  have hU := hMv.2.1
  have hU' := hMv.2.2.1

  have hext : ∀ (N : G.GLV) p, ∃ m : (G.S p).GLV, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N m :=
    fun N p => ((GlobalTheory.HL.RatExt.rational_extend (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ p).2.2.1 N).exists

  have key : ∀ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
      AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ →
      ∃ N N' : G.GLV, (∀ b, N (G.f b) = ∑ a, U a b • G.f a) ∧
        (∀ b, N' (G.f' b) = ∑ a, (U' * (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))⁻¹) a b • G.f' a) ∧
        ∀ p (m m' : (G.S p).GLV), (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N m →
          (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N' m' →
          (G.S p).IsTerm ((G.S p).datOf ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)))
              ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)) ∧
            (G.S p).om ((G.S p).datOf ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)))
              ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)) =
              (G.S p).psi m * ((G.S p).psi' m')⁻¹ := by
    intro ξ hξ
    have hξl : ∀ i j, j < i → (ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) i j = 0 := by
      intro i j hij
      simp [Matrix.map_apply, hξ.1 i j hij]
    have hξd : ∀ i, (ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) i i = 1 := by
      intro i
      simp [Matrix.map_apply, hξ.2.1 i]
    obtain ⟨hBl, hBd, -⟩ := GlobalTheory.T.unitriangular_mul_inv_superdiagonalSum_sub U' _ (fun i j h => (hU' i j).1 h) (fun i => (hU' i i).2 rfl) hξl hξd
    obtain ⟨⟨N, hN⟩, -⟩ := GlobalTheory.T.unitriangularFrameChange_from_linearAut (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G U
      (fun i j h => (hU i j).1 h) (fun i => (hU i i).2 rfl)
    obtain ⟨-, ⟨N', hN'⟩⟩ := GlobalTheory.T.unitriangularFrameChange_from_linearAut (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G
      (U' * (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))⁻¹) hBl hBd
    refine ⟨N, N', hN, hN', ?_⟩
    intro p m m' hm hm'
    obtain ⟨t, d, hto, hlatEq, hf, hf'⟩ := GlobalTheory.T.movedTerm_lattice_isLocalTerm_at_place D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U'
      hMv p ξ hξ N N' hN hN' m m' hm hm'
    obtain ⟨h1, -⟩ := GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates (Y.M p) (Y.agree p).1 (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p)
      D.R.rS D.R.k (FP p) (G.S p) (c.c p)
    obtain ⟨hT, hom, -⟩ := h1 d t hto
    rw [hlatEq] at hT hom
    have : IsNonarchimedeanLocalField ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp :=
      ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).lf
    have : CharZero ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp :=
      ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).char0
    have hd := (GlobalTheory.T.hermitian_lattice_datum_equivariant_flag_isometries ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L p) D.R.rS D.R.k (G.S p)).1 _ _ hT
    rw [hd] at hT hom
    have hpsi := GlobalTheory.T.localTermWeight_eq_character_mul_inv (Y.M p) (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS D.R.k (FP p) (G.S p)
      (c.c p) d t hto m m' hf hf'
    exact ⟨hT, hom ▸ hpsi⟩

  have hsig : ∀ x, D.conjF x = star x := fun x => by
    rw [D.conjF_eq]
    exact (Formalism.BasicNotions.bridge_star_holds _ D.host x).symm
  have hprod := fun (n : G.GLV) (m : ∀ p, (G.S p).GLV)
      (hx : ∀ p, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p n (m p)) =>
    GlobalTheory.HL.PhaseProduct.main (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G D.sp.cm hsig
      (fun p => Units.mk0 (Y.δ p) (Y.agree p).2.1) (gS D) hg0
      (fun p y => (Y.agree p).2.2.2.2.1 y)
      (fun p => hcg p) n m hx
  obtain ⟨ξ₀, hξ₀⟩ := exists_termFrame_admissibilityWitness D X Y u u' t₀
  refine ⟨⟨hlat, fun p => ?_⟩, ?_⟩
  · obtain ⟨N, N', -, -, hloc⟩ := key ξ₀ hξ₀
    obtain ⟨m, hm⟩ := hext N p
    obtain ⟨m', hm'⟩ := hext N' p
    exact (hloc p m m' hm hm').1
  · intro ξ hξ
    obtain ⟨N, N', hN, hN', hloc⟩ := key ξ hξ
    choose m hm using hext N
    choose m' hm' using hext N'
    obtain ⟨hP, -, hfin⟩ := hprod N m hm
    obtain ⟨-, hP', hfin'⟩ := hprod N' m' hm'
    have hom : G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) =
        ∏ᶠ p, ((G.S p).psi (m p) * ((G.S p).psi' (m' p))⁻¹) :=
      finprod_congr fun p => (hloc p (m p) (m' p) (hm p) (hm' p)).2
    have hs1 : (Function.mulSupport fun p => (G.S p).psi (m p)).Finite :=
      hfin.subset fun p hp => Or.inl hp
    have hs2 : (Function.mulSupport fun p => ((G.S p).psi' (m' p))⁻¹).Finite :=
      hfin'.subset fun p hp => Or.inr fun h => (Function.mem_mulSupport.1 hp) (by simp [h])
    rw [hom, finprod_mul_distrib hs1 hs2, finprod_inv_distrib, hP, hP',
      (GlobalTheory.T.simpleRootCoef_eq_superdiagonal_sum_frames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G U N).1 hN,
      (GlobalTheory.T.simpleRootCoef_eq_superdiagonal_sum_frames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G _ N').2 hN',
      (psiInf_exp (gS D) _ 0).1, (psiInf_exp (gS D) _ 0).1, inv_inv]
    have hξl : ∀ i j, j < i → (ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) i j = 0 := by
      intro i j hij
      simp [Matrix.map_apply, hξ.1 i j hij]
    have hξd : ∀ i, (ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) i i = 1 := by
      intro i
      simp [Matrix.map_apply, hξ.2.1 i]
    rw [(GlobalTheory.T.unitriangular_mul_inv_superdiagonalSum_sub U' _ (fun i j h => (hU' i j).1 h) (fun i => (hU' i i).2 rfl) hξl hξd).2.2,
      (psiInf_exp (gS D) _ _).2, mul_assoc]

end GlobalTheory.HL.MovedTermPhase
end

