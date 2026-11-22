import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0371
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0348
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0409
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0462
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0262
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.UnipotentAdelicQuotients.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
import Formalism.PeriodIntegrals.Bundle0022
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0063
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0377
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0277
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0404
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0364
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0341
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0390
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0313
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0417
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0394
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0421
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0463
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0097
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0056
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscNResNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0422
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0396
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0227
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0460
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0392
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0272

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOnePairsNonGenericRowBoundOfRemainingPremi
section
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

theorem GlobalTheory.rowNGP_of_leaves (hCB : StepChoiceConstantsC) (hPin : StepPinExists) (hForm : Formalism.L2.SG.NGVanish.FormNGC)
    (hThmB : StepThmBPinnedP) (hG5 : Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) (hW : Formalism.L2.SG.FamDefs.WeightsNG)
    (hG4 : Formalism.L2.SG.FamDefs.ProductStructureNonGeneric) (hEx : Formalism.L2.SG.FamDefs.ExistNG) : RowNGP := by
  obtain ⟨hS0, hNml, hPts, hN1, hX0⟩ := GlobalTheory.RowNGClosed.closedSteps
  have hFam : Formalism.L2.SG.NGLocModel.StepFamC := GlobalTheory.T.familyStep_of_four_globalLeaves hG5 hW hG4 hEx
  have hconds : ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39 := fun D =>
    ((GlobalTheory.local_nongeneric_bound_record_family 39 le_rfl).2.1 D).1
  have hLoc : StepLocGenPinnedC :=
    stepLocGenPinnedC_of_loc (Formalism.L2.SG.NGLocModel.stepLocPinnedC_of_fam hconds hFam)
  have hVan : StepVanishPinned :=
    stepVanishPinned_of_term (Formalism.L2.SG.NGVanish.stepTermVanish_of_form hForm)
  have hAna : StepAnalyticP := GlobalTheory.T.rowAnalyticFacts_of_four_steps hPin hVan hLoc hThmB
  have hMassData : StepAnalyticConstantsP := GlobalTheory.T.existsRowLevelWithAnalyticFacts_of_steps (tieOfCtx_of hX0) hCB hAna
  exact GlobalTheory.T.nonGenericCorankOnePairsBound_of_splitFiniteRealRow (GlobalTheory.T.rowSplitFiniteArchimedeanParts_of_steps hMassData sizes_of_hypotheses (stepClass_of_equiv hS0) hNml hPts
    (stepHeight_of_normOne hN1))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubleCosetTermEqIffStabiliserOrbitStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCoset_term_eq_iff_stabiliserOrbit : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t t' : TauC Y u u') n m n' m', t.lam = t₀.lam → t.lam' = t₀.lam' → t'.lam = t₀.lam → t'.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → n' ∈ NRat (lf D (X.Fu u)) ∧ m' ∈ NRat (lf D (X.Fu u')) ∧ t'.lin = n'⁻¹ * t₀.lin * m' → (t = t' ↔ G.LRel (c.lat (ρ * n) t.lam) (c.lat (ρ * n') t'.lam)) := by
  first | exact @GlobalTheory.HL.TermOrbit.term_eq_iff_lRel | exact GlobalTheory.HL.TermOrbit.term_eq_iff_lRel | (intros; apply GlobalTheory.HL.TermOrbit.term_eq_iff_lRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubleCosetTermsSameInnerLatticesStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCoset_terms_same_innerLattices : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∀ p, (G.datOf (c.lat (ρ * n) t.lam) p).1 = (G.datOf (c.lat ρ t₀.lam) p).1 ∧ (G.datOf (c.lat (ρ * n) t.lam) p).2.1 = (G.datOf (c.lat ρ t₀.lam) p).2.1 := by
  first | exact @GlobalTheory.HL.datOf_dcoset | exact GlobalTheory.HL.datOf_dcoset | (intros; apply GlobalTheory.HL.datOf_dcoset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalSetting
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.ColDict

namespace GlobalTheory.St.SpectralData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_transport {D : D7} (F : ∀ u, Formalism.L2.Forms.Forms0 D u)
    (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (hι : ∃ ιA, GlobalTheory.St.IsAdeleIso X ιA) (u : D.what₂.Word) :
    ∃ Tr : Transport X u (F u), LevelMatch X Tr hK := by
  obtain ⟨wt, hw⟩ := GlobalTheory.St.WittT.wittExists D X u
  obtain ⟨ιA, hι⟩ := hι
  obtain ⟨g0, hg0⟩ := GlobalTheory.St.G.genusMatch_holds D F X u wt ιA hw hι
  obtain ⟨h0, hL, hKm⟩ := GlobalTheory.St.G.levelConj_holds D F X hK u wt ιA g0 hw hι hg0
  choose hcf hcr using GlobalTheory.St.G.hcExists_all D F X u wt ιA h0 hw hι
  obtain ⟨J, hJ1, hJ2, hJ3⟩ := GlobalTheory.jExists_all D F X u wt hw
  exact ⟨⟨wt, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, ιA, hι.1, hι.2, h0, hcf, hcr, J, hJ1, hJ2, hJ3⟩, hL, hKm⟩

open Formalism.L2.SG.SplitPrimeNormLemmas in

theorem exists_setting (hSW : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent)
    (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) :
      ∃ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D ∧
        (∀ x : X.B.I.E, HEq (X.ιE x) x) ∧ X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧
        Formalism.L2.SG.LocVol.IsStdChar ψ ∧
        Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧
        ∀ hK : X.LevelSubgroupCharacter, ∀ u, ∃ Tr : Transport X u (F u), LevelMatch X Tr hK := by
  have hB : BesselNVGap := Formalism.L2.SG.Closed.BesselNVGap_holds
  have hC : CoefWeightedLoc := Formalism.L2.SG.Closed.CoefWeightedLoc_holds
  let A := Formalism.L2.SG.InstExistsPf.instanceOfRecord D
  obtain ⟨L⟩ := GlobalTheory.St.Lat.latExists_of_forms0 D (F D.u₀)
  obtain ⟨P⟩ := Formalism.L2.SG.Closed.PsiExists_holds D A
  obtain ⟨Rf⟩ := Formalism.L2.SG.Closed.RefExists_holds D A L
  obtain ⟨Xu⟩ := Formalism.L2.SG.Closed.XuExists_holds D A L Rf
  obtain ⟨Bu⟩ := Formalism.L2.SG.Closed.BunExists_holds D hC hG A L P Rf
  obtain ⟨Pi⟩ := Formalism.L2.SG.Closed.PiExists_holds D A L
  obtain ⟨Mu⟩ := Formalism.L2.SG.Closed.MuExists_holds D A L
  obtain ⟨Wb⟩ := GlobalTheory.WBlockExists.realPlaceFunctionBlockExists_of_bessel_coef hB hC D hG A L P Rf Bu Pi Mu
  obtain ⟨Mb, hb, hM⟩ := GlobalTheory.St.mExists_holds D A L P Rf Xu Bu Pi Mu Wb
  obtain ⟨mg, hg, mw, hw, hM', ψ, hψ, hstd, hCm, hL⟩ :=
    GlobalTheory.St.Rescale.rescaleStep3 hSW D (mk A L P Rf Xu Bu Pi Mu Wb Mb) hb hM
  refine ⟨Formalism.L2.SG.SettingExistsMeasured.withMeas (mk A L P Rf Xu Bu Pi Mu Wb Mb) mg hg mw hw, hb, ψ, rfl,
    fun _ => HEq.rfl, hM', hψ, hstd, hCm, hL, fun hK u => ?_⟩
  exact exists_transport F _ hK ⟨RingEquiv.refl _, fun _ => rfl, fun _ => Iff.rfl⟩ u

theorem exists_spectralData : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.BesselMapUniq.BesselMapUniq → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D → ∃ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (Y : Formalism.L2.SG.Full.Full X) (hF : FinX Y) (tr : ∀ u, Transport X u (F u)), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D ∧ (∀ x : X.B.I.E, HEq (X.ιE x) x) ∧ X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧ Formalism.L2.SG.LocVol.IsStdChar ψ ∧ Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ u, LevelMatch X (tr u) Y.hK ∧ ColDictInto X (tr u) Y.hK ∧ ColDictBij X (tr u) Y.hK ∧ ColDictIsom X (tr u) Y.hK (Y.cs u) (hF.shInj u) := by
  intro hSW hMU hRF D F hG hLT
  obtain ⟨X, hb, ψ, hI, hι, hM, hψ, hstd, hCm, hL, hT⟩ := exists_setting hSW D F hG
  obtain ⟨Y⟩ := GlobalTheory.fullExists_of_locTied D X hLT
  obtain ⟨hWD, hph⟩ := Formalism.L2.SG.Pf.wuDecayOfGap_of_jsz hMU D hG X
  have hF : FinX Y := GlobalTheory.FinitenessBundle.finX_of_decay hRF D X Y hWD hph
  choose tr htr using hT Y.hK
  refine ⟨X, hb, ψ, Y, hF, tr, hI, hι, hM, hψ, hstd, hCm, hL, hph, fun u => ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := GlobalTheory.St.colDictCore_holds D X u (F u) (tr u) Y.hK (htr u)
    (GlobalTheory.columnLevel_stabTriv D X Y.hK u)
  exact ⟨htr u, h1, h2, h3 _ (Y.cs u) (hF.shInj u) (Y.colReps u)⟩

end GlobalTheory.St.SpectralData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalCompactReductionStandardFrameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximalCompact_reduction_standardFrame : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∃ c red, FrameRed X h t PY c red := by
  first | exact @GlobalTheory.LabPin.frameRed_exists | exact GlobalTheory.LabPin.frameRed_exists | (intros; apply GlobalTheory.LabPin.frameRed_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTermLatticeBaseFramesOfBasePoint
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold

theorem tg_of_base_point : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ t : TauC Y u u', ptPN t = toPts w → ∃ Λ, TG F F' t Λ := by
  intro D X Y u u' F F' w hZ hG t hpt
  have hcF : IsInCell (ZhatOM (ZhatL F F')) w := by
    refine ⟨(1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), 1, ?_, ?_, by rw [hZ]; simp⟩
    · intro i j
      exact ⟨fun h => Matrix.one_apply_ne h.ne, fun h => h ▸ Matrix.one_apply_eq i⟩
    · intro i j
      exact ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq i⟩
  have hGw := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.gpt_eq F F' w hcF
  have hw : Formalism.L2.SG.PairVal.ptOf t.toTerm = w := Formalism.L2.SG.NGCut.NormalVectorPairings.toPts_inj _ _ hpt
  have hex : ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant := by
    by_contra h
    apply hG
    rw [← hGw, ← hpt]
    show GPt _ (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) = 0
    unfold Formalism.L2.SG.PairVal.ptOf
    rw [dif_neg h]
    exact Formalism.L2.SG.NGCut.NormalVectorPairings.GPt_junk D u u'
  obtain ⟨F'', ⟨hP, hmk⟩, -, hcell⟩ := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm hex
  rw [hw] at hcell
  have hΛ := (Y.rowsOK u).1 t.lam t.mem
  have hmk' : Formalism.L2.SG.TermDef.mk _ _ _ ⟨F'', hP⟩ = Formalism.L2.SG.TermDef.mk _ _ _ ⟨t.frame, t.rep.2.2.2.2⟩ := hmk
  have hrel := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t.lam hΛ _ _).1 hmk'
  have hcell' : IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t.frame)) w := ((Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam hΛ).2.1 _ _ hrel w).1 hcell
  have hGt : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    intro h0
    apply hG
    rw [← hGw]
    exact (Formalism.L2.SG.NGCut.LeadingMinorIntegrality.gpt_eq (T := Tu D u) (T' := Tu D u') _ _ w hcell').trans h0
  obtain ⟨-, γ, hγ, ⟨A, hA, hc⟩, ⟨B, hB, hd⟩⟩ := GlobalTheory.T.rationalFramePairs_differ_isometry_unitriangular D (lf D (X.Fu u)) F t.frame F' w
    (Formalism.L2.SG.Corank.tu_ne_zero u) (Formalism.L2.SG.Corank.tu_ne_zero u') hGt hcell' hZ
  exact ⟨Formalism.HermitianLatticesTheory.gmap γ t.lam, γ, ⟨hγ, fun a => GlobalTheory.FlagChange.chg_sub_mem F.fl hA hc a⟩,
    ⟨hγ, fun a => GlobalTheory.FlagChange.chg_sub_mem F'.fl hB hd a⟩, rfl⟩

end GlobalTheory.Unfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMeanEmbeddedPairsLeMassMulPairBoundStatement
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genusMean_embeddedPairs_le_mass_mul_pairBound : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → HostC → LatticeNormalizationCondition →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    Module.finrank D.host.E W = D.R.k → GlobalTheory.Mass.PD HW.B.flip → ∀ Λ ∈ Y.what₂ u, ∀ x x' : ℕ, 1 ≤ x → 1 ≤ x' →
      GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom HW.B.flip) (Formalism.HermitianLatticesTheory.genus HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ))
                   (fun L => (((GlobalTheory.DegCnt.Trip HW (gS D) L D.R.rS x x').encard : ℕ∞) : ℝ≥0∞)) ≤
        ENNReal.ofReal (Formalism.HermitianLatticesTheory.mass HW.B.flip (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) *
          GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x') := by
  first | exact @GlobalTheory.PairsRow.main | exact GlobalTheory.PairsRow.main | (intros; apply GlobalTheory.PairsRow.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalTermLiesOverLocalDatumAfterIsometry
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver

namespace GlobalTheory.LocOver.GlobOver

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

theorem uni_mul {K : Type} [CommRing K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : Uni A) (hB : Uni B) :
    Uni (A * B) := by
  obtain ⟨hA0, hA1⟩ := hA
  obtain ⟨hB0, hB1⟩ := hB
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hA0 a c h, zero_mul]
    · rw [hB0 c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA1, hB1, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hA0 a c h, zero_mul]
      · rw [hB0 c a h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h

theorem tri_trans {K W : Type} [CommRing K] [AddCommGroup W] [Module K W] {n : ℕ} {f g h : Fin n → W}
    (h1 : Tri K f g) (h2 : Tri K g h) : Tri K f h := by
  obtain ⟨A, hA, hAc⟩ := h1
  obtain ⟨B, hB, hBc⟩ := h2
  have hAc' : ∀ b, g b = ∑ a, A a b • f a := hAc
  have hBc' : ∀ b, h b = ∑ a, B a b • g a := hBc
  refine ⟨A * B, uni_mul hA hB, fun b => ?_⟩
  rw [hBc' b]
  simp only [hAc', Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]

theorem tri_map {K W W' : Type} [CommRing K] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W'] {n : ℕ}
    (φ : W →ₗ[K] W') {f g : Fin n → W} (h : Tri K f g) : Tri K (fun a => φ (f a)) (fun a => φ (g a)) := by
  obtain ⟨A, hA, hc⟩ := h
  have hc' : ∀ b, g b = ∑ a, A a b • f a := hc
  exact ⟨A, hA, fun b => by simp only [hc' b, map_sum, map_smul]⟩

end Mat

section Loc

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ img g Λ ↔ ∃ y ∈ Λ, g y = x := by
  unfold img
  exact Submodule.mem_map

theorem span_map_le (g : V ≃ₗ[E] V) (S : Set V) :
    ∀ v ∈ Submodule.span M.L.O S, g v ∈ Submodule.span M.L.O ((fun x => g x) '' S) := by
  intro v hv
  have h := Submodule.mem_map_of_mem (f := (g : V →ₗ[E] V).restrictScalars M.L.O) hv
  rw [← Submodule.span_image] at h
  exact h

theorem img_selfDual (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} (hΛ : H.IsSelfDual Λ) : H.IsSelfDual (img g Λ) := by
  obtain ⟨hfg, hsp, hdual⟩ := hΛ
  have hg' : ∀ x y, H.h (g x) (g y) = H.h x y := hg
  have hset : ((img g Λ : Submodule M.L.O V) : Set V) = (g : V →ₗ[E] V) '' (Λ : Set V) := by
    ext x
    simp only [SetLike.mem_coe, mem_img, Set.mem_image, LinearEquiv.coe_coe]
  refine ⟨hfg.map _, ?_, fun x => ?_⟩
  · rw [hset, Submodule.span_image, hsp, Submodule.map_top]
    exact LinearEquiv.range g
  · have hx : x ∈ img g Λ ↔ g.symm x ∈ Λ := by
      rw [mem_img]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro h
        exact ⟨_, h, by simp⟩
    rw [hx, hdual (g.symm x)]
    constructor
    · intro h y hy
      obtain ⟨z, hz, rfl⟩ := (mem_img g Λ y).1 hy
      have := h z hz
      rw [← hg' (g.symm x) z, LinearEquiv.apply_symm_apply] at this
      exact this
    · intro h z hz
      rw [← hg' (g.symm x) z, LinearEquiv.apply_symm_apply]
      exact h (g z) ((mem_img g Λ (g z)).2 ⟨z, hz, rfl⟩)

theorem img_frame (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} {r : ℕ} {f : Fin (r + 1) → V} {T : F} (hf : H.IsFrame Λ r f T) :
    H.IsFrame (img g Λ) r (fun b => g (f b)) T := by
  have hg' : ∀ x y, H.h (g x) (g y) = H.h x y := hg
  obtain ⟨⟨hmem, hli, hsp⟩, hiso, hzz, hT⟩ := hf
  refine ⟨⟨fun a => (mem_img g Λ _).2 ⟨f a, hmem a, rfl⟩, hli.map' _ g.ker, ?_⟩, ?_, ?_, hT⟩
  · intro x hx hxs
    obtain ⟨y, hy, rfl⟩ := (mem_img g Λ x).1 hx
    have hr : Set.range (fun b => g (f b)) = (g : V →ₗ[E] V) '' Set.range f :=
      Set.range_comp (⇑(g : V →ₗ[E] V)) f
    have hys : y ∈ Submodule.span E (Set.range f) := by
      rw [hr, Submodule.span_image, Submodule.mem_map] at hxs
      obtain ⟨z, hz, hzy⟩ := hxs
      rwa [← g.injective hzy]
    have h2 := span_map_le (M := M) g (Set.range f) y (hsp y hy hys)
    have hr' : Set.range (fun b => g (f b)) = (fun x => g x) '' Set.range f :=
      Set.range_comp (fun x => g x) f
    rw [hr']
    exact h2
  · intro a b hab
    rw [hg']
    exact hiso a b hab
  · rw [hg']
    exact hzz

theorem smulLat_map (H : HermSp M V) (g : V ≃ₗ[E] V) (c : E) (Λ : Submodule M.L.O V) {x : V}
    (hx : x ∈ H.smulLat c Λ) : g x ∈ H.smulLat c (img g Λ) := by
  unfold HermSp.smulLat at hx ⊢
  refine Submodule.span_mono ?_ (span_map_le (M := M) g _ x hx)
  rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  exact ⟨g v, (mem_img g Λ (g v)).2 ⟨v, hv, rfl⟩, by simp only [map_smul]⟩

private lemma Zhat_comp_unitary (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {r : ℕ}
    (f f' : Fin (r + 1) → V) :
    H.Zhat (fun b => g (f b)) (fun b => g (f' b)) = H.Zhat f f' := by
  have hg' : ∀ x y, H.h (g x) (g y) = H.h x y := hg
  ext a b
  simp only [HermSp.Zhat, Matrix.of_apply, hg']

private lemma Dl_comp_unitary (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {r : ℕ}
    (f f' : Fin (r + 1) → V) (l : ℕ) :
    H.Dl (fun b => g (f b)) (fun b => g (f' b)) l = H.Dl f f' l := by
  simp only [HermSp.Dl, Zhat_comp_unitary H hg]

theorem isTerm_move (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g) {r : ℕ} {t : Term V M r}
    (ht : H.IsTerm t) : H.IsTerm (move g t) := by
  obtain ⟨hsd, hfr, hfr', hD, hG, hsp⟩ := ht
  refine ⟨img_selfDual H hg hsd, img_frame H hg hfr, img_frame H hg hfr', ?_, ?_, ?_⟩
  · show IsUnit (H.Dl (fun b => g (t.f b)) (fun b => g (t.f' b)) (r + 1))
    rw [Dl_comp_unitary H hg]
    exact hD
  · show H.Gdet (fun b => g (t.f b)) (fun b => g (t.f' b)) t.T t.T' ≠ 0
    simpa only [HermSp.Gdet, Dl_comp_unitary H hg] using hG
  · intro q hq
    obtain ⟨h1, h2, h3⟩ := hsp q hq
    refine ⟨h1, h2, fun b => ?_⟩
    show g (t.f' b) - g (t.f b) ∈ H.smulLat _ (img g t.abelian₂)
    rw [← map_sub]
    exact smulLat_map H g _ t.abelian₂ (h3 b)

end Loc

section Glob

theorem over_local : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' → Gval (lf D F0) F' ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), IsInCell (ZhatOM (ZhatL (lf D F0) F')) w → ZhatOM (ZhatL F00 F'0) = ptMat w → ∀ (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), AtBase Z p F00 F'0 (Tu D u) (Tu D u') P → ∃ d, Over P d (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) := by
  intro D Z u u' F0 Λ hrow F' hPD hG w F00 F'0 hcell hpt p P hAt
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.GramJoint.Tu_pos D u).ne'
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (Formalism.L2.SG.GramJoint.Tu_pos D u').ne'
  obtain ⟨-, γ, hγ, hA, hA'⟩ := GlobalTheory.T.rationalFramePairs_differ_isometry_unitriangular D (lf D F0) F00 F' F'0 w hT hT' hG hcell hpt
  obtain ⟨g, hext, hgU, -, -, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p γ hγ
  obtain ⟨ht0, htri0⟩ := locU_isTerm D Z u u' F0 Λ hrow F' hPD hG p
  have hOK : (Z.M p).OK := (Z.agree p).1
  obtain ⟨A, hAu, hAc⟩ := hA
  obtain ⟨A', hA'u, hA'c⟩ := hA'
  obtain ⟨Ap, hAp, -⟩ := tri_scaled D Z _ _ A hAu hAc
  obtain ⟨Ap', hAp', -⟩ := tri_scaled D Z _ _ A' hA'u hA'c
  have hext' : ∀ x, g (baseChange₂ D p x) = baseChange₂ D p (γ x) := hext
  have hmove : ∀ f : Fin (D.R.rS + 1) → (VS D).V,
      (fun a => g (scaled Z p f a)) = scaled Z p (fun a => γ (f a)) := by
    intro f
    funext a
    simp only [scaled, map_smul, hext']
  set t := locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u') with ht_def
  have hf : Tri (D.s.atP p).Ep P.A.f (move g t).f := by
    rw [hAt.1]
    have h1 : (move g t).f = fun a => g (scaled Z p (frame (lf D F0)) a) := rfl
    rw [h1, hmove (frame (lf D F0))]
    exact ⟨Ap p, hAp p⟩
  have hf' : Tri (D.s.atP p).Ep P.B.f (move g t).f' := by
    rw [hAt.2.1]
    have h1 : Tri (D.s.atP p).Ep (fun a => g (scaled Z p (frame F') a)) (fun a => g (t.f' a)) :=
      tri_map (g : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p) htri0
    rw [hmove (frame F')] at h1
    exact tri_trans ⟨Ap' p, hAp' p⟩ h1
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_datum_of_two_congruent_frames (Z.M p) hOK (locH Z p) D.R.rS P (move g t)
    (isTerm_move (locH Z p) hgU ht0) hAt.2.2.1.symm hAt.2.2.2.symm hf hf'
  refine ⟨d, ?_⟩
  unfold Over
  exact ⟨g, hgU, d, (orbit_reps_over (Z.M p) hOK (locH Z p) D.R.rS P).1.refl d, hd⟩

end Glob

end GlobalTheory.LocOver.GlobOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramInvariantIsometryUnitriangularMovesStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramInvariant_isometry_unitriangular_moves : ∀ {D : D7} {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T') (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), MovesTo F0 F0' F F' ρ U U' → Gval F F' = Gval F0 F0' := by
  first | exact @GlobalTheory.HL.gval_movesTo | exact GlobalTheory.HL.gval_movesTo | (intros; apply GlobalTheory.HL.gval_movesTo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatIffLocalGraphsStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.identificationCompat_iff_localGraphs : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → (IotaCompat t₀.lam (lf D (X.Fu u)) t₀.frame t.frame (t.lin * t₀.lin⁻¹) (gS D) ↔ ∀ p, (G.datOf (c.lat (ρ * n) t.lam) p).2.2 = (G.datOf (c.lat ρ t₀.lam) p).2.2) := by
  first | exact @GlobalTheory.IotaGraph.iotaCompat_iff_graph | exact GlobalTheory.IotaGraph.iotaCompat_iff_graph | (intros; apply GlobalTheory.IotaGraph.iotaCompat_iff_graph <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFramesMovedTermUnitriangularChangeStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFrames_movedTerm_unitriangular_change : ∀ {D : D7} (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T') (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (f' : Fin (D.R.rS + 1) → Vp D p), MovesTo F0 F0' F F' ρ U U' → Ext p ρ g → Tri (D.s.atP p).Ep (scaled Z p (frame F')) f' → Tri (D.s.atP p).Ep (scaled Z p (frame F0)) (fun a => g (scaled Z p (frame F) a)) ∧ Tri (D.s.atP p).Ep (scaled Z p (frame F0')) (fun b => g (f' b)) := by
  first | exact @GlobalTheory.LocOver.triMove_main | exact GlobalTheory.LocOver.triMove_main | (intros; apply GlobalTheory.LocOver.triMove_main <;> assumption)
end

