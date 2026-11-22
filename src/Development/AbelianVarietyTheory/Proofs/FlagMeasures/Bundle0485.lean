import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpBoundsUniformOfInputs
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0484
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0473
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0440
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0466
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0435
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0457
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0453
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0338
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsWordLetters
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0062
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp
import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DoubleCosetBesselBoundOfGapConstantLe
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0467
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0358
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0480
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0478
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0422
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0071
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0416
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0402
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0006
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0475
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0477
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0469
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0333
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0380
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0433

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeBoundsUniformLargeGapFamilies
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.GapAmpUniform

theorem weyl_fam_gap : ∀ (eps : ℝ) (Fm : FamP eps), VanishingOnXAndXPlusBranching.FamilyTwelfthHypothesis Fm := by
  intro eps Fm x i τ w H _ _ z π hπ
  obtain ⟨g, -, hg⟩ := hπ
  exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (GlobalTheory.CritLevel.isHCParam_uS (Fm.D x i) w τ)).1 H _ hg

theorem amplitude_bounds_uniform_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 : ℝ, ∃ C C2 Ch thr : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cpr : ℝ, ∀ δ > 0, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlus.AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ) := by
  intro hM hH hB Cg cb Cu cT CT C0 A C1
  obtain ⟨CPT, t1, hPT⟩ := GlobalTheory.T.uniform_amplitude_bound_wide_range_large_gap hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨CDl, t2, hDl⟩ := GlobalTheory.FamDlGap.ptDl_along_family_gap hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨t3, h5⟩ := GlobalTheory.CritLevelGap.tcritLow_along_family_gap hM hH hB Cg cb Cu cT CT C0
  obtain ⟨t4, h9⟩ := GlobalTheory.AmpFamGap.amplitudeNormDegree_along_family_largeGaps hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨hilbertNinetyConstant, t5, hilbertNinetyConstant_pos, hDeg⟩ := GlobalTheory.DegStepG.degI_along_family hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨Ca, t6, hCa, hAC⟩ := GlobalTheory.GapUAmp.abs_all_along_family_gap hM hH hB Cg cb Cu cT CT C0 A C1
  obtain ⟨CS, t8, hS⟩ := GlobalTheory.GapAmp.schur_along_family hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨C, C2, Ch, hC, hCh, H⟩ := GlobalTheory.ampBounds_uniform_of_inputs Cg cb Cu cT CT C0 A C1 CPT CDl hilbertNinetyConstant Ca CS hilbertNinetyConstant_pos hCa
  refine ⟨C, C2, Ch, max t1 (max t2 (max t3 (max t4 (max t5 (max t6 t8))))), hC, hCh, ?_⟩
  intro eps Fm h1 h2 hR Cpr δ hδ
  exact H eps Fm
    (hPT eps Fm ((le_max_left _ _).trans h1) ((le_max_left _ _).trans h2) hR)
    (hDl eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (h5 eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (h9 eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (hDeg eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (hAC eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR).1
    (hAC eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR).2
    (hS eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (weyl_fam_gap eps Fm) Cpr δ hδ

end GlobalTheory.GapAmpUniform
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBessel
section
namespace GlobalTheory

theorem uniqGap_and_besselOfW : GlobalTheory.GapIn.UniqGap ∧ Formalism.L2.SG.LocWSOf.BesselOfW :=
  ⟨CompanionTheory.Lime.BM.uniqGap_holds, Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOneNonGenericRowBoundClosed
section
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

namespace GlobalTheory.NGRowClose

theorem rowNGP_of_formNGVanish (hSW : PI.VolStabS.MassDataS.SWXS) (hC : StepChoiceConstantsC)
    (hP : StepPinExists) (hF : Formalism.L2.SG.NGVanish.FormNGC) (hB : StepThmBPinnedP) :
    RowNGP := by
  obtain ⟨h5, hw, h4, he⟩ := GlobalTheory.T.nongeneric_row_statements_of_family_statements GlobalTheory.T.non_generic_corank_one_terms_family_cut_by_defect
  exact GlobalTheory.T.corankOnePairsNonGenericRowBound_of_remaining_premises hC hP hF hB (h5 GlobalTheory.T.familyRowWeightSumUnfoldingIdentity) (hw (GlobalTheory.T.familyGenericMassPositiveBounded_proof hSW))
    (h4 GlobalTheory.T.familyGroupSumFactorsRowWeightAmplitude_proof) (he GlobalTheory.T.familyLocalObjectsExistAtTerms_proof)

theorem close : PI.VolStabS.MassDataS.SWXS → StepChoiceConstantsC → StepPinExists →
    Formalism.L2.SG.NGVanish.FormNGC → StepThmBPinnedP → RowNGP :=
  fun hSW hC hP hF hB => rowNGP_of_formNGVanish hSW hC hP hF hB

end GlobalTheory.NGRowClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericFamilyStepOfSiegelWeil
section
open GlobalTheory.SnFam

namespace GlobalTheory.SnFamTop

theorem stepFamG_of_SWXS (hSW : PI.VolStabS.MassDataS.SWXS) :
    Formalism.L2.SG.Pf.MainEqFam.StepFamG :=
  GlobalTheory.T.genericRow_familyStep_of_leaves
    (fun D h => GlobalTheory.localMass_le_genericMass_nine _ _ h)
    GlobalTheory.T.differentLocalIdentity_familiesLemmaH GlobalTheory.T.genericScalarClassTerms_formFamily GlobalTheory.T.familyRowWeightSumUnfoldingIdentity (GlobalTheory.T.familyGenericMassPositiveBounded_proof hSW) GlobalTheory.T.familyGroupSumFactorsRowWeightAmplitude_proof GlobalTheory.T.familyLocalObjectsExistAtTerms_proof

end GlobalTheory.SnFamTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TypePOfLargeGapDiscreteSeriesBessel
section
namespace GlobalTheory.TypeAsm.TopGap

theorem typeBound_of_gap :
    GlobalTheory.GapIn.Hyp → Formalism.L2.SG.LocWSOf.BesselOfW → Formalism.L2.SG.RowsPos.TypeP := by
  intro hH hBW

  have hAmp : GlobalTheory.TypeAsm.AmpP :=
    GlobalTheory.T.amplitudeBound_at_terms_of_localData (GlobalTheory.TypeAsm.locDatC_of_besselOfW hBW) (GlobalTheory.T.localDataTailBound_closedForm_largeGaps hH)

  have hPairs : GlobalTheory.TypeAsm.PairsP :=
    GlobalTheory.T.termPairCountBound_of_siegelMassRatios GlobalTheory.Mass.MaxFormula.main GlobalTheory.Mass.siegelMassRatio_holds
  exact GlobalTheory.TypeAsm.typeBound_of_amplitude_pairs hAmp hPairs

end GlobalTheory.TypeAsm.TopGap
end

