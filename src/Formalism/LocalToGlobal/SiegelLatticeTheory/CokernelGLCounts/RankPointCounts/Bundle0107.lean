import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0056
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0041
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0052
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0054
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0064
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0038
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0051
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PcIntGen
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OneSmulApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0071
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0100
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0098
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupOrb
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0095
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.VolumeNormalizedOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPhaseG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0103
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0090
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0086
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0106
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0102
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0081
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0069
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0079
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0072
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0099
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.StepPinExistsHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0068
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0096
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0094
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UniformDenominatorExpansionLocal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0063
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0016
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0076

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefCutDeep
section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cutAt_of_deep {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {δ : ∀ p : PlF D, (D.s.atP p).Fp} {L : CntLocal.LocSp D M} {u u' : D.what₂.Word}
    {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hsig : (VS D).SigOK) (hA : ∀ p, Agree δ M p) (hc : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2])
    (hP : PrimeHyp D u (Tu D u')) (hrows : IsRowReps D F0 what₂)
    (hst : ProdEP2Cut.StepsU M δ u u' F0 what₂)
    (hSA : TupGlob.StabApprox ⟨δ, M, hA⟩ u u')
    (hFS : FrameGlobalPatching.FStarC ⟨δ, M, hA⟩ u u' F0 what₂) :
    CutAt M δ L u u' F0 what₂ := by
  have hRA : FibPart.RepAtTup M δ u u' F0 what₂ := TupFinal.repAtTup_of_stab ⟨δ, M, hA⟩ u u' F0 what₂ hSA
  have hTF := FibQ.tupFun_holds M δ u u' F0 what₂
  have hOZ := TupOrb.orbZT_holds M δ u u' F0 what₂
  have hfin : ∀ Λ ∈ what₂, ∀ Z : PairVal.MatR D, CntLocal.cntE (CntLocal.Tn u') F0 Λ Z ≠ ⊤ :=
    fun Λ hΛ Z => ZsVolFin.finR D u u' F0 what₂ hrows Z Λ hΛ
  have hN : PairVal.NormRepExists D u u' F0 what₂ := PCount.normRepExists_ctx ⟨hc, hrows, hP⟩
  have hM : Formalism.L2.SG.Pf.NormRepMove D u u' :=
    norm_representative_move D u u' (Formalism.L2.SG.Closed.TermStable_holds D u u') (Formalism.L2.SG.Closed.TermEqIff_holds D u u')
      (Formalism.L2.SG.Closed.TermFun_holds D u u') hP hsig
  exact cutAt_of_leaves hA hc hP hrows hN hM (local_phase_typed_places hA) (ZsVolAsm.volIdxProd_of_prodE M δ u u' F0 what₂ hP
      (ProdE.prodE_CZ_of_approxC M δ u u' F0 what₂ (ProdEApprox.approxC M δ u u' F0 what₂) hst))
    (fun _ => PCountEx.exist_holds hA u u')
    (fun _ => FibPart.sumFr_of M δ hTF hRA hOZ hA hc hP hN hrows hfin)
    (fun _ => FrameGlobalPatching.frGlob_of_fstar hFS) (PCount.intGenP_holds ⟨δ, M, hA⟩) PCount.tau_one_holds
    (PCount.partnerCount_holds_all ⟨δ, M, hA⟩)
    (FibPart.fibSum_of M δ hTF hRA hOZ) (densTh_of_ga (SplitCoefficientComponents.GaPlusTh_holds M δ u u'))

def CutLeavesDeep (D : Formalism.BasicNotions.D7) : Prop :=
  (VS D).SigOK →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (_L : CntLocal.LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] → PrimeHyp D u (Tu D u') →
    ∀ (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
      ProdEP2Cut.StepsU M δ u u' F0 what₂ ∧
      TupGlob.StabApprox ⟨δ, M, hA⟩ u u' ∧
      FrameGlobalPatching.FStarC ⟨δ, M, hA⟩ u u' F0 what₂

theorem rowsDatumP_of_deep {D : Formalism.BasicNotions.D7} (h : CutLeavesDeep D) : RowsDatumP D := by
  unfold CutLeavesDeep at h
  unfold RowsDatumP
  intro hsig δ M hA L u u' hc hP F0 what₂ hrows ϖ hϖ nc hnc
  obtain ⟨hst, hSA, hFS⟩ := h hsig δ M hA L u u' hc hP F0 what₂ hrows
  exact rowsDatum_at (cutAt_of_deep (L := L) hsig hA hc hP hrows hst hSA hFS)
    (eligFinite_of (Formalism.L2.SG.Closed.TermsAtFinite_holds D u u') hsig hrows) hrows ϖ hϖ nc hnc

theorem rowsInputP_of_deep {D : Formalism.BasicNotions.D7} (hN : Formalism.L2.SG.SupportG.NormProd D) (h : CutLeavesDeep D) :
    RowsInputP D :=
  rowsInputP_of_normProd hN (rowsDatumP_of_deep h)

theorem lattice_input_of_open_leaves {D : Formalism.BasicNotions.D7} (h : CutLeavesDeep D) : RowsInputP D :=
  rowsInputP_of_deep (Formalism.L2.SG.Closed.NormProd_holds D) h

end Formalism.L2.SG.Pf.Coef
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqHolds
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut
  Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqClass Formalism.L2.SG.Pf.MainEqAna

namespace Formalism.L2.SG.Pf

theorem normExpDegC_holds : NormExpDegC :=
  normExpDegC_of_leaves Formalism.L2.SG.Closed.FinLeviC_holds Formalism.L2.SG.Closed.OOLintSumC_holds

theorem stepPointsG_holds : StepPointsG :=
  Formalism.L2.SG.Pf.MainEqPoints.stepPointsG_of_leaves Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds
    Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds
    Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds
    Formalism.L2.SG.NonRelPf.nonRelCharC_holds (fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')

theorem stepNormOneG_holds : StepNormOneG :=
  Formalism.L2.SG.NGCut.LeadingMinorIntegrality.Gen.stepNormOneG_of_leaves Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds
    Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds
    Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds
    Formalism.L2.SG.NonRelPf.nonRelCharC_holds (fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')

theorem rowMainEqC_of_open (hNI : Formalism.L2.SG.NGCut.NormalInvariants.Gen.NmlInvG) (hB : StepChoiceConstantsC) (hE : StepPinExists)
    (hF : Formalism.L2.SG.Pf.FormRel.FormRelC) (hL : Formalism.L2.SG.Pf.MainEqLoc.StepLocPinnedG)
    (hT : Formalism.L2.SG.Pf.BDat.StepThmBG) : RowMainEqC :=
  rowMainEqC_of_pinned Formalism.FourierDecayAlt.P.norm_chain stepClassG_holds
    (Formalism.L2.SG.NGCut.NormalInvariants.Gen.stepNormalsG_of hNI Formalism.L2.SG.NGCut.NormalCount.NormCount_holds stepNormOneG_holds)
    stepPointsG_holds stepNormOneG_holds (tieOfCtx_of Formalism.L2.SG.NGLeaves.nondegenerate_gram_tuple) hB hE
    (Formalism.L2.SG.Pf.MainEqVanish.stepTermVanishG_of_form (formGC_of_rel hF)) (stepLocGenPinnedG_of_loc hL)
    (stepThmBPinnedG_of_bdat hT)

theorem rowMainEqC_of_fam (hNL : Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine) (hNI : Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInt)
    (hNS : Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep) (hB : StepChoiceConstantsC) (hE : StepPinExists)
    (hDict : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r) (hFam : Formalism.L2.SG.Pf.MainEqFam.StepFamG)
    (hT : Formalism.L2.SG.Pf.BDat.StepThmBG) : RowMainEqC :=
  rowMainEqC_of_open (nmlInvG_of hNL hNI hNS) hB hE formRelC_holds
    (stepLocPinnedG_of_fam (Formalism.L2.SG.NGLeaves.ranks_of_dictionary hDict) hFam) hT

theorem rowMainEquation_of_family (hB : StepChoiceConstantsC)
    (hDict : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r) (hFam : Formalism.L2.SG.Pf.MainEqFam.StepFamG)
    (hT : Formalism.L2.SG.Pf.BDat.StepThmBG) : RowMainEqC :=
  rowMainEqC_of_fam Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine_holds Formalism.L2.SG.NGCut.NormalIntegrality.NmlInt_holds
    Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep_holds hB Formalism.L2.SG.Closed.StepPinExists_holds hDict hFam hT

theorem rowMainEqC_of_shared (hSW : PI.VolStabS.MassDataS.SWXS)
    (hPC : Formalism.L2.SG.NGAnalytic.MassDataLemmas.OnTied fun _ X _ _ u u' _ ψ => Formalism.L2.SG.LocVol.ProdConv X u u' ψ)
    (hInfG : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
      Formalism.L2.SG.RealObj.InInfinityX X u u' 1)
    (hDict : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r) (hFam : Formalism.L2.SG.Pf.MainEqFam.StepFamG)
    (hB3 : Formalism.L2.SG.ThmBUseR.JointNormBoundRotatedUniform) (hA : Formalism.L2.SG.Pf.BDat.AmpUnif)
    (hR : Formalism.L2.SG.Pf.ThmBChain.RowRestUnifR) : RowMainEqC :=
  rowMainEquation_of_family (choice_massData hSW hPC hInfG) hDict hFam (theoremB_generic_final hB3 hA hR)

theorem rowMainEqC_of_shared2 (hSW : PI.VolStabS.MassDataS.SWXS)
    (hInfG : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
      Formalism.L2.SG.RealObj.InInfinityX X u u' 1)
    (hDict : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r) (hFam : Formalism.L2.SG.Pf.MainEqFam.StepFamG)
    (hB3 : Formalism.L2.SG.ThmBUseR.JointNormBoundRotatedUniform) (hA : Formalism.L2.SG.Pf.BDat.AmpUnif)
    (hR : Formalism.L2.SG.Pf.ThmBChain.RowRestUnifR) : RowMainEqC :=
  rowMainEqC_of_shared hSW Formalism.L2.SG.Pf.ProdConvCut2.prodConv_onTied hInfG hDict hFam hB3 hA hR

end Formalism.L2.SG.Pf
end
end

