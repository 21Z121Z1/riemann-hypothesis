import Development.EtaleCohomology.EtaleSheaves.Bundle0030
import Development.EtaleCohomology.EtaleSheaves.FPColimPf
import Development.EtaleCohomology.EtaleSheaves.Bundle0086
import Development.EtaleCohomology.EtaleSheaves.Bundle0014
import Development.EtaleCohomology.EtaleSheaves.TwPairExists
import Development.EtaleCohomology.EtaleSheaves.Bundle0075
import Development.EtaleCohomology.EtaleSheaves.Bundle0017
import Development.EtaleCohomology.EtaleSheaves.Bundle0011
import Development.EtaleCohomology.EtaleSheaves.Bundle0072
import Development.EtaleCohomology.EtaleSheaves.Bundle0009
import Development.EtaleCohomology.EtaleSheaves.Bundle0035
import Development.EtaleCohomology.EtaleSheaves.Bundle0010
import Development.EtaleCohomology.EtaleSheaves.Bundle0024
import Development.EtaleCohomology.EtaleSheaves.Bundle0053
import Development.EtaleCohomology.EtaleSheaves.UnimodularBlockEqToHomValEqOne
import Development.EtaleCohomology.EtaleSheaves.HalfDegreeVanishing.SecondBlockUnimodularLocusInclusionMono
import Development.EtaleCohomology.EtaleSheaves.Bundle0055
import Development.EtaleCohomology.EtaleSheaves.LeafInjSecInjOf
import Development.EtaleCohomology.EtaleSheaves.Bundle0048
import Development.EtaleCohomology.EtaleSheaves.UnitExistence.CocycleOfSec
import Development.EtaleCohomology.EtaleSheaves.Bundle0036
import Development.EtaleCohomology.EtaleSheaves.Bundle0025
import Development.EtaleCohomology.EtaleSheaves.Bundle0058
import Development.EtaleCohomology.EtaleSheaves.Bundle0067
import Development.EtaleCohomology.EtaleSheaves.Bundle0080
import Development.EtaleCohomology.EtaleSheaves.Bundle0037
import Development.EtaleCohomology.EtaleSheaves.Bundle0051
import Development.EtaleCohomology.EtaleSheaves.Bundle0077
import Development.EtaleCohomology.EtaleSheaves.EtaleEvenCohomologyGradedCommRingOfCupRingAxioms
import Development.EtaleCohomology.EtaleSheaves.LeafSecInjPf
import Development.EtaleCohomology.EtaleSheaves.Bundle0049
import Development.EtaleCohomology.EtaleSheaves.Bundle0073
import Development.EtaleCohomology.EtaleSheaves.Bundle0087
import Development.EtaleCohomology.EtaleSheaves.Bundle0081
import Development.EtaleCohomology.EtaleSheaves.Bundle0082
import Development.EtaleCohomology.EtaleSheaves.Bundle0084
import Development.EtaleCohomology.EtaleSheaves.Bundle0038
import Development.EtaleCohomology.EtaleSheaves.Bundle0026
import Development.EtaleCohomology.EtaleSheaves.LeafTwTensExistsPf
import Development.EtaleCohomology.EtaleSheaves.TwistTensorRestriction
import Development.EtaleCohomology.EtaleSheaves.Bundle0056
import Development.EtaleCohomology.EtaleSheaves.Bundle0050
import Development.EtaleCohomology.EtaleSheaves.UnitSections
import Development.EtaleCohomology.EtaleSheaves.Bundle0013
import Development.EtaleCohomology.EtaleSheaves.LeafZModInjFlatPf
import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
import Development.EtaleCohomology.EtaleSheaves.Bundle0066
import Development.EtaleCohomology.EtaleSheaves.LeafDescendMapPf
import Development.EtaleCohomology.EtaleSheaves.Bundle0076
import Development.EtaleCohomology.EtaleSheaves.Bundle0079
import Development.EtaleCohomology.EtaleSheaves.Bundle0083
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
import Development.EtaleCohomology.EtaleSheaves.Bundle0029
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback

-- bundled from Development.EtaleCohomology.EtaleSheaves.ArchimedeanComparison
section
theorem LateralTheory.E.TruncationIsoComparison.IEComp_of : LateralTheory.E.t_E3Cut.IEComp :=
  LateralTheory.E.IECompPf.IEComp_of (LateralTheory.E.UnderFAPf.UnderFA_of LateralTheory.E.FPColimPf.FPColim_of)
    (LateralTheory.E.SpreadPf.Cut.EtSpreads_of LateralTheory.E.SpreadPf.FPProof.finite_presentation_ring_maps_pre_ind_spread LateralTheory.E.EtStagePf.EtStage_of)
theorem LateralTheory.E.TruncationIsoComparison.Comp_of : LateralTheory.E.SHExistsPf.Comp := @LateralTheory.E.TruncationIsoComparison.IEComp_of
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.AwSpec
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.Fix.EtaleChapterDTwo

theorem awSpec : LateralTheory.E.LeafA6suppPf.LeafAWSpec := by
  intro q _ E n m i j α β
  have hS := LateralTheory.Fix.CupProductTensor.cupSpec (ZMod q) (twPair q i j) E (rfl : n + m = n + m)
  obtain ⟨γ, hγ⟩ := hS.1 α β
  exact ⟨γ, hγ, hS.2 α β γ hγ⟩

theorem s0 : LateralTheory.E.D2.LeafA6nat := @_root_.LateralTheory.E.LeafA6nat_xy7V2Cut.goal_of
theorem s1 : LateralTheory.E.CupProductRingLaws.LeafCupSpec := @_root_.LateralTheory.Fix.CupProductTensor.cupSpec
theorem s2 : LateralTheory.E.CupProductRingLaws.LeafTwPairExists := @_root_.LateralTheory.Fix.CupProductTensor.twPairExists
theorem s3 : LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensExists := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensExists_of
theorem s4 : LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor_of
theorem s5 : LateralTheory.E.ZModFlatnessFromBaerCriterion.TensTwRes := @_root_.GlobalTheory.EtC.isTwRes_tensor
theorem s6 : LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj := @_root_.LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj_of
theorem s7 : LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjFlatZMod := @_root_.LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjFlatZMod_of
theorem s8 : LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensRes := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensRes_of s5 s6 s7
theorem s9 : LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy_of
theorem s10 : LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy := @_root_.LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy_of s3 s4 s8 s9
theorem s11 : LateralTheory.E.LeafTwPairUniquePf.LeafHtpyAW := @_root_.LateralTheory.E.FreeSheafGeneratorLifts.LeafHtpyAW_proved
theorem s12 : LateralTheory.E.CupProductRingLaws.LeafTwPairUnique := @_root_.LateralTheory.E.CupProductRingLaws.LeafTwPairUnique_of s1 s10 s11
theorem s13 : LateralTheory.E.LeafOneExistsPf.LeafUnitSec := @_root_.LateralTheory.E.UnitSections.LeafUnitSec_of
theorem s14 : LateralTheory.E.LeafOneSpecPf.LeafOneExists := @_root_.LateralTheory.E.LeafOneExistsPf.CocycleOfSec.LeafOneExists_of_unit s13
theorem s15 : LateralTheory.E.LeafOneSpecPf.LeafPrimCover := @_root_.LateralTheory.E.LeafPrimCoverPf.leafPrimCover_pf
theorem s16 : LateralTheory.E.CupProductRingLaws.LeafOneSpec := @_root_.LateralTheory.E.LeafOneSpecPf.LeafOneSpec_of s14 s15
theorem s17 : LateralTheory.E.LeafUnitActPf.LeafActSheaf := @_root_.LateralTheory.E.LeafActSheafPf.LeafActSheaf_of
theorem s18 : LateralTheory.E.LeafUnitPairGPf.LeafUnitAct := @_root_.LateralTheory.E.LeafUnitActPf.LeafUnitAct_of s17
theorem s19 : LateralTheory.E.LeafPairExtPf2.LeafTensUP := @_root_.LateralTheory.E.LeafTensUPPf.etale_tensor_pairing_universal_property_holds
theorem s20 : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocGen := @_root_.LateralTheory.E.LeafTw0LocGenPf.LeafTw0LocGen_of
theorem s21 : LateralTheory.E.LeafTw0LocSplitPfM.LeafTw0TwFree := @_root_.LateralTheory.E.LeafTw0TwFreePf.LeafTw0TwFree_of
theorem s22 : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0GenFree := @_root_.LateralTheory.E.LeafTw0LocSplitPfM.LeafTw0GenFree_of s21
theorem s23 : LateralTheory.E.LeafTensMonoPf.LeafTw0LocSplit := @_root_.LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocSplit_of s20 s22
theorem s24 : LateralTheory.E.LeafTensMonoPf.LeafPreTensLocInj := @_root_.LateralTheory.E.LeafPreTensLocInjPf.LeafPreTensLocInj_of s23
theorem s25 : LateralTheory.E.LeafExtTensPf.LeafTensMono := @_root_.LateralTheory.E.LeafTensMonoPf.LeafTensMono_of s24
theorem s26 : LateralTheory.E.LeafTensQIsoPf.LeafTensQIsoGen := @_root_.LateralTheory.E.LeafTensQIsoGenPf.LeafTensQIsoGen_of
theorem s27 : LateralTheory.E.LeafTensQIsoPf.LeafSecInj := @_root_.LateralTheory.E.LeafSecInjPf.LeafSecInj_of
theorem s28 : LateralTheory.E.LeafTensQIsoPf.LeafZModInjFlat := @_root_.LateralTheory.E.LeafZModInjFlatPf.LeafZModInjFlat_of
theorem s29 : LateralTheory.E.LeafExtTensPf.LeafTensQIso := @_root_.LateralTheory.E.LeafTensQIsoPf.LeafTensQIso_of s26 s27 s28
theorem s30 : LateralTheory.E.LeafPairExtPf2.LeafExtTens := @_root_.LateralTheory.E.LeafExtTensPf.LeafExtTens_of s25 s29
theorem s31 : LateralTheory.E.LeafPairExtPf.LeafExtAlongAug := @_root_.LateralTheory.E.LeafPairExtPf2.LeafExtAlongAug_of s19 s30
theorem s32 : LateralTheory.E.LeafUnitPairGPf.LeafPairExt := @_root_.LateralTheory.E.LeafPairExtPf.LeafPairExt_of' s31
theorem s33 : LateralTheory.E.LeafUnitPairPf.LeafUnitPairG := @_root_.LateralTheory.E.LeafUnitPairGPf.LeafUnitPairG_of s18 s32
theorem s34 : LateralTheory.E.LeafRingUnitPf.LeafUnitPair := @_root_.LateralTheory.E.LeafUnitPairPf.LeafUnitPair_of s33
theorem s35 : LateralTheory.E.LeafOneLocPf.LeafPrimLoc := @_root_.LateralTheory.E.PrimitiveRootLocalization.LeafPrimLoc_of
theorem s36 : LateralTheory.E.LeafRingUnitPf.LeafOneLoc := @_root_.LateralTheory.E.LeafOneLocPf.LeafOneLoc_of s35
theorem s37 : LateralTheory.E.LeafRingUnitPf.LeafUnitAW := @_root_.LateralTheory.E.LeafUnitAWPf.LeafUnitAW_of
theorem s38 : LateralTheory.E.CupProductRingLaws.LeafRingUnit := @_root_.LateralTheory.E.LeafRingUnitPf.LeafRingUnit_of s1 s2 s12 s16 s34 s36 s37
theorem s39 : LateralTheory.E.CupProductRingLaws.LeafRingAssoc := @_root_.LateralTheory.Fix.CupProductTensor.ringAssoc
theorem s40 : LateralTheory.E.CupProductRingLaws.LeafRingComm := @_root_.LateralTheory.E.RingCommutativity.goal_of
theorem s41 : LateralTheory.E.D2.LeafA6ring := @_root_.LateralTheory.E.LeafA6ringCut.goal_of s38 s39 s40
theorem s42 : LateralTheory.E.D2.LeafRing := @_root_.LateralTheory.E.D2.LeafRing_of s0 s41
theorem s43 : LateralTheory.E.D2.LeafChern := @_root_.LateralTheory.E.D2.LeafChern_of
theorem s44 : LateralTheory.E.D2.LeafNat := @_root_.LateralTheory.E.D2.LeafNat_of s0
theorem s45 : LateralTheory.E.LeafGeomPf.LeafHalf1 := @_root_.LateralTheory.E.LeafHalf1Pf.LeafHalf1_of
theorem s46 : LateralTheory.E.HalfDegreeVanishing.LeafMapW := @_root_.LateralTheory.E.LeafMapWPf.LeafMapW_of
theorem s47 : LateralTheory.E.LeafGeomPf.LeafHalf2 := @_root_.LateralTheory.E.HalfDegreeVanishing.LeafHalf2_of s46
theorem s48 : LateralTheory.E.D2.LeafGeom := @_root_.LateralTheory.E.LeafGeomPfLoc.LeafGeom_of s45 s47
theorem s49 : LateralTheory.E.D2.LeafCover2 := @_root_.LateralTheory.E.LeafCover2Pf.LeafCover2_of
theorem s50 : LateralTheory.E.LeafA6suppPf.LeafAWSpec := awSpec
theorem s51 : LateralTheory.E.LeafA6suppPf.LeafRepVanish := @_root_.LateralTheory.E.LeafRepVanishPf.LeafRepVanish_of
theorem s52 : LateralTheory.E.LeafA6suppPf.LeafCochainVanish := @_root_.LateralTheory.E.LeafA6suppPf.LeafCochainVanish_of
theorem s53 : LateralTheory.E.D2.LeafA6supp := @_root_.LateralTheory.E.LeafA6suppPf.LeafA6supp_of s50 s51 s52
theorem s54 : LateralTheory.E.D2.LeafWhitney := @_root_.LateralTheory.E.D2.LeafWhitney_of s48 s49 s53 s0
theorem s55 : LateralTheory.E.D2.LeafLine := @_root_.LateralTheory.E.D2.LeafLine_of s0
theorem s56 : LateralTheory.E.D2.LeafNewton := @_root_.LateralTheory.E.LeafNewtonPf.LeafNewton_of
theorem s57 : LateralTheory.E.EtaleChapterDTwo := @_root_.LateralTheory.E.D2.goal_of s42 s43 s44 s54 s55 s56

theorem intersectionNumber_baseChange : LateralTheory.E.EtaleChapterDTwo := s57

end LateralTheory.Fix.EtaleChapterDTwo
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DiagramDescent
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf

namespace LateralTheory.E.DiagramDescent

theorem descendFP_of (hA : LateralTheory.E.LeafObjFPPf.LeafObjAff) (hG : LateralTheory.E.LeafObjGluePf.LeafGlueTwo)
    (hQ : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct) (hI : LateralTheory.E.LeafInclDescendPf.LeafInclPiece)
    (hL : LateralTheory.E.LeafMapFPPf.LeafLimFP) (hF : LateralTheory.E.LeafPairRelPf.LeafFactorStage) : LeafDescendFP := by
  have hO : LeafObjFP := LateralTheory.E.LeafObjFPPf.objectDescent_of_affineDescent hA
    (LateralTheory.E.LeafObjGluePf.LeafObjGlue_of (LateralTheory.E.LeafInclDescendPf.LeafInclDescend_of hI) hG) hQ
  exact diagramDescent_of_objects_pairs_triples hO (LateralTheory.E.LeafPairFPPf.pairDescent_of_objects_morphisms hO (LateralTheory.E.LeafMapFPPf2.morphismDescent_of_isLimit hL))
    (LateralTheory.E.LeafTripleFPPf.tripleDescent_of_pairRelation (LateralTheory.E.LeafPairRelPf.LeafPairRel_of hO hF))

theorem fp_snd {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (hf : FP f) : FP (pullback.snd f g) := by
  obtain ⟨h1, h2, h3⟩ := hf
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem cond {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R')
    {C D : Scheme.{0}} {g : D ⟶ Sp R} {v : C ⟶ D} {c : C ⟶ Sp Ω} (h : IsPullback v c g (toR R)) :
    v ≫ g = (c ≫ toR R') ≫ incl hR := by
  rw [Category.assoc, LateralTheory.E.LeafDescendMapPf.toR_incl]; exact h.w

theorem sq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R')
    {C D : Scheme.{0}} {g : D ⟶ Sp R} {v : C ⟶ D} {c : C ⟶ Sp Ω} (h : IsPullback v c g (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR R') (cond hR h)) c (pullback.snd g (incl hR)) (toR R') := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback g (incl hR))
  rw [pullback.lift_fst, LateralTheory.E.LeafDescendMapPf.toR_incl]; exact h

theorem LeafDescendPreMap_of (hA : LateralTheory.E.LeafObjFPPf.LeafObjAff) (hG : LateralTheory.E.LeafObjGluePf.LeafGlueTwo)
    (hQ : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct) (hI : LateralTheory.E.LeafInclDescendPf.LeafInclPiece)
    (hL : LateralTheory.E.LeafMapFPPf.LeafLimFP) (hF : LateralTheory.E.LeafPairRelPf.LeafFactorStage) :
    LateralTheory.E.QuasiFiniteDescent.LeafDescendPreMap := by
  intro k _ X p _ Ω _ _ C0 c0 e hc0 he C1 C2 γ1 γ2 h1 h2
  obtain ⟨R, hRfg, D0, D1, D2, q, d1, d2, v0, v1, v2, hpre⟩ :=
    descendFP_of hA hG hQ hI hL hF k Ω c0 hc0 C1 C2 γ1 γ2 h1 h2
  obtain ⟨hq0, hq1, hq2, p0, p1, p2, m1, m2⟩ := hpre
  have : LocallyOfFinitePresentation p := LateralTheory.E.LeafDescendMapPf.lfp p
  let bk := Spec.map (CommRingCat.ofHom (algebraMap k R))
  have hlfp : LocallyOfFinitePresentation (pullback.snd p bk) := inferInstance
  have ha : e ≫ p = (c0 ≫ toR R) ≫ bk := by
    rw [he, Category.assoc, LateralTheory.E.LeafDescendMapPf.toR_base]
  obtain ⟨R', h, hR'fg, g, hg1, hg2⟩ := hF k Ω R hRfg c0 q v0 hq0 p0 (pullback.snd p bk) hlfp
    (pullback.lift e (c0 ≫ toR R) ha) (pullback.lift_snd _ _ _)
  let e1 : pullback (d1 ≫ q) (incl h) ⟶ pullback q (incl h) :=
    pullback.map _ _ _ _ d1 (𝟙 _) (𝟙 _) (by simp) (by simp)
  let e2 : pullback (d2 ≫ d1 ≫ q) (incl h) ⟶ pullback (d1 ≫ q) (incl h) :=
    pullback.map _ _ _ _ d2 (𝟙 _) (𝟙 _) (by simp) (by simp)
  have E1 : e1 ≫ pullback.snd q (incl h) = pullback.snd (d1 ≫ q) (incl h) := by
    simp only [e1, pullback.map, pullback.lift_snd, Category.comp_id]
  have E2 : e2 ≫ e1 ≫ pullback.snd q (incl h) = pullback.snd (d2 ≫ d1 ≫ q) (incl h) := by
    rw [E1]; simp only [e2, pullback.map, pullback.lift_snd, Category.comp_id]
  refine ⟨R', hR'fg, _, _, _, pullback.snd q (incl h), e1, e2, g ≫ pullback.fst p bk,
    pullback.lift v0 (c0 ≫ toR R') (cond h p0), pullback.lift v1 ((γ1 ≫ c0) ≫ toR R') (cond h p1),
    pullback.lift v2 ((γ2 ≫ γ1 ≫ c0) ≫ toR R') (cond h p2), ?_, ⟨fp_snd _ _ hq0, ?_, ?_, sq h p0, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hg1, Category.assoc,
      LateralTheory.E.LeafDescendMapPf.incl_base]
  · rw [E1]; exact fp_snd _ _ hq1
  · rw [E2]; exact fp_snd _ _ hq2
  · rw [E1]; exact sq h p1
  · rw [E2]; exact sq h p2
  · apply pullback.hom_ext
    · simp only [e1, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact m1
    · simp only [e1, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id]
  · apply pullback.hom_ext
    · simp only [e2, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]; exact m2
    · simp only [e2, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id]
  · rw [← Category.assoc, hg2, pullback.lift_fst]

end LateralTheory.E.DiagramDescent

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafClosedImmSpreadPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafSpreadSeparatedPf

namespace LateralTheory.E.LeafClosedImmSpreadPf

theorem bc_sq {X Y Z T : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (t : T ⟶ Z) :
    IsPullback (pullback.fst (f ≫ g) t) (BC f g (f ≫ g) rfl t) f (pullback.fst g t) := by
  have e : BC f g (f ≫ g) rfl t ≫ pullback.snd g t = pullback.snd (f ≫ g) t := by
    simp only [BC, pullback.map, pullback.lift_snd, Category.comp_id]
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback g t)
  · rw [e]; exact IsPullback.of_hasPullback (f ≫ g) t
  · simp only [BC, pullback.map, pullback.lift_fst]

theorem toR_eq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) :
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap R.toSubring.subtype : Sp Ω ⟶ Sp R) = toR R := rfl

theorem incl_eq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R S : Subalgebra k Ω} (h : R ≤ S)
    (h' : R.toSubring ≤ S.toSubring) :
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Subring.inclusion h') : Sp S ⟶ Sp R) = incl h := rfl

theorem LeafClosedImmSpread_of : LeafClosedImmSpread := by
  intro k _ Ω _ _ R hR X Y f g hg hfg hci
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hp1, hp2, hp3⟩ := hfg
  have := hg1; have := hg2; have := hg3; have := hp1; have := hp2; have := hp3
  have : QuasiSeparated f := QuasiSeparated.of_comp f g
  have : QuasiCompact f := QuasiCompact.of_comp f g
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f g
  have hY : IsPullback (pullback.fst g (toR R)) (pullback.snd g (toR R)) (g : Y ⟶ Sp R.toSubring)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap R.toSubring.subtype) := by
    rw [toR_eq]; exact IsPullback.of_hasPullback g (toR R)
  have : QuasiCompact (g : Y ⟶ Sp R.toSubring) := hg2
  obtain ⟨F, hF⟩ := GlobalTheory.isClosedImmersion_descends_to_subring Ω R.toSubring X Y _ _ f g
    (BC f g (f ≫ g) rfl (toR R)) (pullback.fst _ _) (pullback.fst _ _) (pullback.snd _ _) hY (bc_sq f g _) hci
  let S : Subalgebra k Ω := R ⊔ Algebra.adjoin k (F : Set Ω)
  have h : R ≤ S := le_sup_left
  have h' : R.toSubring ≤ S.toSubring := fun x hx => h hx
  have hsub : (F : Set Ω) ⊆ S.toSubring := fun x hx =>
    (le_sup_right : Algebra.adjoin k (F : Set Ω) ≤ S) (Algebra.subset_adjoin hx)
  refine ⟨S, h, hR.sup (Subalgebra.fg_adjoin_finset F), ?_⟩
  have hY1 : IsPullback (pullback.fst g (incl h)) (pullback.snd g (incl h)) (g : Y ⟶ Sp R.toSubring)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Subring.inclusion h')) := by
    rw [incl_eq h h']; exact IsPullback.of_hasPullback g (incl h)
  exact hF S.toSubring h' hsub _ _ (BC f g (f ≫ g) rfl (incl h)) (pullback.fst _ _) (pullback.fst _ _)
    (pullback.snd _ _) hY1 (bc_sq f g _)

end LateralTheory.E.LeafClosedImmSpreadPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafResDimQePf
section
noncomputable section
namespace LateralTheory.E.LeafResDimQePf
open LateralTheory.E.LeafCoordsPointResPf
open scoped TensorProduct

theorem LeafResDimQe_of : LeafResDimQe := by
  intro d e A B _ _ _ I hB hBI P _ hIP
  set K := P.ResidueField
  have hI : ∀ a ∈ I, algebraMap B K a = 0 := fun a ha => by
    rw [Ideal.algebraMap_residueField_eq_zero]; exact hIP ha
  letI : Algebra (B ⧸ I) K := (Ideal.Quotient.lift I (algebraMap B K) hI).toAlgebra
  have : IsScalarTower B (B ⧸ I) K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (fun h => Ideal.IsPrime.ne_top ‹P.IsPrime› (eq_top_iff.mpr (h ▸ hIP)))
  have := hBI
  have := hBI.isStandardSmooth
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := A) (S := B ⧸ I) e
  have hf : Module.finrank (B ⧸ I) Ω[(B ⧸ I)⁄A] = e := Module.finrank_eq_of_rank_eq hr
  have : TensorProduct.CompatibleSMul B (B ⧸ I) K Ω[(B ⧸ I)⁄A] := ⟨fun r m n => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective r
    have h1 : (Ideal.Quotient.mk I b) • m = b • m := (algebraMap_smul (B ⧸ I) b m)
    have h2 : (Ideal.Quotient.mk I b) • n = b • n := (algebraMap_smul (B ⧸ I) b n)
    rw [h1, h2, TensorProduct.smul_tmul]⟩
  rw [← (TensorProduct.equivOfCompatibleSMul B (B ⧸ I) K K Ω[(B ⧸ I)⁄A]).finrank_eq,
    Module.finrank_baseChange, hf]

end LateralTheory.E.LeafResDimQePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafResKerPf
section
noncomputable section
namespace LateralTheory.E.LeafCoordsPointResPf
open LateralTheory.E.LeafCoordsPf LateralTheory.E.LeafCoordsPointPf
open scoped TensorProduct

theorem LeafResKer_of : LeafResKer := by
  intro d e A B _ _ _ I _ _ P _ hIP
  set K := P.ResidueField
  set C := B ⧸ I
  set S : Submodule K (K ⊗[B] Ω[B⁄A]) := Submodule.span K (Set.range fun x : I =>
      (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (x : B))
  let g : Ω[B⁄A] →ₗ[B] Ω[C⁄A] := (KaehlerDifferential.map A A B C).restrictScalars B
  have hI : ∀ a ∈ I, (Algebra.ofId B K) a = 0 := fun a ha => by
    simp only [Algebra.ofId_apply]
    exact (Ideal.algebraMap_residueField_eq_zero).mpr (hIP ha)
  let φ : C →ₗ[B] K := (Ideal.Quotient.liftₐ I (Algebra.ofId B K) hI).toLinearMap
  have hφ1 : φ 1 = 1 := by simp [φ]

  have h2 : ∀ ω : Ω[B⁄A], g ω = 0 → (1 : K) ⊗ₜ[B] ω ∈ S := by
    intro ω hω
    have hm : KaehlerDifferential.mapBaseChange A B C ((1 : C) ⊗ₜ[B] ω) = 0 := by
      rw [KaehlerDifferential.mapBaseChange_tmul, one_smul]; exact hω
    obtain ⟨y, hy⟩ := (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange A B C
      Ideal.Quotient.mk_surjective ((1 : C) ⊗ₜ[B] ω)).mp hm
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ y
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent] at hy
    have hx : (x : B) ∈ I := by
      have := x.2; rw [RingHom.mem_ker] at this; exact Ideal.Quotient.eq_zero_iff_mem.mp this
    have := congrArg (LinearMap.rTensor (Ω[B⁄A]) φ) hy
    simp only [LinearMap.rTensor_tmul, hφ1] at this
    rw [← this]
    exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
  have hex := lTensor_exact K (LinearMap.exact_subtype_ker_map g)
    (KaehlerDifferential.map_surjective_of_surjective A A B C Ideal.Quotient.mk_surjective)
  intro z hz
  rw [LinearMap.mem_ker] at hz
  have hz' : LinearMap.lTensor K g z = 0 := by
    rw [← hz, nu]; rfl
  obtain ⟨w, rfl⟩ := (hex z).mp hz'
  clear hz hz'
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul k n =>
    rw [LinearMap.lTensor_tmul]
    have : k ⊗ₜ[B] ((LinearMap.ker g).subtype n) = k • ((1 : K) ⊗ₜ[B] (n : Ω[B⁄A])) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl
    rw [this]
    exact S.smul_mem k (h2 n n.2)
  | add a b ha hb => rw [map_add]; exact S.add_mem ha hb

end LateralTheory.E.LeafCoordsPointResPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.QuasiFiniteAtOfIsOpenFiber
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.QuasiFiniteAtDescent

theorem quasiFiniteAt_of_isOpen_fiber {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (y : Y) (z : f.fiber y) (a : X) (hza : f.fiberι y z = a) (hz : IsOpen ({z} : Set (f.fiber y))) :
    f.QuasiFiniteAt a := by
  have hy : y = f a := by
    rw [← hza, ← Scheme.Hom.comp_apply, Scheme.Hom.fiber_fac, Scheme.Hom.comp_apply]
    simp
  subst hy
  have : z = f.asFiber a := by
    apply (f.fiberι (f a)).isEmbedding.injective
    rw [hza, Scheme.Hom.fiberι_asFiber]
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← this]
  exact hz

theorem qf_of_fiberMap {CA CB A B : Scheme.{0}} (γ : CA ⟶ CB) (g : A ⟶ B) (vA : CA ⟶ A) (vB : CB ⟶ B)
    [LocallyOfFiniteType g] [LocallyOfFiniteType γ] (x : CA)
    (φ : γ.fiber (γ x) ⟶ g.fiber (vB (γ x))) (hφ : UniversallyOpen φ)
    (e : φ ≫ g.fiberι (vB (γ x)) = γ.fiberι (γ x) ≫ vA) (hx : γ.QuasiFiniteAt x) :
    g.QuasiFiniteAt (vA x) := by
  have hx' : IsOpen ({γ.asFiber x} : Set (γ.fiber (γ x))) :=
    Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hx
  have hopen := φ.isOpenMap _ hx'
  have h2 : IsOpen ({φ (γ.asFiber x)} : Set (g.fiber (vB (γ x)))) := by
    convert hopen using 1
    exact (Set.image_singleton).symm
  refine quasiFiniteAt_of_isOpen_fiber g (vB (γ x)) (φ (γ.asFiber x)) (vA x) ?_ h2
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber]

theorem LeafQFAtDescend_of : LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafQFAtDescend := by
  intro CA CB A B γ g vA vB sq hg x hx
  have : LocallyOfFiniteType γ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq hg
  have sqF := isPullback_fiberToSpecResidueField_of_isPullback sq (γ x)
  have hφ := MorphismProperty.of_isPullback (P := @UniversallyOpen) sqF.flip inferInstance
  refine qf_of_fiberMap γ g vA vB x _ hφ ?_ hx
  exact pullback.lift_fst _ _ _

end LateralTheory.E.QuasiFiniteAtDescent
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StalkContPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf LateralTheory.E.StalkGermPf GlobalTheory.StalkLimit

namespace LateralTheory.E.StalkContPf

set_option backward.isDefEq.respectTransparency false

variable {X S : Scheme.{0}}

theorem diagram_map_eq (p : X ⟶ S) (s : S) {V W : AffNhd s} (i : V ⟶ W) :
    (diagram s p).map i = resO p i.le := by
  apply pullback.hom_ext <;> simp [diagram, resO]

theorem cone_app_eq (p : X ⟶ S) (s : S) (V : AffNhd s) :
    (cone (IsPullback.of_hasPullback p (S.fromSpecStalk s))).π.app V = toO p s V.1 V.2.1 := by
  apply pullback.hom_ext <;> simp [cone, toO]

theorem pull_cone {q : ℕ} {n i : ℤ} (p : X ⟶ S) (s : S) (V : AffNhd s) (y : Ht q (sch.obj (overO p V.1)) n i) :
    pull _ (sch.map ((cone (IsPullback.of_hasPullback p (S.fromSpecStalk s))).π.app V)) (tw q i) n y =
      pull _ (sch.map (toO p s V.1 V.2.1)) (tw q i) n y := by
  rw [cone_app_eq]; rfl

theorem pull_diag {q : ℕ} {n i : ℤ} (p : X ⟶ S) (s : S) {V W : AffNhd s} (f : V ⟶ W)
    (y : Ht q (sch.obj (overO p W.1)) n i) :
    pull _ (sch.map ((diagram s p).map f)) (tw q i) n y = pull _ (sch.map (resO p f.le)) (tw q i) n y := by
  rw [diagram_map_eq]; rfl

theorem exists_aff (s : S) (U : S.Opens) (hs : s ∈ U) : ∃ V : AffNhd s, V.1 ≤ U := by
  obtain ⟨W, h₁, h₂, h₃⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hs
  exact ⟨⟨W, h₂, h₁⟩, h₃⟩

theorem StalkCont_of : StalkCont := by
  intro hC hH q X S p _ _ _ _ hq i n s
  have hc := (nonempty_isLimit (IsPullback.of_hasPullback p (S.fromSpecStalk s))).some
  have hcpt : ∀ V : AffNhd s, CompactSpace ((diagram s p).obj V) := fun V => by
    have : IsAffine V.1.toScheme := V.2.2
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V.1.ι)
  have hqs : ∀ V : AffNhd s, QuasiSeparatedSpace ((diagram s p).obj V) := fun V => by
    have : IsAffine V.1.toScheme := V.2.2
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V.1.ι)
  have hu : ∀ V : AffNhd s, IsUnit (q : Γ((diagram s p).obj V, ⊤)) := fun V => by
    have := hq.map ((pullback.fst p V.1.ι ≫ p).appTop).hom
    simp only [map_natCast] at this
    exact this
  obtain ⟨hsurj, hkill⟩ := hC hH q (diagram s p) _ hc (fun f => inferInstance) hcpt hqs hu n i
  constructor
  · intro U hs x hx
    obtain ⟨V0, hV0⟩ := exists_aff s U hs
    have h0 : pull _ (sch.map ((cone (IsPullback.of_hasPullback p (S.fromSpecStalk s))).π.app V0)) _ _
        (pull _ (sch.map (resO p hV0)) _ _ x) = 0 := by
      rw [pull_cone, ← pull_mc, toO_res]; exact hx
    obtain ⟨k, f, hf⟩ := hkill V0 _ h0
    have hkV : k.1 ≤ V0.1 := f.le
    refine ⟨k.1, hkV.trans hV0, k.2.1, ?_⟩
    rw [pull_diag, ← pull_mc, res_res] at hf
    exact hf
  · intro z
    obtain ⟨j, y, hy⟩ := hsurj z
    exact ⟨j.1, j.2.1, y, (pull_cone p s j y).symm.trans hy⟩

end LateralTheory.E.StalkContPf
end
end

