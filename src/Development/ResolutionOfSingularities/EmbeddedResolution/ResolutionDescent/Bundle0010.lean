import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Bundle0001
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0002
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InducedBlowupsFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.FieldExtensionEtaleCover
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0008
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartPushforward
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedLocusPushforward
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0005
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrictTransformTower
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0009
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ClosedEmbeddingIntoAffineSpace
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleLocality
section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem principalizationAlgorithm_toSequenceOfBlowups_congr_ideal (A : PrincipalizationAlgorithm.{u}) (k : Type u) [Field k] [CharZero k]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I J : X.IdealSheafData) (hIJ : I = J)
    (hI : NonzeroOnComponents I) (hJ : NonzeroOnComponents J)
    (E : List X.IdealSheafData) (hE hE' : InStrictNormalCrossingPosition p E) :
    (A k X p I hI E hE).toSequenceOfBlowups = (A k X p J hJ E hE').toSequenceOfBlowups := by
  subst hIJ
  rfl

private theorem isPullbackSequenceOfBlowups_congr_left {X X' : Scheme.{u}} {φ : X' ⟶ X}
    {s1 s2 : SequenceOfBlowups X'} {t : SequenceOfBlowups X} (h : s1 = s2) (H : IsPullbackBlowupSequence φ s1 t) :
    IsPullbackBlowupSequence φ s2 t := by
  subst h
  exact H

theorem embeddedResolutionRule_isPullbackBlowupSequence_of_smooth
    (A : PrincipalizationAlgorithm.{u}) (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (k : Type u) [Field k] [CharZero k] (Y Y' : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) (p' : Y' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType p'] [AlgebraicGeometry.QuasiCompact p']
    [AlgebraicGeometry.IsReduced Y'] [AlgebraicGeometry.IsAffine Y']
    (D : EmbeddingDatum k Y p) (D' : EmbeddingDatum k Y' p')
    (φ : D'.ambient ⟶ D.ambient) [AlgebraicGeometry.Smooth φ] (ψ : Y' ⟶ Y)
    (hφ : φ ≫ D.ambientStruct = D'.ambientStruct)
    (hsq : IsPullback D'.emb ψ φ D.emb) :
    IsPullbackBlowupSequence ψ (embeddedResolutionRuleOfPrincipalization A hw k Y' p' D')
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D) := by
  have : AlgebraicGeometry.Flat φ := inferInstance
  have : AlgebraicGeometry.QuasiCompact D.emb := inferInstance
  have : AlgebraicGeometry.QuasiCompact D'.emb := inferInstance
  have hker : D'.emb.ker = D.emb.ker.comap φ :=
    ker_eq_comap_ker_of_isPullback_of_flat hsq.flip
  have hI' : NonzeroOnComponents (D.emb.ker.comap φ) := hker ▸ D'.nonzeroOnComponents_ker
  have hE' : InStrictNormalCrossingPosition D'.ambientStruct
      (List.map (fun Z => Z.comap φ) ([] : List D.ambient.IdealSheafData)) := D'.sncEmpty
  have h0 := hA.smooth_pullback k D.ambient D.ambientStruct D.emb.ker
      D.nonzeroOnComponents_ker [] D.sncEmpty D'.ambient D'.ambientStruct φ hφ hI' hE'
  have hpb : IsPullbackBlowupSequence φ (D'.toEmbeddedBlowupSequence A).ambientSeq (D.toEmbeddedBlowupSequence A).ambientSeq := by
    rw [EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups, EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups]
    exact isPullbackSequenceOfBlowups_congr_left
      (principalizationAlgorithm_toSequenceOfBlowups_congr_ideal A k D'.ambient D'.ambientStruct
        (D.emb.ker.comap φ) D'.emb.ker hker.symm hI' _ [] hE' _) h0
  have hflat2 : AlgebraicGeometry.Flat
      (show (D'.toEmbeddedBlowupSequence A).ambient ⟶ (D.toEmbeddedBlowupSequence A).ambient from φ) :=
    (inferInstance : AlgebraicGeometry.Flat φ)
  rw [embeddedResolutionRuleOfPrincipalization_apply, embeddedResolutionRuleOfPrincipalization_apply]
  exact (chartFlatBaseChangeOfIsPullbackSeq (D.toEmbeddedBlowupSequence A) (D'.toEmbeddedBlowupSequence A) φ ψ
    hsq.flip hpb).isPullbackBlowupSequence_inducedBlowupsWithoutIso _ _

theorem embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps
    (A : PrincipalizationAlgorithm.{u}) (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A) :
    EmbeddedResolutionRule.IsCompatibleWithSmoothAmbientMaps (embeddedResolutionRuleOfPrincipalization A hw) := by
  intro k _ _ Y Y' p p' _ _ _ _ _ _ _ _ D D' φ _ ψ hφ hsq
  exact embeddedResolutionRule_isPullbackBlowupSequence_of_smooth A hA hw k Y Y' p p' D D' φ ψ hφ hsq

theorem embeddedResolutionRule_isStrictPullbackBlowupSeq_baseChange
    (A : PrincipalizationAlgorithm.{u}) (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    (D : EmbeddingDatum k Y p) (K : Type u) [Field K] [CharZero K] [Algebra k K]
    [AlgebraicGeometry.IsReduced (baseChange p K)]
    (hker : NonzeroOnComponents (D.baseChangeEmb K).ker)
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec D.ambientStruct K)
      ([] : List (baseChange D.ambientStruct K).IdealSheafData)) :
    haveI : AlgebraicGeometry.IsAffine (baseChange p K) := isAffine_baseChange p K
    haveI : AlgebraicGeometry.LocallyOfFiniteType (baseChangeToSpec p K) :=
      locallyOfFiniteType_baseChangeToSpec p K
    haveI : AlgebraicGeometry.QuasiCompact (baseChangeToSpec p K) :=
      quasiCompact_baseChangeToSpec p K
    IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (embeddedResolutionRuleOfPrincipalization A hw K (baseChange p K) (baseChangeToSpec p K)
        (D.baseChange K hker hsnc))
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D) := by
  have : AlgebraicGeometry.IsAffine (baseChange p K) := isAffine_baseChange p K
  have : AlgebraicGeometry.LocallyOfFiniteType (baseChangeToSpec p K) :=
    locallyOfFiniteType_baseChangeToSpec p K
  have : AlgebraicGeometry.QuasiCompact (baseChangeToSpec p K) :=
    quasiCompact_baseChangeToSpec p K
  have : AlgebraicGeometry.IsAffine (baseChange D.ambientStruct K) :=
    EmbeddingDatum.isAffine_baseChange_ambientToSpec D K
  have : AlgebraicGeometry.Smooth (baseChangeToSpec D.ambientStruct K) :=
    EmbeddingDatum.smooth_baseChangeToSpec_ambientToSpec D K
  have : AlgebraicGeometry.LocallyOfFiniteType (baseChangeToSpec D.ambientStruct K) :=
    EmbeddingDatum.locallyOfFiniteType_baseChangeToSpec_ambientToSpec D K
  have : AlgebraicGeometry.QuasiCompact (baseChangeToSpec D.ambientStruct K) :=
    EmbeddingDatum.quasiCompact_baseChangeToSpec_ambientToSpec D K
  have : AlgebraicGeometry.Flat (baseChangeProjection D.ambientStruct K) := inferInstance
  have : AlgebraicGeometry.Surjective (baseChangeProjection p K) := inferInstance
  have : AlgebraicGeometry.QuasiCompact D.emb := inferInstance
  have : AlgebraicGeometry.QuasiCompact (D.baseChangeEmb K) := inferInstance
  show IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (embeddedResolutionRuleOfPrincipalization A hw K (baseChange p K) (baseChangeToSpec p K)
        (D.baseChange K hker hsnc))
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D)
  have hkerbc : (D.baseChangeEmb K).ker
      = D.emb.ker.comap (baseChangeProjection D.ambientStruct K) :=
    ker_eq_comap_ker_of_isPullback_of_flat (D.isPullback_baseChangeEmb K).flip
  have hI' : NonzeroOnComponents (D.emb.ker.comap (baseChangeProjection D.ambientStruct K)) :=
    hkerbc ▸ hker
  have hE' : InStrictNormalCrossingPosition (baseChangeToSpec D.ambientStruct K)
      (List.map (fun Z => Z.comap (baseChangeProjection D.ambientStruct K))
        ([] : List D.ambient.IdealSheafData)) := hsnc
  have h0 := hA.base_change k D.ambient D.ambientStruct D.emb.ker D.nonzeroOnComponents_ker
      [] D.sncEmpty K (algebraMap k K) hI' hE'
  have hpb : IsPullbackBlowupSequence (baseChangeProjection D.ambientStruct K)
      ((D.baseChange K hker hsnc).toEmbeddedBlowupSequence A).ambientSeq
      (D.toEmbeddedBlowupSequence A).ambientSeq := by
    rw [EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups, EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups]
    exact isPullbackSequenceOfBlowups_congr_left
      (principalizationAlgorithm_toSequenceOfBlowups_congr_ideal A K (baseChange D.ambientStruct K)
        (baseChangeToSpec D.ambientStruct K)
        (D.emb.ker.comap (baseChangeProjection D.ambientStruct K)) (D.baseChangeEmb K).ker
        hkerbc.symm hI' _ [] hE' _) h0
  have hflat2 : AlgebraicGeometry.Flat
      (show ((D.baseChange K hker hsnc).toEmbeddedBlowupSequence A).ambient ⟶
          (D.toEmbeddedBlowupSequence A).ambient from baseChangeProjection D.ambientStruct K) :=
    (inferInstance : AlgebraicGeometry.Flat (baseChangeProjection D.ambientStruct K))
  rw [embeddedResolutionRuleOfPrincipalization_apply, embeddedResolutionRuleOfPrincipalization_apply]
  refine IsPullbackBlowupSequence.isStrictPullback_of_surjective ?_ ?_
  · exact (chartFlatBaseChangeOfIsPullbackSeq (D.toEmbeddedBlowupSequence A)
      ((D.baseChange K hker hsnc).toEmbeddedBlowupSequence A) (baseChangeProjection D.ambientStruct K)
      (baseChangeProjection p K) (D.isPullback_baseChangeEmb K).flip hpb).isPullbackBlowupSequence_inducedBlowupsWithoutIso _ _
  · intro i hi
    exact SequenceOfBlowups.withoutIsoBlowups_center_ne_top ((D.toEmbeddedBlowupSequence A).inducedBlowups _) hi

theorem embeddedResolutionRule_isCompatibleWithFieldBaseChange
    (A : PrincipalizationAlgorithm.{u}) (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A) :
    EmbeddedResolutionRule.IsCompatibleWithFieldBaseChange (embeddedResolutionRuleOfPrincipalization A hw) := by
  intro k _ _ Y p _ _ _ _ D K _ _ _ _ hker hsnc
  exact embeddedResolutionRule_isStrictPullbackBlowupSeq_baseChange A hA hw k Y p D K hker hsnc

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InactiveTotalSpacePushforward
section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace ChartPushforward

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  {S S' : EmbeddedBlowupSequence k Y pY}

theorem le_length_of_le_length (P : ChartPushforward S S') {i : ℕ} (hi : i ≤ S.length) : i ≤ S'.length := by
  rw [← P.len_eq]
  exact hi

theorem lt_length_of_lt_length (P : ChartPushforward S S') {i : ℕ} (hi : i < S.length) : i < S'.length := by
  rw [← P.len_eq]
  exact hi

private def detachedCoprodIsoOfLE (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] :
    ∀ i : ℕ, i ≤ S'.length → (S.detachedCoprod i ≅ S'.detachedCoprod i) := fun i =>
  Nat.rec (motive := fun n => n ≤ S'.length → (S.detachedCoprod n ≅ S'.detachedCoprod n))
    (fun _ => eqToIso (S.detachedCoprod_zero.trans S'.detachedCoprod_zero.symm))
    (fun n ih hn => coprod.mapIso (ih (Nat.le_of_succ_le hn))
      (P.detachedSchemeIso n (lt_of_lt_of_le (Nat.lt_succ_self n) hn))) i

theorem exists_iso_detachedCoprod_compatible (P : ChartPushforward S S')
    [AlgebraicGeometry.IsReduced Y] :
    ∃ e : ∀ i : ℕ, i ≤ S'.length → (S.detachedCoprod i ≅ S'.detachedCoprod i),
      (∀ h : (0 : ℕ) ≤ S'.length,
          (e 0 h).hom = eqToHom (S.detachedCoprod_zero.trans S'.detachedCoprod_zero.symm)) ∧
      (∀ (i : ℕ) (hi : i < S'.length),
          S.detachedCoprodInl i ≫ (e (i + 1) hi).hom = (e i hi.le).hom ≫ S'.detachedCoprodInl i) ∧
      (∀ (i : ℕ) (hi : i < S'.length),
          S.detachedCoprodInr i ≫ (e (i + 1) hi).hom =
            (P.detachedSchemeIso i hi).hom ≫ S'.detachedCoprodInr i) := by
  refine ⟨detachedCoprodIsoOfLE P, fun _ => rfl, ?_, ?_⟩
  · intro i hi
    show (coprod.inl : S.detachedCoprod i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i) ≫
        coprod.map (detachedCoprodIsoOfLE P i hi.le).hom (P.detachedSchemeIso i hi).hom =
      (detachedCoprodIsoOfLE P i hi.le).hom ≫
        (coprod.inl : S'.detachedCoprod i ⟶ S'.detachedCoprod i ⨿ S'.detachedScheme i)
    simp
  · intro i hi
    show (coprod.inr : S.detachedScheme i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i) ≫
        coprod.map (detachedCoprodIsoOfLE P i hi.le).hom (P.detachedSchemeIso i hi).hom =
      (P.detachedSchemeIso i hi).hom ≫
        (coprod.inr : S'.detachedScheme i ⟶ S'.detachedCoprod i ⨿ S'.detachedScheme i)
    simp

def inactiveTotalIso (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) : S.detachedCoprod i ≅ S'.detachedCoprod i :=
  P.exists_iso_detachedCoprod_compatible.choose i hi

@[reassoc]
theorem detachedCoprodInl_inactiveTotalIso_hom (P : ChartPushforward S S')
    [AlgebraicGeometry.IsReduced Y] (i : ℕ) (hi : i < S'.length) :
    S.detachedCoprodInl i ≫ (P.inactiveTotalIso (i + 1) hi).hom =
      (P.inactiveTotalIso i hi.le).hom ≫ S'.detachedCoprodInl i :=
  P.exists_iso_detachedCoprod_compatible.choose_spec.2.1 i hi

@[reassoc]
theorem detachedCoprodInr_inactiveTotalIso_hom (P : ChartPushforward S S')
    [AlgebraicGeometry.IsReduced Y] (i : ℕ) (hi : i < S'.length) :
    S.detachedCoprodInr i ≫ (P.inactiveTotalIso (i + 1) hi).hom =
      (P.detachedSchemeIso i hi).hom ≫ S'.detachedCoprodInr i :=
  P.exists_iso_detachedCoprod_compatible.choose_spec.2.2 i hi

def totalSpaceIso (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) : S.totalSpace i ≅ S'.totalSpace i :=
  coprod.mapIso (P.strictTransformIso i hi) (P.inactiveTotalIso i hi)

theorem totalSpaceIso_hom_eq_coprodMap (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) :
    (P.totalSpaceIso i hi).hom =
      coprod.map (P.strictTransformIso i hi).hom (P.inactiveTotalIso i hi).hom := rfl

@[reassoc]
theorem inl_totalSpaceIso_hom (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) :
    (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ (P.totalSpaceIso i hi).hom =
      (P.strictTransformIso i hi).hom ≫ (coprod.inl : S'.strictTransform i ⟶ S'.totalSpace i) := by
  rw [P.totalSpaceIso_hom_eq_coprodMap i hi]
  simp

@[reassoc]
theorem inr_totalSpaceIso_hom (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i ≤ S'.length) :
    (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫ (P.totalSpaceIso i hi).hom =
      (P.inactiveTotalIso i hi).hom ≫ (coprod.inr : S'.detachedCoprod i ⟶ S'.totalSpace i) := by
  rw [P.totalSpaceIso_hom_eq_coprodMap i hi]
  simp

private theorem comap_hom_comap_inv {A B : Scheme.{u}} (e : A ≅ B) (I : B.IdealSheafData) :
    (I.comap e.hom).comap e.inv = I := by
  rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]

private theorem comap_inv_comap_hom {A B : Scheme.{u}} (e : A ≅ B) (I : A.IdealSheafData) :
    (I.comap e.inv).comap e.hom = I := by
  rw [← Scheme.IdealSheafData.comap_comp, e.hom_inv_id, Scheme.IdealSheafData.comap_id]

private theorem comap_map_of_comm_iso {A B A' B' : Scheme.{u}} (eA : A ≅ A') (eB : B ≅ B')
    (u : A ⟶ B) (u' : A' ⟶ B') (hcomm : u ≫ eB.hom = eA.hom ≫ u')
    (J : A'.IdealSheafData) :
    (J.map u').comap eB.hom = (J.comap eA.hom).map u := by
  have hcomm' : u' ≫ eB.inv = eA.inv ≫ u := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hcomm, Category.assoc, eB.hom_inv_id,
      Category.comp_id]
  refine le_antisymm ?_ ?_
  · rw [Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.IdealSheafData.comap_comp, hcomm,
      Scheme.IdealSheafData.comap_comp]
    exact Scheme.IdealSheafData.comap_mono _
      (Scheme.IdealSheafData.le_map_iff_comap_le.mp le_rfl)
  · have key : ((J.comap eA.hom).map u).comap eB.inv ≤ J.map u' := by
      rw [Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.IdealSheafData.comap_comp, hcomm',
        Scheme.IdealSheafData.comap_comp]
      have h2 : (((J.comap eA.hom).map u).comap u).comap eA.inv ≤
          (J.comap eA.hom).comap eA.inv :=
        Scheme.IdealSheafData.comap_mono eA.inv
          (Scheme.IdealSheafData.le_map_iff_comap_le.mp
            (le_rfl : (J.comap eA.hom).map u ≤ (J.comap eA.hom).map u))
      rw [comap_hom_comap_inv eA J] at h2
      exact h2
    have h3 : (((J.comap eA.hom).map u).comap eB.inv).comap eB.hom ≤
        (J.map u').comap eB.hom :=
      Scheme.IdealSheafData.comap_mono eB.hom key
    rwa [comap_inv_comap_hom eB] at h3

theorem comap_totalCenter (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y] (i : ℕ)
    (hi : i < S'.length) :
    (S'.totalCenter i).comap (P.totalSpaceIso i hi.le).hom = S.totalCenter i := by
  have h := comap_map_of_comm_iso (P.strictTransformIso i hi.le) (P.totalSpaceIso i hi.le)
      (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)
      (coprod.inl : S'.strictTransform i ⟶ S'.totalSpace i)
      (P.inl_totalSpaceIso_hom i hi.le) (S'.centerOffDetached i)
  rw [P.comap_centerOffDetached i hi] at h
  exact h

private theorem totalSpaceIso_hom_totalTransition (P : ChartPushforward S S')
    [AlgebraicGeometry.IsReduced Y] (i : ℕ) (hi : i < S'.length) :
    (P.totalSpaceIso (i + 1) hi).hom ≫ S'.totalTransition i
      = S.totalTransition i ≫ (P.totalSpaceIso i hi.le).hom := by
  refine coprod.hom_ext ?_ ?_
  · rw [P.inl_totalSpaceIso_hom_assoc (i + 1) hi, S'.inl_totalTransition_eq_strictTransformMap_inl i, S.inl_totalTransition_assoc i,
      P.inl_totalSpaceIso_hom i hi.le]
    exact P.strictTransformIso_hom_comp_strictTransformMap_assoc i hi _
  · refine S.detachedCoprod_succ_hom_ext i ?_ ?_
    · rw [P.inr_totalSpaceIso_hom_assoc (i + 1) hi, P.detachedCoprodInl_inactiveTotalIso_hom_assoc i hi,
        S'.detachedCoprodInl_inr_totalTransition i, S.detachedCoprodInl_inr_totalTransition_assoc i,
        P.inr_totalSpaceIso_hom i hi.le]
    · rw [P.inr_totalSpaceIso_hom_assoc (i + 1) hi, P.detachedCoprodInr_inactiveTotalIso_hom_assoc i hi,
        S'.detachedCoprodInr_inr_totalTransition i, S.detachedCoprodInr_inr_totalTransition_assoc i,
        P.inl_totalSpaceIso_hom i hi.le]
      exact P.detachedSchemeIso_hom_comp_detachedι_assoc i hi _

theorem inducedBlowups_isomorphic (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y]
    (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups) :
    (S.inducedBlowups h).Isomorphic (S'.inducedBlowups h') := by
  refine ⟨P.len_eq, fun i hi => P.totalSpaceIso i (P.le_length_of_le_length hi), ?_, ?_, ?_⟩
  · show (P.totalSpaceIso 0 (Nat.zero_le _)).hom ≫ S'.totalSpaceZeroIso.hom = S.totalSpaceZeroIso.hom
    refine coprod.hom_ext ?_ ?_
    · rw [P.inl_totalSpaceIso_hom_assoc 0 (Nat.zero_le _), S'.inl_totalSpaceZeroIso_hom,
        S.inl_totalSpaceZeroIso_hom]
      exact P.strictTransformIso_zero_hom_comp_strictTransformZeroIso_hom
    · have hB : IsInitial (S.detachedCoprod 0) := initialIsInitial
      exact hB.hom_ext _ _
  · intro i hi
    rw [inducedBlowups_blowupMorphism S' h' i, inducedBlowups_blowupMorphism S h i]
    exact P.totalSpaceIso_hom_totalTransition i (P.lt_length_of_lt_length hi)
  · intro i hi
    exact P.comap_totalCenter i (P.lt_length_of_lt_length hi)

theorem inducedBlowupsWithoutIso_isomorphic (P : ChartPushforward S S') [AlgebraicGeometry.IsReduced Y]
    (h : S.TransitionsAreBlowups) (h' : S'.TransitionsAreBlowups) :
    (S.inducedBlowupsWithoutIso h).Isomorphic (S'.inducedBlowupsWithoutIso h') :=
  (P.inducedBlowups_isomorphic h h').withoutIsoBlowups

end ChartPushforward

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PresentedSelection
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure PresentedSelection where
  sel : EmbeddingChoice.{u}
  pres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y], ClosedEmbeddingIntoAffineSpace (sel k Y p)
  basePres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (K : Type u) [Field K] [CharZero K] [Algebra k K]
    (hker : NonzeroOnComponents (Scheme.Hom.ker ((sel k Y p).baseChangeEmb K)))
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec (sel k Y p).ambientStruct K) []),
    ClosedEmbeddingIntoAffineSpace ((sel k Y p).baseChange K hker hsnc)

theorem isCompatibleWithFieldBaseChange_toAffineResolutionRule (R : EmbeddedResolutionRule.{u})
    (C : PresentedSelection.{u}) (hinv : R.IsIndependentOfPresentedEmbedding)
    (hfield : R.IsCompatibleWithFieldBaseChange)
    (hsnc : ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
      (q : A ⟶ Spec (CommRingCat.of k)), AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q []) :
    IsCompatibleWithFieldBaseChange (R.toAffineResolutionRule C.sel) := by
  intro k _ _ Y p _ _ _ _ K _ _ _ _ _
  have hlft : AlgebraicGeometry.LocallyOfFiniteType (baseChangeToSpec p K) :=
    locallyOfFiniteType_baseChangeToSpec p K
  have hqcb : AlgebraicGeometry.QuasiCompact (baseChangeToSpec p K) :=
    quasiCompact_baseChangeToSpec p K
  have hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (C.sel k Y p).ambientStruct K)
      ([] : List (baseChange (C.sel k Y p).ambientStruct K).IdealSheafData) :=
    hsnc K (baseChange (C.sel k Y p).ambientStruct K)
      (baseChangeToSpec (C.sel k Y p).ambientStruct K)
      (EmbeddingDatum.smooth_baseChangeToSpec_ambientToSpec (C.sel k Y p) K)
  have hsq : IsPullback (baseChangeProjection p K) ((C.sel k Y p).baseChangeEmb K)
      (C.sel k Y p).emb (baseChangeProjection (C.sel k Y p).ambientStruct K) :=
    (EmbeddingDatum.isPullback_baseChangeEmb (C.sel k Y p) K).flip
  have hflat : AlgebraicGeometry.Flat (baseChangeProjection (C.sel k Y p).ambientStruct K) :=
    inferInstance
  have hqc1 : AlgebraicGeometry.QuasiCompact (C.sel k Y p).emb := inferInstance
  have hqc2 : AlgebraicGeometry.QuasiCompact ((C.sel k Y p).baseChangeEmb K) :=
    quasiCompact_of_isPullback hsq
  have hkerK : NonzeroOnComponents (Scheme.Hom.ker ((C.sel k Y p).baseChangeEmb K)) := by
    rw [ker_eq_comap_ker_of_isPullback_of_flat hsq]
    exact NonzeroOnComponents.comap_of_flat (C.sel k Y p).nonzeroOnComponents_ker _
  exact IsStrictPullbackBlowupSeq.of_isomorphic_pullback (hfield k Y p (C.sel k Y p) K hkerK hsncK)
    (hinv K (baseChange p K) (baseChangeToSpec p K)
      ((C.sel k Y p).baseChange K hkerK hsncK)
      (C.sel K (baseChange p K) (baseChangeToSpec p K))
      (C.basePres k Y p K hkerK hsncK)
      (C.pres K (baseChange p K) (baseChangeToSpec p K)))

def affineSpacePresentedSelection (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    PresentedSelection.{u} where
  sel := affineSpaceEmbeddingChoice hemb hsncE hsm
  pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
  basePres := fun k _ _ Y p _ _ _ _ K _ _ _ hker hsncK =>
    affineSpaceChartBaseChangePresentation hemb hsncE hsm k K Y p hker hsncK

@[simp]
theorem affineSpacePresentedSelection_selection (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    (affineSpacePresentedSelection hemb hsncE hsm).sel = affineSpaceEmbeddingChoice hemb hsncE hsm :=
  rfl

end FunctorialResolution.EmbeddedResolution

end
end

