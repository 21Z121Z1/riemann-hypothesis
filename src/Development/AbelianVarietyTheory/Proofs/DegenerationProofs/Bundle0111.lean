import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenSpread

set_option backward.isDefEq.respectTransparency false

section Bundles

variable {W X Y : Scheme.{0}}

theorem lbIso_pullback {L M : LB X} (h : LBIso L M) (j : Y ⟶ X) : LBIso (L.pull j) (M.pull j) :=
  LBIso.chartPull (GlobalTheory.chartPullPull L j) (GlobalTheory.chartPullPull M j) h

theorem lbIso_pull_pull {L : LB X} (hL : L.IsLB) {a : Y ⟶ X} (j : W ⟶ Y) {a' : W ⟶ X} (ha : a' = j ≫ a) :
    LBIso (L.pull a') ((L.pull a).pull j) :=
  LBIso.chartPull (chartPullSame L _ _ _ j fun _ => ha) (GlobalTheory.chartPullPull _ j) (lbIso_refl (pull_isLB hL a))

theorem lbIso_pull_comp {Z : Scheme.{0}} {L : LB X} {M : LB Z} {a : Y ⟶ X} {b : Y ⟶ Z} (j : W ⟶ Y) {a' : W ⟶ X}
    {b' : W ⟶ Z} (ha : a' = j ≫ a) (hb : b' = j ≫ b) (h : LBIso (L.pull a) (M.pull b)) :
    LBIso (L.pull a') (M.pull b') :=
  LBIso.chartPull (chartPullSame L _ _ _ j fun _ => ha) (chartPullSame M _ _ _ j fun _ => hb) h

theorem lbIso_pull_of_lbIso {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : W ⟶ Y) {a' : W ⟶ X}
    (ha : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (GlobalTheory.chartPullPull M j) (chartPullSame L _ _ _ j fun _ => ha) h

end Bundles

variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_forall_mem {V : (Sp R).Opens} (hV : genericPoint (Sp R) ∈ V) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ z : Sp R', spMap g z ∈ V := by
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, ha, hle⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hV V.isOpen
  refine ⟨a, ?_, fun R' _ g hg z => hle ?_⟩
  · rintro rfl
    simp at ha
  · exact fun h => z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hg)

theorem exists_forall_notMem {C : Set (Sp R)} (hC : IsClosed C)
    (h : ∀ z : Sp K, spMap (algebraMap R K) z ∉ C) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ z : Sp R', spMap g z ∉ C := by
  have hg : genericPoint (Sp R) ∈ Set.range (spMap (algebraMap R K)) := by
    rw [(IsGenericPointHom.fractionField R K).range_eq]; rfl
  obtain ⟨z, hz⟩ := hg
  exact exists_forall_mem (V := ⟨Cᶜ, hC.isOpen_compl⟩) (hz ▸ h z)

theorem exists_isPullback_stalk {Y Y₀ : Scheme.{0}} {p : Y ⟶ Sp R} {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K}
    (h : IsPullback φ p₀ p (spMap (algebraMap R K))) :
    ∃ p₁, IsPullback φ p₁ p ((Sp R).fromSpecStalk (genericPoint (Sp R))) := by
  obtain ⟨e, he⟩ := IsGenericPointHom.fractionField R K
  refine ⟨p₀ ≫ e.hom, h.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp) ?_⟩
  simpa using he.symm

theorem exists_lift_open {S S' Y Y' : Scheme.{0}} (p : Y ⟶ S) (V : S.Opens) {π : Y' ⟶ Y} {p' : Y' ⟶ S'}
    {t : S' ⟶ S} (w : π ≫ p = p' ≫ t) (ht : ∀ z, t z ∈ V) :
    ∃ l : Y' ⟶ pullback p V.ι, l ≫ pullback.fst p V.ι = π := by
  refine ⟨pullback.lift π (IsOpenImmersion.lift V.ι (p' ≫ t) ?_) ?_, pullback.lift_fst _ _ _⟩
  · rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact ht _
  · exact w.trans (IsOpenImmersion.lift_fac _ _ _).symm

theorem exists_hom {Y X Y₀ : Scheme.{0}} (p : Y ⟶ Sp R) [QuasiCompact p] [QuasiSeparated p] (q : X ⟶ Sp R)
    [LocallyOfFinitePresentation q] {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K}
    (h : IsPullback φ p₀ p (spMap (algebraMap R K))) (u₀ : Y₀ ⟶ X) (hu : u₀ ≫ q = φ ≫ p) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (Y' : Scheme.{0}) (π : Y' ⟶ Y) (p' : Y' ⟶ Sp R'), π ≫ p = p' ≫ spMap g →
        ∃ u : Y' ⟶ X, u ≫ q = π ≫ p ∧ ∀ φ' : Y₀ ⟶ Y', φ' ≫ π = φ → φ' ≫ u = u₀ := by
  obtain ⟨p₁, h₁⟩ := exists_isPullback_stalk h
  obtain ⟨V, hV, -, w, u, hw, hwu, hq⟩ := StalkLimit.exists_spread h₁ q u₀ hu
  obtain ⟨a, ha, H⟩ := exists_forall_mem hV
  refine ⟨a, ha, fun R' _ g hg Y' π p' e => ?_⟩
  obtain ⟨l, hl⟩ := exists_lift_open p V e (H R' g hg)
  refine ⟨l ≫ u, by rw [Category.assoc, hq, reassoc_of% hl], fun φ' hφ' => ?_⟩
  have : φ' ≫ l = w := by
    rw [← cancel_mono (pullback.fst p V.ι), Category.assoc, hl, hφ', hw]
  rw [reassoc_of% this, hwu]

theorem exists_lbIso {Y Y₀ : Scheme.{0}} (p : Y ⟶ Sp R) [QuasiCompact p] [QuasiSeparated p]
    {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K} (h : IsPullback φ p₀ p (spMap (algebraMap R K))) {M N : LB Y}
    (hM : M.IsLB) (hN : N.IsLB) (H : LBIso (M.pull φ) (N.pull φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (Y' : Scheme.{0}) (π : Y' ⟶ Y) (p' : Y' ⟶ Sp R'), π ≫ p = p' ≫ spMap g →
        LBIso (M.pull π) (N.pull π) := by
  obtain ⟨p₁, h₁⟩ := exists_isPullback_stalk h
  obtain ⟨hc⟩ := StalkLimit.nonempty_isLimit h₁
  obtain ⟨V₀⟩ : Nonempty (StalkLimit.AffNhd (genericPoint (Sp R))) := IsCofiltered.nonempty
  have : IsAffine V₀.1.toScheme := V₀.2.2
  have : CompactSpace ((StalkLimit.diagram _ p).obj V₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V₀.1.ι)
  have : QuasiSeparatedSpace ((StalkLimit.diagram _ p).obj V₀) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V₀.1.ι)
  let ι₀ : (StalkLimit.diagram _ p).obj V₀ ⟶ Y := pullback.fst p V₀.1.ι
  have e₀ : φ = (StalkLimit.cone h₁).π.app V₀ ≫ ι₀ := (StalkLimit.cone_π_fst h₁ V₀).symm
  obtain ⟨V, i, HV⟩ := exists_lbIso_of_isLimit (StalkLimit.diagram _ p) (fun V => (StalkLimit.cone h₁).π.app V)
    (fun i => (StalkLimit.cone h₁).w i) hc (M.pull ι₀) (N.pull ι₀) (pull_isLB hM _) (pull_isLB hN _)
    (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) (pull_isLB (pull_isLB hN _) _)
      (lbIso_pull_pull hM _ e₀).symm
      (LBIso.trans (pull_isLB hM _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) H (lbIso_pull_pull hN _ e₀)))
  have e₁ : pullback.fst p V.1.ι = (StalkLimit.diagram _ p).map i ≫ ι₀ := (StalkLimit.diagram_map_fst _ p i).symm
  have HV' : LBIso (M.pull (pullback.fst p V.1.ι)) (N.pull (pullback.fst p V.1.ι)) :=
    LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hN _) (lbIso_pull_pull hM _ e₁)
      (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hN _) HV
        (lbIso_pull_pull hN _ e₁).symm)
  obtain ⟨a, ha, Ha⟩ := exists_forall_mem V.2.1
  refine ⟨a, ha, fun R' _ g hg Y' π p' e => ?_⟩
  obtain ⟨l, hl⟩ := exists_lift_open p V.1 e (Ha R' g hg)
  exact lbIso_pull_comp l hl.symm hl.symm HV'

theorem exists_projective_model {X₀ : Scheme.{0}} (f₀ : X₀ ⟶ Sp K) [IsProper f₀] {L₀ : LB X₀}
    (hL : IsAmpleLB L₀) (hL' : L₀.IsLB) :
    ∃ (X : Scheme.{0}) (f : X ⟶ Sp R) (φ : X₀ ⟶ X) (H : LB X) (N : ℕ), IsProper f ∧
      IsPullback φ f₀ f (spMap (algebraMap R K)) ∧ H.IsLB ∧ IsAmpleLB H ∧ 1 ≤ N ∧ LBIso (lbPow L₀ N) (H.pull φ) := by
  obtain ⟨N, hN, M, s, hs⟩ := hL.exists_veryAmpleBy f₀
  obtain ⟨hs, hc⟩ := (ProjSpace.veryAmpleBy_iff f₀ s).1 hs
  let c := ProjSpace.toProj f₀ s hs
  let u := ProjSpace.baseChange M (algebraMap R K)
  have hu := ProjSpace.isPullback_baseChange M (algebraMap R K)
  have : Flat (spMap (algebraMap R K)) := flat_specMap_localization (nonZeroDivisors R) K
  have : Mono (spMap (algebraMap R K)) := mono_specMap_localization (nonZeroDivisors R) K
  have : Flat u := MorphismProperty.of_isPullback (P := @Flat) hu.flip inferInstance
  have : Mono u := MorphismProperty.of_isPullback (P := .monomorphisms _) hu.flip
    (inferInstanceAs (Mono (spMap (algebraMap R K))))
  have : QuasiCompact u := MorphismProperty.of_isPullback (P := @QuasiCompact) hu.flip inferInstance
  have hp := isPullback_toImage_of_isClosedImmersion (c ≫ u) c u rfl
  have := isProper_str R M
  refine ⟨(c ≫ u).image, (c ≫ u).imageι ≫ PSpace.str R M, (c ≫ u).toImage,
    (ProjSpace.O1 R M).pull (c ≫ u).imageι, N, inferInstance, ?_, pull_isLB (ProjSpace.O1_isLB R M) _,
    (isAmple_projective_O_one R M).pull_of_isClosedImmersion _, hN, ?_⟩
  · have := hp.flip.paste_vert hu
    rwa [ProjSpace.toProj_str] at this
  · have h1 {Y : Scheme.{0}} (F : Y ⟶ PSpace R M) := pull_isLB (ProjSpace.O1_isLB R M) F
    refine LBIso.trans (isLB_lbPow hL' _) (pull_isLB (ProjSpace.O1_isLB K M) c) (pull_isLB (h1 _) _)
      (ProjSpace.lbIso_pullback_O1_toProj f₀ s hs).symm ?_
    refine LBIso.trans (pull_isLB (ProjSpace.O1_isLB K M) c) (h1 (c ≫ u)) (pull_isLB (h1 _) _)
      (lbIso_pull_of_lbIso (ProjSpace.lbIso_pull_O1 M (algebraMap R K)).symm c rfl) ?_
    exact lbIso_pull_pull (ProjSpace.O1_isLB R M) _ (Scheme.Hom.toImage_imageι _).symm

theorem exists_isAmpleLB {X X₀ : Scheme.{0}} (f : X ⟶ Sp R) [QuasiCompact f] [QuasiSeparated f]
    {φ : X₀ ⟶ X} {f₀ : X₀ ⟶ Sp K} (h : IsPullback φ f₀ f (spMap (algebraMap R K))) {L H : LB X} {L₀ : LB X₀}
    (hL : L.IsLB) (hH : H.IsLB) (hL₀ : L₀.IsLB) (hA : IsAmpleLB H) {N : ℕ} (hN : 1 ≤ N)
    (e : LBIso L₀ (L.pull φ)) (e' : LBIso (lbPow L₀ N) (H.pull φ)) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) →
        IsAmpleLB (L.pull π) := by
  obtain ⟨a, ha, Ha⟩ := exists_lbIso f h (isLB_lbPow hL N) hH
    (LBIso.trans (pull_isLB (isLB_lbPow hL N) _) (isLB_lbPow (pull_isLB hL _) N) (pull_isLB hH _)
      (lbIso_lbPow_pull hL φ N).symm
      (LBIso.trans (isLB_lbPow (pull_isLB hL _) N) (isLB_lbPow hL₀ N) (pull_isLB hH _) (lbIso_lbPow e N).symm e'))
  refine ⟨a, ha, fun R' _ g hg X' π f' hp => ?_⟩
  have : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) hp.flip inferInstance
  refine (isAmpleLB_pow_iff (pull_isLB hL π) hN).1 ((hA.pull_of_isAffineHom π).of_lbIso
    (isLB_lbPow (pull_isLB hL _) N) ?_)
  exact LBIso.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow hL N) _) (pull_isLB hH _)
    (lbIso_lbPow_pull hL π N) (Ha R' g hg X' π f' hp.w)

end GlobalTheory.GenSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymplecticLevelBaseChangePolarisedAbelian
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

namespace GlobalTheory

theorem exists_level_baseChange : Laws → ∀ (S S' : Scheme.{0}) [IsLocallyNoetherian S] [IsLocallyNoetherian S'] (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → P'.g = P.g → ∀ (k : ℕ) (ze : Γ(S, ⊤)ˣ) (ze' : Γ(S', ⊤)ˣ), f.appTop.hom ze.val = ze'.val → IsPrimitiveRoot ze' k → ∀ lev : Out.Level P k ze, ∃ lev' : Out.Level P' k ze', ∀ (i : Fin (2 * P.g)) (i' : Fin (2 * P'.g)), (i : ℕ) = i' → (lev'.pt i').left ≫ φ = f ≫ (lev.pt i).left := by
  intro hL S S' _ _ f P P' φ h hiso hg k ze ze' hz hprim lev
  have e : 2 * P'.g = 2 * P.g := congrArg (2 * ·) hg
  have cast : ∀ {n n' : ℕ} (e : n' = n) {T : Over S} (y : Fin n → (T ⟶ P.A)) (a : Fin n' → ℕ),
      linComb (fun i => y (Fin.cast e i)) a = linComb y (fun i => a (Fin.cast e.symm i)) := by
    intro n n' e T y a
    subst e
    rfl
  choose pt hpt using fun i => ThetaObjPull.exists_sec h (lev.pt (Fin.cast e i))
  have hpt' : ∀ i, (pt i).left ≫ φ = f ≫ (lev.pt (Fin.cast e i)).left := fun i =>
    congrArg (fun z => z.left) (hpt i)
  have key : ∀ (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ S') (c : Fin (2 * P'.g) → ℕ),
      pushHom h (Over.mk x) (linComb (fun i =>
        (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S') ≫ pt i) c) =
      linComb (fun i => (Over.homMk (x ≫ f) (by simp) : Over.mk (x ≫ f) ⟶ baseOver S) ≫ lev.pt i)
        (fun i => c (Fin.cast e.symm i)) := fun K _ x c => by
    rw [ThetaObjPull.map_linComb]
    refine Eq.trans ?_ (cast e _ c)
    congr 1
    funext i
    apply Over.OverMorphism.ext
    show (x ≫ (pt i).left) ≫ _ = (x ≫ f) ≫ (lev.pt _).left
    rw [Category.assoc, hpt', Category.assoc]
  have := P.isAb.comm
  refine ⟨{ pt := pt
            prim := hprim
            torsion := fun i => ThetaObjPull.pushHom_injective h _ ?_
            indep := fun K _ _ x c c' hc => ?_
            span := fun K _ _ x y hy => ?_
            pairing := fun i j => ?_ }, fun i i' hi => ?_⟩
  · rw [map_pow, map_one, hpt]
    exact (map_pow (preHom (ThetaObjPull.toBase f)) _ _).symm.trans (by rw [lev.torsion, map_one])
  · have q := lev.indep K (x ≫ f) (fun i => c (Fin.cast e.symm i)) (fun i => c' (Fin.cast e.symm i))
      ((key K x _).symm.trans ((congrArg (pushHom h (Over.mk x)) hc).trans (key K x _)))
    funext i
    exact congrFun q (Fin.cast e i)
  · have hy' : pushHom h (Over.mk x) y ^ k = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨c, hc⟩ := lev.span K (x ≫ f) (pushHom h (Over.mk x) y) hy'
    exact ⟨fun i => c (Fin.cast e i), ThetaObjPull.pushHom_injective h _ ((key K x _).trans hc)⟩
  · refine (weilIs_grpPullback_of_comm _ _ _ _ f _ _ _ P.isLB P'.isLB h hiso (baseOver S') k (pt i) (pt j)
      (ThetaObjPull.toBase f ≫ lev.pt _) (ThetaObjPull.toBase f ≫ lev.pt _) _ (hpt' i).symm (hpt' j).symm).2 ?_
    have w := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (ThetaObjPull.toBase f)
      (lev.pairing (Fin.cast e i) (Fin.cast e j))
    rw [map_zpow] at w
    have e₁ : Units.map (ThetaObjPull.toBase f).left.appTop.hom.toMonoidHom ze = ze' := Units.ext hz
    have e₂ : stdSymp P.g (Fin.cast e i) (Fin.cast e j) = stdSymp P'.g i j := by
      simp only [stdSymp, Fin.val_cast, hg]
    rw [e₁, e₂] at w
    exact w
  · obtain rfl : i = Fin.cast e i' := Fin.ext hi
    exact hpt' i'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointSpecialFibreSectionNeZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.TorsionNonzero

section Pull
variable {X Y : Scheme.{0}}

abbrev one (L : LB X) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)

theorem chart_le (L : LB X) {V : X.Opens} (F : Y ⟶ X) (h : ⊤ ≤ F ⁻¹ᵁ V) (k : PUnit → L.ι) :
    (L.pull F).U k ≤ F ⁻¹ᵁ (V ⊓ (one L).U (fun _ => k PUnit.unit)) := fun x hx =>
  ⟨h (x := x) trivial, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx PUnit.unit⟩

theorem appLE_res (F : Y ⟶ X) {U V : X.Opens} {W : Y.Opens} (e : V ≤ U) (h : W ≤ F ⁻¹ᵁ V) (h' : W ≤ F ⁻¹ᵁ U)
    (a : Γ(X, U)) : (F.appLE V W h).hom (resG X e a) = (F.appLE U W h').hom a := by
  rw [← Scheme.Hom.map_appLE F h (homOfLE e).op]
  rfl

theorem res_appLE (F : Y ⟶ X) {U : X.Opens} {W W' : Y.Opens} (e : W' ≤ W) (h : W ≤ F ⁻¹ᵁ U) (h' : W' ≤ F ⁻¹ᵁ U)
    (a : Γ(X, U)) : resG Y e ((F.appLE U W h).hom a) = (F.appLE U W' h').hom a := by
  rw [← Scheme.Hom.appLE_map F h (homOfLE e).op]
  rfl

theorem g_eq {K : Type} [Fintype K] [Unique K] (L : LB X) (F : Y ⟶ X) (i j : K → L.ι)
    (h : _ ≤ F ⁻¹ᵁ (L.U (i default) ⊓ L.U (j default))) :
    ((LB.LinComb L (K := K) (fun _ => F) (fun _ => 1)).g i j).val =
      (F.appLE _ _ h).hom (L.g (i default) (j default)).val := by
  simp only [LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl

def pullSec (L : LB X) {V : X.Opens} (σ : ∀ j, Γ(X, V ⊓ (one L).U j)) (hσ : σ ∈ secOn (one L) V) (F : Y ⟶ X)
    (h : ⊤ ≤ F ⁻¹ᵁ V) : (L.pull F).Sec where
  f k := (F.appLE _ _ (chart_le L F h k)).hom (σ fun _ => k PUnit.unit)
  compat i j := by
    have hi := (inf_le_left : (L.pull F).U i ⊓ (L.pull F).U j ≤ _).trans (chart_le L F h i)
    have hj := (inf_le_right : (L.pull F).U i ⊓ (L.pull F).U j ≤ _).trans (chart_le L F h j)
    have hj' : (L.pull F).U i ⊓ (L.pull F).U j ≤ F ⁻¹ᵁ (one L).U (fun _ => j PUnit.unit) :=
      hj.trans (F.preimage_mono inf_le_right)
    have hi' : (L.pull F).U i ⊓ (L.pull F).U j ≤ F ⁻¹ᵁ (one L).U (fun _ => i PUnit.unit) :=
      hi.trans (F.preimage_mono inf_le_right)
    have hW : (L.pull F).U i ⊓ (L.pull F).U j ≤
        F ⁻¹ᵁ (V ⊓ (one L).U (fun _ => i PUnit.unit) ⊓ (one L).U (fun _ => j PUnit.unit)) := le_inf hi hj'
    have h₁ : (one L).U (fun _ => i PUnit.unit) ⊓ (one L).U (fun _ => j PUnit.unit) ≤
        𝟙 X ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      inf_le_inf (LB.wchart_le L _ _ 0) (LB.wchart_le L _ _ 0)
    have h₂ : (L.pull F).U i ⊓ (L.pull F).U j ≤ F ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
      inf_le_inf (LB.wchart_le L _ _ PUnit.unit) (LB.wchart_le L _ _ PUnit.unit)
    have hU : (L.pull F).U i ⊓ (L.pull F).U j ≤
        F ⁻¹ᵁ ((one L).U (fun _ => i PUnit.unit) ⊓ (one L).U (fun _ => j PUnit.unit)) := le_inf hi' hj'
    have e := congrArg (F.appLE _ _ hW).hom (hσ (fun _ => i PUnit.unit) (fun _ => j PUnit.unit))
    rw [map_mul, appLE_res F _ hW hi, appLE_res F _ hW hj, appLE_res F _ hW hU] at e
    refine (res_appLE F _ _ hi _).trans (e.trans (congrArg₂ (· * ·) ?_ (res_appLE F _ _ hj _).symm))
    refine (congrArg (F.appLE _ _ hU).hom (g_eq L (𝟙 X) _ _ h₁)).trans (Eq.trans ?_ (g_eq L F i j h₂).symm)
    exact congrArg (fun φ => φ.hom (L.g (i PUnit.unit) (j PUnit.unit)).val)
      (Scheme.Hom.appLE_comp_appLE F (𝟙 X) _ _ _ h₁ hU)

theorem le_nonzeroLocus_iff (L : LB X) {V : X.Opens} (σ : ∀ j, Γ(X, V ⊓ (one L).U j)) (hσ : σ ∈ secOn (one L) V)
    (F : Y ⟶ X) (h : ⊤ ≤ F ⁻¹ᵁ V) {K : Type} [Field K] (x : Sp K ⟶ Y) :
    ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (pullSec L σ hσ F h) ↔ ∃ j, valF (x ≫ F) _ (σ j) ≠ 0 := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((Points.le_preimage_iff x _).1 hx)
    have h₁ := (Points.le_preimage_iff x _).2 hk
    have h₂ := Points.le_preimage_mono x (Y.basicOpen_le _) h₁
    have h₃ := (Points.le_preimage_basicOpen_iff x h₂ _).1 h₁
    refine ⟨fun _ => k PUnit.unit, ?_⟩
    rw [Points.valF_eq_valR, ← Points.valR_appLE x F (chart_le L F h k) h₂]
    exact h₃.ne_zero
  · rintro ⟨j, hj⟩
    obtain ⟨a, rfl⟩ : ∃ a, j = fun _ => a := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim _ _)⟩
    have h₁ : ⊤ ≤ (x ≫ F) ⁻¹ᵁ (V ⊓ (one L).U fun _ => a) := by
      by_contra hc
      exact hj (dif_neg hc)
    have h₂ : ⊤ ≤ x ⁻¹ᵁ (L.pull F).U (fun _ => a) := fun z hz =>
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (h₁ hz).2 0
    rw [Points.valF_eq_valR, ← Points.valR_appLE x F (chart_le L F h fun _ => a) h₂] at hj
    exact Points.le_preimage_mono x (le_iSup (fun k => Y.basicOpen ((pullSec L σ hσ F h).f k)) fun _ => a)
      ((Points.le_preimage_basicOpen_iff x h₂ _).2 hj.isUnit)

end Pull

theorem exists_torsion_valF_ne_zero : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Big → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → LBIso (Q.L.L.pull F) u.U.LG.L → ∀ (N : M.Z.Opens) (σ : Q.SecFam N), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.FibNe N σ → y (cPt p) ∈ N → ∃ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ spMap jV) ⟶ u.G, t ^ (S.r * S.N) = 1 ∧ ∃ j, valF (X := Q.G.left) (t.left ≫ F) _ (σ j) ≠ 0 := by
  intro laws laws₂ o Ω _ _ _ _ S ρ M U₀ Q hbig p _ y y₀ u jV yV yK hfac F ψ hmap hiso N σ hσ hne hy
  obtain ⟨hj, hyV, -, -⟩ := hfac
  have hloc := ZHPre.isLocalHom_of_test u jV hj
  have hK : IsAlgClosed (IsLocalRing.ResidueField (OO p)) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hsq := hmap.1.1
  set r : Sp (IsLocalRing.ResidueField (OO p)) ⟶ Sp u.V :=
    spMap (IsLocalRing.residue (OO p)) ≫ spMap jV with hr
  have key : ∀ x, r x = IsLocalRing.closedPoint u.V := fun x => by
    have hx : x = IsLocalRing.closedPoint _ :=
      Subsingleton.elim (α := PrimeSpectrum (IsLocalRing.ResidueField (OO p))) _ _
    subst hx
    exact (congrArg (PrimeSpectrum.comap jV)
      (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans (IsLocalRing.comap_closedPoint jV)
  have hrange : Set.range r = {IsLocalRing.closedPoint u.V} := by
    ext x
    exact ⟨fun ⟨a, ha⟩ => ha ▸ key a, fun h => ⟨IsLocalRing.closedPoint _, (key _).trans h.symm⟩⟩
  have hyN : ⊤ ≤ yV ⁻¹ᵁ N := by
    refine (Points.le_preimage_iff yV N).2 ?_
    rw [← hyV] at hy
    rw [← IsLocalRing.comap_closedPoint jV]
    exact hy
  have hF : ⊤ ≤ F ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N) := by
    rw [← Scheme.Hom.comp_preimage, hsq.w]
    exact fun z _ => hyN (x := u.G.hom z) trivial
  let θ := pullSec Q.L.L σ hσ F hF
  have hθ : ∃ x ∈ nonzeroLocus θ, u.G.hom x = IsLocalRing.closedPoint u.V := by
    obtain ⟨g, j, hg, hv⟩ := hne _ (r ≫ yV) (by
      rintro _ ⟨z, rfl⟩
      exact hyN (x := r z) trivial)
    have h₁ := (le_nonzeroLocus_iff Q.L.L σ hσ F hF (hsq.lift g r hg)).2 ⟨j, by rwa [hsq.lift_fst]⟩
    refine ⟨hsq.lift g r hg (IsLocalRing.closedPoint _), h₁ (x := IsLocalRing.closedPoint _) trivial, ?_⟩
    exact (congrArg (fun φ : Sp _ ⟶ Sp u.V => φ (IsLocalRing.closedPoint _)) (hsq.lift_snd g r hg)).trans (key _)
  have hg : u.A.g = S.g := (H1.dim_unique u.A.A.hom u.A.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback u.cart.1 ρ.P.smoothDim)
    (eSec u.A.A (IsLocalRing.closedPoint (FractionRing u.V)))).trans ρ.g_eq
  have hN : 4 ≤ S.N := by
    rw [ρ.N_eq]
    have h₂ : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (two_pos.trans_le ρ.two_le).ne' _)
    exact Nat.pow_le_pow_left h₂ 2
  have hn : ((S.r * S.N : ℕ) : IsLocalRing.ResidueField (OO p)) ≠ 0 := by
    have := S.unit.map (Spec.preimage (r ≫ yV ≫ M.s)).hom
    rw [map_natCast] at this
    exact this.ne_zero
  have hlt : 6 * (S.N ^ u.A.g * u.A.g.factorial) < (S.r * S.N) ^ 2 := by
    rw [hg]
    exact hbig.2.2.trans_le (Nat.le_self_pow two_ne_zero _)
  have hc := GlobalTheory.FewZeros.card_torsion_translate_zeros_lt laws laws₂ u.V u.complete u.D u.A u.G u.U (Q.L.L.pull F) θ
    (pull_isLB Q.L.isLB F) hiso hθ _ r S.N (S.r * S.N) hrange hN hn hlt 1
  by_contra hcon
  have heq : Nat.card {h : Over.mk r ⟶ u.G // h ^ (S.r * S.N) = 1 ∧ ¬ ⊤ ≤ (1 * h).left ⁻¹ᵁ nonzeroLocus θ} =
      Nat.card {h : Over.mk r ⟶ u.G // h ^ (S.r * S.N) = 1} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun h => and_iff_left_of_imp fun hh hle => hcon ⟨h, hh, ?_⟩)
    rw [_root_.one_mul] at hle
    exact (le_nonzeroLocus_iff Q.L.L σ hσ F hF h.left).1 hle
  omega

end GlobalTheory.ZH.TorsionNonzero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationDataOfSemiAbelianSymmetry
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH

theorem exists_setting_of_hypS : Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∃ E : SplitExt (Sp (IsLocalRing.ResidueField V)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj G)) → HypS A.A A.L → ∀ gen : (Over.pullback (jK V)).obj G ≅ A.A, IsMonHom gen.hom → ∃ s : GlobalTheory.UU.HidaSetting V A G, s.gen = gen := by
  intro laws hext V _ _ hd _ hc A G _ _ hG hE hS gen hgen
  have hV : GlobalTheory.UU.CDVR V := ⟨hd, hc, inferInstance⟩
  obtain ⟨L, hL⟩ := GlobalTheory.UU.polarisation_extends laws V A G hG gen hgen
  obtain ⟨P, rfl⟩ := GlobalTheory.CubicalPackage.exists_package laws V hV A G hG gen hgen L hL
  obtain ⟨w, -, hw, -, -, hiso, -⟩ := GlobalTheory.T.symmetryHyp_extends_semiAbelian_dvr hext V A G hG hS gen hgen P.L hL
  obtain ⟨E, ⟨d⟩⟩ := hE
  have : IsCommMonObj ((Over.pullback (spMap (IsLocalRing.residue V))).obj G) := Functor.isCommMonObj_obj
  obtain ⟨r, hr⟩ := GlobalTheory.UU.thick_zero_factor V
  obtain ⟨Q₀⟩ := GlobalTheory.UU.nonempty_tq_pullback_comp r _ hr G (GlobalTheory.UU.TQ.ofGtDatum d)
  obtain ⟨P₀, h₀⟩ := GlobalTheory.UU.exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P
  obtain ⟨wA, hwA⟩ := hL
  have := E.free
  have := E.finite
  exact ⟨⟨hV, hG, gen, hgen, P, wA, hwA, E.X, Q₀, P₀, h₀,
    GlobalTheory.T.exists_even_cubical_trivialisation_specialFibre laws V hV A G hG gen hgen P w hw hiso E.X Q₀ P₀ h₀⟩, rfl⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitGeneratingSectionPullbackFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_generatingSection_pullback_field : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (φ : R →+* K), Function.Injective φ → ∀ (D : DegPre R) (D' : DegPre K) (hD : IsPullDeg φ D D') (th : H0 D.P.L 1) (th' : H0 D'.P.L 1), (∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) → (∀ s : H0 D'.P.L 1, ∃ r : K, ∀ j, s.f j = resTop _ (scal D'.P.A.hom r) * th'.f j) → ∃ c : Kˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → sval th (r ≫ PsiEvenPull.proj hD) z J = (TauTwist.unitAt (r ≫ D'.P.A.hom) z c * ArcPull.om hD.w z J J' r).val * sval th' r z J' := by
  first | exact @GlobalTheory.exists_unit_generating_section_pull | exact GlobalTheory.exists_unit_generating_section_pull | (intros; apply GlobalTheory.exists_unit_generating_section_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitWeightZeroIntegralCoords
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.ModPrim

theorem exists_unit_and_residue_point : Out.Laws → Out.Laws2 → ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls), Big g N N' → ∀ (c : Sp (OO p) ⟶ G.left) (w : J → OO p), c ≫ G.hom = spMap j → Crd H σ c w → (∃ i, cls i = 0 ∧ IsUnit (w i)) ∧ ∃ x : m.Φ.Pt, x.left ≫ m.r = rPt p ≫ c ∧ Crd (m.Φ.H 1) m.F x.left (fun i => IsLocalRing.residue (OO p) (w i)) := by
  intro L₁ L₂ p _ V _ j G _ g N N' X _ q H J _ σ cls m hB c w hc hw
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have pb : IsPullback m.r m.Φ.G.hom G.hom (rPt p ≫ spMap j) := m.cart.1
  have hsq : (rPt p ≫ c) ≫ G.hom = 𝟙 _ ≫ rPt p ≫ spMap j := by
    rw [Category.assoc, hc, Category.id_comp]
  let x : m.Φ.Pt := Over.homMk (pb.lift (rPt p ≫ c) (𝟙 _) hsq) (pb.lift_snd _ _ hsq)
  have hx : x.left ≫ m.r = rPt p ≫ c := pb.lift_fst _ _ hsq
  obtain ⟨v, hv⟩ := CrdCalc.crd_exists (R := kb p) (m.Φ.H_isLB 1) m.F x.left
  have h₁ := m.red x v hv
  rw [hx] at h₁
  have h₂ := CrdCalc.crd_map (IsLocalRing.residue (OO p)) hw
  obtain ⟨u, hu⟩ := CrdCalc.crd_unique h₁ h₂
  have h₃ : Crd (m.Φ.H 1) m.F x.left (fun i => IsLocalRing.residue (OO p) (w i)) := by
    have := CrdCalc.crd_smul u hv
    rwa [← funext hu] at this
  refine ⟨?_, x, hx, h₃⟩
  have hcov := (GlobalTheory.T.immBy_weight_zero' L₁ L₂ (kb p) m.Φ g N N' _ J _ m.F m.pol hB m.good m.dim).1
  have hmem : (x.left : Sp (kb p) ⟶ m.Φ.G.left) (IsLocalRing.closedPoint (kb p)) ∈
      ⨆ i ∈ {i | m.xe.symm (cls i) = 0}, Out.nonzeroLocus (m.F i) := by
    rw [hcov]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at hmem
  obtain ⟨i, hi, hm⟩ := hmem
  refine ⟨i, m.xe.symm.map_eq_zero_iff.1 hi, ?_⟩
  have h₄ := (CrdCalc.crd_isUnit_iff i h₃).2 ((CrdCalc.top_le_iff _ _).2 hm)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 h₄.ne_zero

end GlobalTheory.ZH.ModPrim
end

