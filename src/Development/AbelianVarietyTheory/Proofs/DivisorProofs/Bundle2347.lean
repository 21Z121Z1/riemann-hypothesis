import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0592
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsEqDegenerationSeries
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0193
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsJetsChangeSectionBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionWhiskerLeftRangePreimageSnd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem isPullback_whiskerLeft_snd_left {S : Scheme.{0}} (A : Over S) {B' B : Over S} (j : B' ⟶ B) :
    IsPullback (A ◁ j).left (snd A B').left (snd A B).left j.left := by
  refine IsPullback.of_right (h₁₂ := pullback.fst A.hom B.hom) (v₁₃ := A.hom) (h₂₂ := B.hom)
    ?_ ?_ (IsPullback.of_hasPullback A.hom B.hom)
  · have hw : j.left ≫ B.hom = B'.hom := Over.w j
    rw [Over.whiskerLeft_left_fst, hw]
    exact IsPullback.of_hasPullback A.hom B'.hom
  · simp

theorem isOpenImmersion_whiskerLeft_left_and_range {S : Scheme.{0}} (A : Over S) {B' B : Over S}
    (j : B' ⟶ B) [IsOpenImmersion j.left] :
    IsOpenImmersion (A ◁ j).left ∧
      Set.range (A ◁ j).left = (snd A B).left ⁻¹' Set.range j.left := by
  have h := isPullback_whiskerLeft_snd_left A j
  refine ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) h.flip
    inferInstance, ?_⟩
  simpa [Set.image_univ] using Scheme.image_preimage_eq_of_isPullback h.flip Set.univ

end GlobalTheory.DualCon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreconnectedComplexPointsOpenVariety
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.CxPts

namespace GlobalTheory.CxConn

variable {F : Type} [Field F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {σ : F →+* ℂ} {d : ℕ}

theorem exists_algX_eq [IsProper p] [GeometricallyIntegral p] (a : Γ(Y, ⊤)) : ∃ c : F, algX p ⊤ c = a := by
  have : IsIso p.appTop := ProperFunctions.isIso_appTop_of_field p
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso p.appTop).2 a
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 b
  exact ⟨c, congrArg (fun g : Γ(Sp F, ⊤) ⟶ Γ(Y, ⊤) => g ((Scheme.ΓSpecIso (CommRingCat.of F)).inv c))
    (p.appLE_eq_app (U := ⊤))⟩

theorem eq_of_holoOn_univ [SmoothOfRelativeDimension d p] [IsProper p] [GeometricallyIntegral p]
    (hp : IsProjOver p) (R : AnRead p σ d) {f : CxPts p σ → ℂ} (hf : R.HoloOn univ f) (y z : CxPts p σ) :
    f y = f z := by
  have hs : (fun _ => f) ∈ R.holSec (Out.Inh.trivLB Y) := by
    refine ⟨⟨fun i j w hi hj => ?_, fun i w h => (h mem_ptsIn_top).elim⟩, fun i => hf.mono (subset_univ _)⟩
    have e : gv p σ (Out.Inh.trivLB Y) i j w = 1 :=
      (ev_eq (mem_ptsIn_inf.2 ⟨hi, hj⟩) _).trans (map_one _)
    rw [e, one_mul]
  obtain ⟨x, hx⟩ := (AnRead.bijective_valC hp R (Out.Inh.trivLB_isLB Y)).2 ⟨_, hs⟩
  let L : ((Out.Inh.trivLB Y).ι → CxPts p σ → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun s => s PUnit.unit y - s PUnit.unit z
      map_add' := fun s t => add_sub_add_comm _ _ _ _
      map_smul' := fun c s => (mul_sub c _ _).symm }
  have h := SecC.val_mem_of (M := LinearMap.ker L) (fun s => by
    obtain ⟨c, hc⟩ := exists_algX_eq (p := p) (s.f PUnit.unit)
    have e (w : CxPts p σ) : secVal p σ s PUnit.unit w = σ c :=
      (congrArg (fun a => ev p σ ⊤ a w) hc.symm).trans (ev_algX mem_ptsIn_top c)
    change secVal p σ s PUnit.unit y - secVal p σ s PUnit.unit z = 0
    rw [e, e, sub_self]) x
  have e : SecC.val x = fun _ => f := congrArg Subtype.val hx
  rw [e] at h
  exact sub_eq_zero.1 h

theorem exists_holoOn_univ_of_local {R : AnRead p σ d} {A : Set (CxPts p σ)} (hA : Dense A) {u : CxPts p σ → ℂ}
    (h : ∀ y, ∃ (T : Set (CxPts p σ)) (f : CxPts p σ → ℂ), IsOpen T ∧ y ∈ T ∧ R.HoloOn T f ∧ EqOn f u (T ∩ A)) :
    ∃ f, R.HoloOn univ f ∧ EqOn f u A := by
  choose T f hT hy hf he using h
  refine ⟨fun y => f y y, AnRead.holoOn_of_cover (T := T) hT (fun y _ => ⟨y, hy y⟩)
    fun y => ((hf y).mono inter_subset_right).congr fun z hz => ?_, fun y hS => he y ⟨hy y, hS⟩⟩
  have ho := (hT z).inter (hT y)
  have e : EqOn (f z) (f y) (T z ∩ T y ∩ A) := fun w hw =>
    (he z ⟨hw.1.1, hw.2⟩).trans (he y ⟨hw.1.2, hw.2⟩).symm
  exact e.of_subset_closure (((hf z).mono inter_subset_left).continuousOn ho)
    (((hf y).mono inter_subset_right).continuousOn ho) inter_subset_left (hA.open_subset_closure_inter ho)
    ⟨hy z, hz.2⟩

theorem exists_local_extension [GeometricallyIntegral p] [LocallyOfFiniteType p] (R : AnRead p σ d) {W : Y.Opens}
    (hW : (W : Set Y).Nonempty) {u : CxPts p σ → ℂ} (hu : R.HoloOn (ptsIn p σ W) u) {C : ℝ}
    (hC : ∀ y, ‖u y‖ ≤ C) (y : CxPts p σ) :
    ∃ (T : Set (CxPts p σ)) (f : CxPts p σ → ℂ), IsOpen T ∧ y ∈ T ∧ R.HoloOn T f ∧ EqOn f u (T ∩ ptsIn p σ W) := by
  have : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton p
  obtain ⟨i, hi⟩ := R.cover y
  set c := R.chart i
  obtain ⟨φ, hφ, hφW⟩ := CxPtsDense.exists_ne_zero_basicOpen_le c.affine
    ⟨_, mem_ptsIn.1 (c.source_subset hi)⟩ hW
  have hD : Dense (ptsIn p σ (Y.basicOpen φ)) := by
    refine (CxPtsDense.nonempty_and_dense_of_geometricallyIntegral p σ).2 _ (nonempty_iff_ne_empty.2 fun h => hφ ?_)
    exact (basicOpen_eq_bot_iff φ).1 (Opens.ext h)
  have hin {z} (hz : z ∈ c.e.source) : z ∈ ptsIn p σ (Y.basicOpen φ) ↔ ev p σ c.U φ z ≠ 0 :=
    mem_ptsIn_basicOpen (c.source_subset hz) φ
  obtain ⟨v, hv, he⟩ := GlobalTheory.LogExt.riemann_extension_log _ c.e.target (ev p σ c.U φ ∘ c.e.symm) (u ∘ c.e.symm)
    c.e.open_target ((c.holo c.U φ).mono fun b hb => ⟨hb, c.source_subset (c.e.map_target hb)⟩)
    ((hu i).mono fun b hb => ⟨hb.1, ptsIn_mono hφW ((hin (c.e.map_target hb.1)).2 hb.2)⟩)
    (fun b hb => by
      have hs := c.e.map_target hb
      have h₁ := hD.open_subset_closure_inter c.e.open_source hs
      have h₂ := (c.e.continuousAt hs).continuousWithinAt.mem_closure_image h₁
      rw [c.e.right_inv hb] at h₂
      refine closure_mono ?_ h₂
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨c.e.map_source hz.1, ?_⟩
      rw [Function.comp_apply, c.e.left_inv hz.1]
      exact (hin hz.1).1 hz.2)
    fun b _ => ⟨C, 0, Eventually.of_forall fun b' _ => by rw [pow_zero, mul_one]; exact hC _⟩
  have hf : R.HoloOn c.e.source (v ∘ c.e) := by
    have := AnRead.holoOn_of_chart (R := R) (S := univ) (f := v ∘ c.e) c
      ((hv.mono inter_subset_left).congr fun b hb => congrArg v (c.e.right_inv hb.1))
    rwa [inter_univ] at this
  refine ⟨c.e.source, v ∘ c.e, c.e.open_source, hi, hf, ?_⟩
  have ho := c.e.open_source.inter (isOpen_ptsIn (p := p) (σ := σ) W)
  have e : EqOn (v ∘ c.e) u (c.e.source ∩ ptsIn p σ W ∩ ptsIn p σ (Y.basicOpen φ)) := fun z hz => by
    have := he (x := c.e z) ⟨c.e.map_source hz.1.1, by
      rw [Function.comp_apply, c.e.left_inv hz.1.1]; exact (hin hz.1.1).1 hz.2⟩
    simpa only [c.e.left_inv hz.1.1, Function.comp_apply] using this
  exact e.of_subset_closure ((hf.mono inter_subset_left).continuousOn ho)
    ((hu.mono inter_subset_right).continuousOn ho) inter_subset_left (hD.open_subset_closure_inter ho)

theorem isPreconnected_ptsIn_of_isProjOver (d : ℕ) [SmoothOfRelativeDimension d p] [IsProper p]
    [GeometricallyIntegral p] (hp : IsProjOver p) (W : Y.Opens) : IsPreconnected (ptsIn p σ W) := by
  refine isPreconnected_of_forall_constant fun g hg y hy z hz => ?_
  have hW : (W : Set Y).Nonempty := ⟨_, mem_ptsIn.1 hy⟩
  let R := AnRead.all p σ d
  let κ : Bool → ℂ := fun b => if b then 1 else 0
  have hu : R.HoloOn (ptsIn p σ W) (κ ∘ g) := fun i b hb => by
    have h₁ : ContinuousAt (g ∘ (R.chart i).e.symm) b :=
      (hg.continuousAt ((isOpen_ptsIn W).mem_nhds hb.2)).comp ((R.chart i).e.continuousAt_symm hb.1)
    have h₂ : ∀ᶠ b' in 𝓝 b, (g ∘ (R.chart i).e.symm) b' = (g ∘ (R.chart i).e.symm) b :=
      h₁.eventually ((isOpen_discrete _).mem_nhds (mem_singleton _))
    refine ((differentiableAt_const (κ ((g ∘ (R.chart i).e.symm) b))).congr_of_eventuallyEq
      (h₂.mono fun b' hb' => congrArg κ hb')).differentiableWithinAt
  have hC (w) : ‖(κ ∘ g) w‖ ≤ 1 := by
    simp only [Function.comp_apply, κ]
    split_ifs <;> simp
  obtain ⟨f, hf, he⟩ := exists_holoOn_univ_of_local
    ((CxPtsDense.nonempty_and_dense_of_geometricallyIntegral p σ).2 W hW) (exists_local_extension R hW hu hC)
  have e : κ (g y) = κ (g z) := (he hy).symm.trans ((eq_of_holoOn_univ hp R hf y z).trans (he hz))
  revert e
  cases g y <;> cases g z <;> simp [κ]

theorem isPreconnected_ptsIn : ∀ (F : Type) [Field F] [NumberField F] (B : GlobalTheory.ProjVar.Var F) (e : F →+* ℂ)
    (W : B.X.Opens), IsPreconnected (GlobalTheory.CxPts.ptsIn B.str e W) :=
  fun _ _ _ B _ W => isPreconnected_ptsIn_of_isProjOver B.dim B.isProjOver W

end GlobalTheory.CxConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteTypeStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyOfFiniteType_of_isProjOver : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → LocallyOfFiniteType s := by
  first | exact @GlobalTheory.isProjOver_locallyOfFiniteType | exact GlobalTheory.isProjOver_locallyOfFiniteType | (intros; apply GlobalTheory.isProjOver_locallyOfFiniteType <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQProjOver_target_galoisCover_noetherian : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → IsSeparated sY → LocallyOfFiniteType sY → IsQProjOver (π ≫ sY) → IsQProjOver sY := by
  first | exact @GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover | exact GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover | (intros; apply GlobalTheory.GaloisQuotientRing.isQProjOver_of_isGaloisCover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularRingLocalizationOfComapEqBot
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericFibreFactorial

theorem isRegularRing_localization_of_comap_eq_bot (R A : Type) [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] (p : Ideal A) [p.IsPrime]
    (hp : p.comap (algebraMap R A) = ⊥) : IsRegularRing (Localization.AtPrime p) := by
  let K := FractionRing R
  let M := Algebra.algebraMapSubmonoid A (nonZeroDivisors R)
  let B := Localization M
  letI : Algebra K B := localizationAlgebra (nonZeroDivisors R) A
  haveI : IsScalarTower R K B := inferInstance
  haveI h1 : Algebra.IsPushout R A K B :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors R) K A B
  haveI : Algebra.IsPushout R K A B := h1.symm
  haveI : Algebra.Smooth K B := Algebra.Smooth.of_equiv (Algebra.IsPushout.equiv (R := R) (S := K) (R' := A) (S' := B))
  haveI : IsRegularRing B := GlobalTheory.isRegularRing_of_smooth K B
  have disj : Disjoint (M : Set A) (p : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrp
    have : r ∈ p.comap (algebraMap R A) := hrp
    rw [hp, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hr this
  let q := p.map (algebraMap A B)
  haveI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M B p inferInstance disj
  haveI : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime q) q
    exact (IsLocalization.under_map_of_isPrime_disjoint M B inferInstance disj).symm
  haveI : IsRegularRing (Localization.AtPrime q) :=
    GlobalTheory.ExtendRig.isRegularRing_of_isLocalization q.primeCompl _
  exact IsRegularRing.of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime q) (Localization.AtPrime p)).toRingEquiv

theorem ufd_stalk_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp R) [Smooth f] (x : X), (show PrimeSpectrum R from f x).asIdeal = ⊥ →
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  intro R _ _ X _ f _ x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hs : (f.appLE ⊤ U le_top).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  haveI : Nonempty (⊤ : (Sp R).Opens) := ⟨⟨f x, trivial⟩⟩
  haveI : IsDomain Γ(Sp R, ⊤) := inferInstance
  have hgen : f x = genericPoint (Sp R) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hx
  have h1 := IsAffineOpen.comap_primeIdealOf_appLE (f := f) ⊤ (isAffineOpen_top _) U hU le_top hxU
  have h2 : (isAffineOpen_top (Sp R)).primeIdealOf ⟨f x, (show f x ∈ (⊤ : (Sp R).Opens) from trivial)⟩ =
      genericPoint (Spec Γ(Sp R, ⊤)) := by
    rw [← (isAffineOpen_top (Sp R)).primeIdealOf_genericPoint]
    congr 1
    exact Subtype.ext hgen
  rw [h2, genericPoint_eq_bot_of_affine] at h1
  have hcomap : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.comap (f.appLE ⊤ U le_top).hom = ⊥ :=
    congrArg PrimeSpectrum.asIdeal h1
  algebraize [(f.appLE ⊤ U le_top).hom]
  have hreg := isRegularRing_localization_of_comap_eq_bot Γ(Sp R, ⊤) Γ(X, U)
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal hcomap
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : IsRegularRing (X.presheaf.stalk x) :=
    IsRegularRing.of_ringEquiv (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv
  exact GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
    GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
    GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE _

end GlobalTheory.GenericFibreFactorial
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtOfThetaConstantsAndFirstJets
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.ThetaOfJet

open GlobalTheory.MBLow.JetUniq

theorem isGenSec_of_polAVSectionInverseImage {K : Type} [Field K] (x : KeyIn K)
    (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))))
    (h : IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th) : IsGenSec x.P.A x.P.L 1 th := by
  have e : th = TrSec.thSec x.P x.th := by
    refine NormTheta.sec_ext fun j => ?_
    obtain ⟨i, rfl⟩ : ∃ i : x.P.L.ι, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    exact (h i (TrSec.chart_le x.P _)).trans (TrSec.projectionPullbackSectionBaseProduct_isInverseImage x.P x.th i (TrSec.chart_le x.P _)).symm
  subst e
  haveI : Subsingleton (Over.mk (𝟙 (Sp K))).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  refine (GenSecFibre.isGenSec_iff_fibres firstFiveLaws.2.1 (Sp K) x.P K (𝟙 _) _).2 fun p => ?_
  obtain ⟨z, -, hz⟩ := x.th_ne p
  exact ⟨_, Subsingleton.elim _ _, TrSec.nonzero_thSec x.P x.th z hz⟩

theorem ptSecT_left {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (z : baseOver (Sp R) ⟶ A) :
    (ptSecT A z).left = z.left ≫ toProd A := by
  rw [toProd, ← Over.comp_left, comp_lift, Category.comp_id, ptSecT]
  congr 2
  ext
  simpa using (Over.w z).symm

open GlobalTheory.MBLow.JetUniq

theorem fnOf_valR_id {K : Type} [Field K] (f : Γ(Sp K, ⊤)) : GlobalTheory.Ex.fnOf (valR (𝟙 (Sp K)) ⊤ f) = f := by
  have h : ⊤ ≤ (𝟙 (Sp K)) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  rw [valR, dif_pos h]
  simp [GlobalTheory.Ex.fnOf, Scheme.Hom.appLE]
  rfl

theorem isThetaPt_of_thJet : ∀ (K : Type) [Field K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)) (ϑ : I → K) (J : I → Fin g → K), ThJet x hg m pt ϑ J → IsThetaPt x.P m pt fun i => fnOf (ϑ i) := by
  intro K _ x g hg m hm hK I pt ϑ J hJ
  obtain ⟨th, hth, U, t, i₀, c, hUT, hi₀, H⟩ := hJ
  have hLaw : Laws := firstFiveLaws.1
  have hL := x.P.isLB
  let T : Over (Sp K) := baseOver (Sp K)
  obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ x.P m
  have e₁ : (snd T x.P.A).left ≫ (mulA x.P.A m).left = (snd T x.P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α₁, hα₁, -⟩ := exists_gen hL (φ' := ![(snd T x.P.A).left, (snd T x.P.A ^ m).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg₂ (fun q n => f q ^ n) (Category.comp_id _) (Nat.cast_pow m 2).symm
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen x.P.L ![𝟙 x.P.A.left, (mulA x.P.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd T x.P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨α, hα, hn⟩ := NormTheta.exists_normalised hL x.rig_gen m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) rfl α₁ hα₁
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT x.P.A T m) (snd T x.P.A ^ m) (lift_snd _ _)
    ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
  choose s₂ hs₂ using fun i => ThetaPtExist.exists_isTwistPull hL (translT x.P.A (U i).pt) (translPt x.P.A (U i).pt)
    (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) (U i).φ (U i).isGen s₁
  have ht : ∀ i, t i = s₂ i := fun i => NormTheta.sec_ext (tr_unique x.P x.rig hm (fun _ => rfl) (hUT i).1 (hUT i).1
    (hUT i).2 ⟨α, s₁, hα, hn, hs₁, hs₂ i⟩)
  let τ := rigT x.P.A x.P.L x.rig T ((m ^ 2 : ℕ) : ℤ)
  have hτ : τ.IsGen := NormTheta.rigT_isGen x.rig_gen _
  choose w hw using fun i => ThetaPtExist.exists_isValueAt hL (s₂ i) 1 τ hτ
  have k₀ : ⊤ ≤ eSec x.P.A ⁻¹ᵁ x.P.L.U i₀ := fun z hz => hi₀ hz
  let r : K := valR (𝟙 (Sp K)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀) (x.rig.s fun _ => i₀).val
  have hr₀ : r ≠ 0 := (isUnit_valR (𝟙 (Sp K)) ((x.P.L.pull (eSec x.P.A)).U fun _ => i₀)
    (fun z hz => Set.mem_iInter.2 fun _ => k₀ hz) _).ne_zero
  let V₁ := (x.P.L.LinComb (fun _ : Fin 1 => (1 : T ⟶ x.P.A).left) fun _ => ((m ^ 2 : ℕ) : ℤ)).U fun _ => i₀
  let q : K := valR (𝟙 (Sp K)) V₁ (τ.s fun _ => i₀).val
  have hq₀ : q ≠ 0 := (isUnit_valR (𝟙 (Sp K)) V₁ (fun z hz => Set.mem_iInter.2 fun _ => k₀ hz) _).ne_zero
  have hp : (ptSecT x.P.A (1 : T ⟶ x.P.A)).left = eSec x.P.A ≫ toProd x.P.A := by
    rw [ptSecT_left, NormTheta.one_left]
    exact congrArg (· ≫ toProd x.P.A) (Category.id_comp _)
  let j₀ : Fin g := ⟨0, hg ▸ x.g_pos⟩
  have hval : ∀ i, valR (𝟙 (Sp K)) ⊤ (w i) * q = r ^ (m ^ 2) * ϑ i := fun i => by
    have e2 := GlobalTheory.ZH.TorsReg.valR_valueAt x.P.A x.P.L _ (hw i) (𝟙 (Sp K)) i₀ (by
      rintro _ ⟨z, rfl⟩; exact k₀ trivial)
    rw [Category.id_comp, hp, ← ht i] at e2
    let V := LB.wchart x.P.L (fun _ : Fin 1 => (snd (baseOver (Sp K)) x.P.A).left) fun _ => i₀
    have e : (valR (epsLift (x.v (Fin.cast hg.symm j₀))) V ((t i).f fun _ => i₀)).fst = r ^ (m ^ 2) * ϑ i := by
      have := congrArg TrivSqZeroExt.fst (H i j₀)
      simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr,
        add_zero] at this
      exact this
    rw [epsLift_eq] at e
    erw [GlobalTheory.HolHom.valR_comp (A := DualNumber K) (x.v (Fin.cast hg.symm j₀)).left (toProd x.P.A) V] at e
    rw [fst_valR (x.basis.1 _) (le_toProd k₀)] at e
    erw [← GlobalTheory.HolHom.valR_comp (A := K) (eSec x.P.A) (toProd x.P.A) V] at e
    exact e2.symm.trans e
  have un : ∀ a : K, a ≠ 0 → IsUnit (fnOf a) := fun a ha =>
    (IsUnit.mk0 _ ha).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hmu : IsUnit (m : Γ(T.left, ⊤)) := by
    have := un m hK
    rwa [GlobalTheory.Ex.fnOf, map_natCast] at this
  haveI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  refine ThetaSeries.isThetaPt_of_data x.P hm hmu (Nat.cast_pow m 2) th s₁ α τ U s₂ w
    (un _ (div_ne_zero hq₀ (pow_ne_zero (m ^ 2) hr₀))).unit
    ⟨isGenSec_of_polAVSectionInverseImage x th hth, hα, hτ, hs₁, fun i => (hUT i).1, hs₂, hw, fun i => ?_⟩
  rw [IsUnit.unit_spec, ← fnOf_valR_id (w i), ← map_mul]
  congr 1
  field_simp
  linear_combination (hval i).symm

end GlobalTheory.MBLow.ThetaOfJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

open GlobalTheory.DeRham

variable {K : Type} [Field K]

def IsTransl {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left)
    (v : epsR K ⟶ A) (w : Sp (DualNumber B) ⟶ A.left) : Prop :=
  ∃ x' v' : Over.mk (spMap ((algebraMap B (DualNumber B)).comp φ)) ⟶ A,
    x'.left = spMap (algebraMap B (DualNumber B)) ≫ x ∧ v'.left = spMap (dualMap φ) ≫ v.left ∧ (x' * v').left = w

def IsCechKS (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) (i : A.left ⟶ A'.left) (L : LB A.left)
    {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ (J : Type) (W : J → A.left.Opens) (c : J → L.ι)
    (lam : ∀ (_ : J) (B : Type) [CommRing B] [Algebra (DualNumber K) B], (Sp B ⟶ A.left) → (Sp B ⟶ A'.left)),
    ⨆ k, W k = ⊤ ∧ (∀ k, W k ≤ L.U (c k)) ∧
    (∀ k (B : Type) [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left),
      x ≫ A.hom = spMap ((algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K))) → ⊤ ≤ x ⁻¹ᵁ W k →
      lam k B x ≫ A'.hom = spMap (algebraMap (DualNumber K) B) ∧
      spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ lam k B x =
        spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ x ≫ i ∧
      ∀ (B' : Type) [CommRing B'] [Algebra (DualNumber K) B'] (ρ : B →ₐ[DualNumber K] B'),
        spMap (ρ : B →+* B') ≫ lam k B x = lam k B' (spMap (ρ : B →+* B') ≫ x)) ∧
    ∀ (k k' : J) (B : Type) [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left)
      (O : A'.left.Opens) (f : Γ(A'.left, O)) (w : Fin n → (Sp (DualNumber B) ⟶ A.left)),
      x ≫ A.hom = spMap ((algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K))) →
      ⊤ ≤ x ⁻¹ᵁ (W k ⊓ W k') → ⊤ ≤ x ⁻¹ᵁ (i ⁻¹ᵁ O) →
      (∀ a, IsTransl ((algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K))) x (u a) (w a)) →
      valR (lam k B x) O f - valR (lam k' B x) O f =
        algebraMap (DualNumber K) B DualNumber.eps *
          ∑ a, ∑ b, (algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K)) (θ a b) *
            ((valR (w b) _ (L.g (c k) (c k')).val).snd * valR x _ (L.g (c k) (c k'))⁻¹.val) *
            (valR (w a) (i ⁻¹ᵁ O) ((i.app O).hom f)).snd

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitThetaKeyScalarGoodReductionChartStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_thetaKeyScalar_goodReduction_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ κ : KeyRule, IsKeyRule κ → ∀ (M : GChart Y) (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (y : Sp K ⟶ Xo.XF c), y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ x : KeyIn K, KeyAt M (spMap (algebraMap R K) ≫ z) (le_preimage_comp _ hz) x → ∃ u : Rˣ, (κ K x : K) = algebraMap R K u := by
  first | exact @GlobalTheory.KeyUnitGood.isUnit_key_of_good | exact GlobalTheory.KeyUnitGood.isUnit_key_of_good | (intros; apply GlobalTheory.KeyUnitGood.isUnit_key_of_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingComplexEmbeddedFieldStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kawamataViehweg_vanishing_complexEmbeddedField : GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingPair → ∀ (F : Type) [Field F], Nonempty (F →+* ℂ) → ∀ (X : Scheme.{0}) (p : X ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → ∀ (K : CanonLB p D) (N : LB X), (letI := algebraΓOfHom p; IsNef F N) → (letI := algebraΓOfHom p; IsBig F N) → ∀ q : ℕ, 0 < q → Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  first | exact @GlobalTheory.VanishEmbedded.subsingleton_coh_canon_tens | exact GlobalTheory.VanishEmbedded.subsingleton_coh_canon_tens | (intros; apply GlobalTheory.VanishEmbedded.subsingleton_coh_canon_tens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosSemidefRealDetLeProdDiagStatement
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posSemidef_det_le_prod_diag' : ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) ℝ), G.PosSemidef → G.det ≤ ∏ i, G i i := by
  first | exact @GlobalTheory.posSemidef_real_det_le_prod_diag | exact GlobalTheory.posSemidef_real_det_le_prod_diag | (intros; apply GlobalTheory.posSemidef_real_det_le_prod_diag <;> assumption)
end

