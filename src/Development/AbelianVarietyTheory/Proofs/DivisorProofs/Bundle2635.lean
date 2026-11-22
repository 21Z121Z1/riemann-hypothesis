import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.SubAddEqZeroOfEqAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackRestrictISupOfForallRestrict
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isPullback_iSup_of_forall : ∀ (P' X T S : Scheme.{0}) (a : X ⟶ P') (p : X ⟶ S) (q : P' ⟶ T) (π : S ⟶ T), a ≫ q = p ≫ π → ∀ (I : Type) (V : I → P'.Opens), (∀ i, IsPullback (a ∣_ V i) ((a ⁻¹ᵁ V i).ι ≫ p) ((V i).ι ≫ q) π) → IsPullback (a ∣_ (⨆ i, V i)) ((a ⁻¹ᵁ (⨆ i, V i)).ι ≫ p) ((⨆ i, V i).ι ≫ q) π := by
  intro P' X T S a p q π w I V hV
  have hw : (a ∣_ (⨆ i, V i)) ≫ (⨆ i, V i).ι ≫ q = ((a ⁻¹ᵁ (⨆ i, V i)).ι ≫ p) ≫ π := by
    rw [morphismRestrict_ι_assoc, Category.assoc, w]
  set U := ⨆ i, V i with hUdef
  let L := pullback.lift (a ∣_ U) ((a ⁻¹ᵁ U).ι ≫ p) hw
  let Wo : I → U.toScheme.Opens := fun i => U.ι ⁻¹ᵁ V i
  let O : I → (pullback (U.ι ≫ q) π).Opens := fun i => pullback.fst (U.ι ≫ q) π ⁻¹ᵁ Wo i
  have hO : (⨆ i, O i) = ⊤ := by
    simp only [O, Wo]
    rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, ← hUdef, Scheme.Opens.ι_preimage_self,
      Scheme.Hom.preimage_top]
  have hle : ∀ i, V i ≤ U := fun i => le_iSup V i
  have hr1 : ∀ i, Set.range ((Wo i).ι ≫ U.ι) = Set.range (V i).ι := by
    intro i
    ext x
    simp only [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨⟨x, hle i hx⟩, hx⟩, rfl⟩
  have hpt : ∀ z, U.ι (pullback.fst (U.ι ≫ q) π (L z)) = a ((a ⁻¹ᵁ U).ι z) := by
    intro z
    have h := congr($(show L ≫ pullback.fst (U.ι ≫ q) π ≫ U.ι = (a ⁻¹ᵁ U).ι ≫ a by
      rw [pullback.lift_fst_assoc, morphismRestrict_ι]) z)
    simpa using h
  have key : ∀ i, IsIso (L ∣_ O i) := by
    intro i
    let e := IsOpenImmersion.isoOfRangeEq ((Wo i).ι ≫ U.ι) (V i).ι (hr1 i)
    have he : e.hom ≫ (V i).ι = (Wo i).ι ≫ U.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    let j : (a ⁻¹ᵁ V i).toScheme ⟶ (a ⁻¹ᵁ U).toScheme := X.homOfLE (a.preimage_mono (hle i))
    have hj : j ≫ (a ⁻¹ᵁ U).ι = (a ⁻¹ᵁ V i).ι := Scheme.homOfLE_ι _ _
    have outer : IsPullback ((j ≫ L) ≫ pullback.snd (U.ι ≫ q) π) ((a ∣_ V i) ≫ e.inv) π
        ((Wo i).ι ≫ U.ι ≫ q) := by
      have h0 := (hV i).flip
      have e1 : (j ≫ L) ≫ pullback.snd (U.ι ≫ q) π = (a ⁻¹ᵁ V i).ι ≫ p := by
        rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hj]
      rw [e1]
      refine IsPullback.of_iso h0 (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_ ?_
      · simp
      · simp
      · simp
      · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
        rw [← reassoc_of% he, Iso.inv_hom_id_assoc]
    have hv : IsPullback (j ≫ L) ((a ∣_ V i) ≫ e.inv) (pullback.fst (U.ι ≫ q) π) (Wo i).ι := by
      refine IsPullback.of_right (h₁₂ := pullback.snd (U.ι ≫ q) π) (h₂₂ := U.ι ≫ q) (v₁₃ := π) outer ?_
        (IsPullback.of_hasPullback (U.ι ≫ q) π).flip
      rw [← cancel_mono U.ι]
      simp only [Category.assoc, L, pullback.lift_fst_assoc, morphismRestrict_ι, reassoc_of% hj]
      rw [← he, Iso.inv_hom_id_assoc, morphismRestrict_ι]
    have R := (isPullback_morphismRestrict (pullback.fst (U.ι ≫ q) π) (Wo i)).flip
    have hr2 : Set.range ((L ⁻¹ᵁ O i).ι ≫ (a ⁻¹ᵁ U).ι) = Set.range (a ⁻¹ᵁ V i).ι := by
      ext x
      simp only [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
      constructor
      · rintro ⟨y, rfl⟩
        have hy := y.2
        change U.ι (pullback.fst (U.ι ≫ q) π (L y.1)) ∈ V i at hy
        rw [hpt] at hy
        exact hy
      · intro hx
        refine ⟨⟨⟨x, hle i hx⟩, ?_⟩, rfl⟩
        change U.ι (pullback.fst (U.ι ≫ q) π (L ⟨x, hle i hx⟩)) ∈ V i
        exact (congrArg (· ∈ V i) (hpt _)).mpr hx
    let f₁ := IsOpenImmersion.isoOfRangeEq _ _ hr2
    have hkey : L ∣_ O i = f₁.hom ≫ (hv.isoIsPullback _ _ R).hom := by
      rw [← cancel_mono (O i).ι, morphismRestrict_ι, Category.assoc, IsPullback.isoIsPullback_hom_fst,
        ← Category.assoc f₁.hom]
      congr 1
      rw [← cancel_mono (a ⁻¹ᵁ U).ι, Category.assoc, hj, IsOpenImmersion.isoOfRangeEq_hom_fac]
    rw [hkey]
    infer_instance
  have hiso : IsIso L :=
    IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) O hO key
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso L) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularFibreOfJacobianDerivations
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem regular_fibre_of_jacobian : ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsRegularRing T] [Field K] [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q → (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) → ∀ (h : ℕ) (f : Fin h → S) (g : S) (d : Fin h → Derivation ℤ S S) (D : Fin h → Derivation ℤ T T), (∀ i x, D i (algebraMap S T x) = algebraMap S T (d i x)) → g ∉ Q → (∀ j, f j ∈ Q) → (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) → (Matrix.of fun i j => d i (f j)).det ∉ Q → IsRegularRing (T ⊗[S] K) := by
  intro S T K _ _ _ _ _ _ Q hker hfrac h f g d D hD hg hf hgQ hdet
  refine GlobalTheory.T.isRegularRing_tensor_of_regular_fibre_localizations S T K Q hker hfrac ?_
  intro n _ hn
  set F : Fin h → T := fun j => algebraMap S T (f j) with hFdef
  have hFn : ∀ j, F j ∈ n := by
    intro j
    have : f j ∈ n.comap (algebraMap S T) := by rw [hn]; exact hf j
    exact this
  have hdetn : (Matrix.of fun i j => D i (F j)).det ∉ n := by
    intro hmem
    have hm : (Matrix.of fun i j => D i (F j)) = (Matrix.of fun i j => d i (f j)).map (algebraMap S T) := by
      ext i j; simp [hFdef, hD]
    rw [hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hmem
    have : (Matrix.of fun i j => d i (f j)).det ∈ n.comap (algebraMap S T) := hmem
    rw [hn] at this
    exact hdet this
  have hreg := GlobalTheory.T.isRegularLocalRing_quotient_of_det_derivation_unit T h F D n hFn hdetn
  have heq : (Ideal.span (Set.range F)).map (algebraMap T (Localization.AtPrime n)) =
      (Q.map (algebraMap S T)).map (algebraMap T (Localization.AtPrime n)) := by
    have hspan : Ideal.span (Set.range F) = (Ideal.span (Set.range f)).map (algebraMap S T) := by
      rw [Ideal.map_span, ← Set.range_comp]; rfl
    rw [hspan, Ideal.map_map, Ideal.map_map]
    apply le_antisymm
    · apply Ideal.map_mono
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hf j
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap]
      have hu : IsUnit ((algebraMap T (Localization.AtPrime n)).comp (algebraMap S T) g) := by
        rw [RingHom.comp_apply]
        apply IsLocalization.map_units (M := n.primeCompl) (Localization.AtPrime n) (⟨algebraMap S T g, ?_⟩ : n.primeCompl)
        intro hgn
        have : g ∈ n.comap (algebraMap S T) := hgn
        rw [hn] at this
        exact hg this
      have hm : (algebraMap T (Localization.AtPrime n)).comp (algebraMap S T) (g * x) ∈
          (Ideal.span (Set.range f)).map ((algebraMap T (Localization.AtPrime n)).comp (algebraMap S T)) :=
        Ideal.mem_map_of_mem _ (hgQ x hx)
      rw [map_mul] at hm
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hm
  rw [← heq]
  exact hreg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSharpBasisSharpBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.Sep.E8Fibration.Lab

def sharpBasis (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) :
    (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
  (sharpReindex h).trans
    { twistSnd (e8 W).adjugate with
      invFun := twistSnd (e8 W)
      left_inv := twistSnd_twistSnd _ _ (by rw [Matrix.mul_adjugate, hW, one_smul])
      right_inv := twistSnd_twistSnd _ _ (by rw [Matrix.adjugate_mul, hW, one_smul]) }

theorem isSharpBasis_sharpBasis (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) :
    IsSharpBasis W (sharpBasis W hW h) := by
  intro i j
  rw [← sum_omegaStd_single h i j]
  exact sum_omegaStd_twistSnd (e8 W) _ (by simp [e8, Matrix.transpose_add, add_comm])
    (by rw [Matrix.mul_adjugate, hW, one_smul]) _ _

def labMat (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) (a : Fin 2) :
    Matrix (Fin (2 * (8 * h))) (Fin (2 * (8 * h))) ℤ :=
  fun i' i => (sharpBasis W hW h).symm
    (fun u c => ∑ v, actMat W a u v * sharpBasis W hW h (Pi.single i 1) v c) i'

variable {S : Scheme.{0}}

def ptOf {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] {pr : Fin 8 → (A ⟶ B)} (hP : IsProd pr)
    {T : Over S} {C : Type} [Fintype C] (b : C → (T ⟶ B)) (x : Fin 8 → C → ℤ) : T ⟶ A :=
  (hP.2 T fun u => ∏ c, b c ^ x u c).exists.choose

theorem ptOf_pr {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] {pr : Fin 8 → (A ⟶ B)} (hP : IsProd pr)
    {T : Over S} {C : Type} [Fintype C] (b : C → (T ⟶ B)) (x : Fin 8 → C → ℤ) (u : Fin 8) :
    ptOf hP b x ≫ pr u = ∏ c, b c ^ x u c :=
  (hP.2 T fun u => ∏ c, b c ^ x u c).exists.choose_spec u

end GlobalTheory.Poinc.Sep.E8Fibration.Lab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricRigidifiedBundleBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyVals

theorem isSymmetric_bL : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    L.IsSymmetric → (KeyVals.bL L ξ).IsSymmetric :=
  fun _ G _ _ L _ _ ξ h =>
    CubePf.sym_pull (cubeMapOf (isGrpPullback_pullback G ξ)) L (bL L ξ).isLB (bL L ξ).rigGen h

end GlobalTheory.KeyVals
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentOfFibrePullbackTangentAtChart
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
open GlobalTheory.CechKS

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CechKS.isTangent_of_fibre : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (hv : ∀ a, IsTanAtG t (LogKS.chart U) (v a)) {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (A : Over (Sp K)) [GrpObj A] (m : A.left ⟶ t.G.left) (u : Fin n → (epsR K ⟶ A)) (hm : IsGrpPullback A t.G x0 m) (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) (a : Fin n), IsTangent (u a) := by
  intro E _ _ _ H X t U n v hv K _ x0 hU A _ m u hm hu a

  have hunit : η[A].left ≫ m = x0 ≫ η[t.G].left := by
    have hw : (η[A].left ≫ m) ≫ t.G.hom = (𝟙_ (Over (Sp K))).hom ≫ x0 := by
      rw [Category.assoc, hm.1.w, ← Category.assoc, Over.w η[A]]
    let p : Over.mk ((𝟙_ (Over (Sp K))).hom ≫ x0) ⟶ t.G := Over.homMk (η[A].left ≫ m) hw
    have h1 : (1 : 𝟙_ (Over (Sp K)) ⟶ A) = η[A] := by
      rw [Hom.one_def, toUnit_unit, Category.id_comp]
    have hpp := hm.2 (𝟙_ (Over (Sp K))) 1 1 p p (by rw [h1]; rfl) (by rw [h1]; rfl)
    rw [_root_.mul_one, h1] at hpp
    have hp : p * p = p := Over.OverMorphism.ext hpp
    have hp1 : p = 1 := mul_eq_left.mp hp
    have := congrArg (fun q => q.left) hp1
    simp only [p, Over.homMk_left, Hom.one_def, Over.comp_left, Over.toUnit_left, Over.mk_hom] at this
    rw [this]
    simp
  show spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (u a).left = η[A].left
  apply hm.1.hom_ext
  · rw [Category.assoc, hu a, hunit, ← Category.assoc, ← Spec.map_comp]
    have hr : CommRingCat.ofHom (dualMap (ev x0 U.1 hU)) ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom =
        CommRingCat.ofHom (TrivSqZeroExt.fstHom Γ(X, U.1) Γ(X, U.1) Γ(X, U.1)).toRingHom ≫ CommRingCat.ofHom (ev x0 U.1 hU) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      simp [dualMap]
    rw [hr, Spec.map_comp, Category.assoc, (hv a).2, Hom.one_def, Over.comp_left, Over.toUnit_left,
      ← Category.assoc]
    congr 1
    exact GlobalTheory.FlagMod.spMap_ev x0 U.2 hU
  · rw [Category.assoc, Over.w (u a), Over.w η[A]]
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    show _ = 𝟙 (Sp K)
    rw [← Spec.map_id]
    congr 1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTerms
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UT
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSum

section
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

def UTerms (u : ρ.UTest p y₀) (x₀ : S.Gam) {C X : Type} [AddCommGroup X] (lab : C → S.Gam) (j : u.D.toPre.X ≃+ X)
    (T : X → C → PadicAlgCl p) : Prop :=
  ∃ (Φ : u.Geom) (w₀ : W0 u.U.toUnifPre) (ϑ : Fam u.D.toPre (PadicAlgCl p) 1)
    (pk : C → QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (w : ∀ c, GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) 1 (pk c).g.b),
    NormW u.U.toUnifPre w₀ Φ.rig ∧ u.U.ExpandsF (PadicAlgCl p) 1 w₀ Φ.th ϑ ∧
    (∀ c, (pk c).y = 0 ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) (pk c) (Φ.pt (lab c)) ∧ (w c).IsGen ∧
      ∀ k : ℕ, 1 ≤ k → ∀ wk : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k (pk c).g.b, wk.IsGen →
        (∀ z J, Good u.D.toPre.P.L z J → val wk (𝟙 _) z J = val (w c) (𝟙 _) z J ^ k) →
        ∀ (s : SecA u.A (PadicAlgCl p) k) (s' : Fam u.D.toPre (PadicAlgCl p) k) (v : PadicAlgCl p),
          u.U.ExpandsF (PadicAlgCl p) k w₀ s s' → ValAt s (Φ.pt (lab c)) (Φ.fr (lab c)) v →
          SumF (maximalIdeal u.V) (PadicAlgCl p) (coef s' (pk c).g wk) v) ∧
    ∀ (mu : X) (c : C), T mu c * y₀ ⟨S.th x₀, S.th_mem x₀⟩ = coef ϑ (pk c).g (w c) (j.symm mu)

end

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

def IsTerms (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) {p : ℕ} [Fact p.Prime] {z : X.M.Z}
    (c : CTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) (Fin 8 → c.T.D.toPre.X)) (x₀ : X.S.Gam)
    (t : (Fin 8 → c.T.D.toPre.X) → X.S.HH X.M z → PadicAlgCl p) : Prop :=
  ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b)
    (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R')
    (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)),
    Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧
    R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧
    ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) ∧
      ∃ (u : ρ'.UTest p y₀) (l : u.Lab) (j : u.D.toPre.X ≃+ (Fin 8 → c.T.D.toPre.X)),
        (∀ χ, l.q χ = c.sc * (qW W c.T.β (j χ) : ℤ)) ∧
        (∀ a χ, l.yy a = QuotientAddGroup.mk χ → yy a = QuotientAddGroup.mk (j χ)) ∧
        (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
          (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x →
          QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ (ε' E).left →
          CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)) ∧
        UTerms u x₀ (fun κ : X.S.HH X.M z => (κ : X.S.Gam)) j t

end GlobalTheory.Poinc.GSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtFibreSpreadModelAtFieldPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (j : B →+* C) :
    spMap j ≫ spMap f = spMap (j.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem isThetaPt_fibre : ∀ (F Ω T : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] [CommRing T] [IsDomain T] [Algebra F T] (em : F →+* Ω) (jT : T →+* Ω) (t : T →ₐ[F] F), Algebra.FiniteType F T → Function.Injective jT → jT.comp (algebraMap F T) = em → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (m : ℕ) (I : Type) (x : I → (baseOver (Sp Ω) ⟶ A.A)) (y : I → (baseOver (Sp T) ⟶ P.A)) (v : I → F), Odd m → 3 ≤ m → (∀ i, (x i).left ≫ φ = spMap jT ≫ (y i).left) → (∀ i, y i ^ (m ^ 2) = 1) → (∀ z : Over.mk (spMap t.toRingHom) ⟶ P.A, z ^ m = 1 → ∃ i, ((Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫ y i) ^ m = z) → IsThetaPt A m x (fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → IsThetaPt P m (fun i => (Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫ y i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (v i)) := by
  intro F Ω T _ _ _ _ _ _ _ _ em jT t hft hinj hcomp A P φ hp hw m I x y v hm hm3 hxy hy hcov hA
  obtain ⟨⟨hL, hL2, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  haveI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing F T
  let tR : T →+* F := t.toRingHom
  have htR : ∀ a : F, tR (algebraMap F T a) = a := fun a => t.commutes a
  have hsurj : Function.Surjective tR := fun a => ⟨algebraMap F T a, htR a⟩
  let p : Ideal T := RingHom.ker tR
  haveI hpm : p.IsMaximal := RingHom.ker_isMaximal_of_surjective tR hsurj
  let R := Localization.AtPrime p
  let s : Sp R ⟶ Sp T := spMap (algebraMap T R)
  have hjT : ∀ z : p.primeCompl, IsUnit (jT z) := fun z => by
    refine IsUnit.mk0 _ fun h => z.2 ?_
    have : (z : T) = 0 := hinj (h.trans (map_zero jT).symm)
    rw [this]; exact p.zero_mem
  have htU : ∀ z : p.primeCompl, IsUnit (tR z) := fun z => IsUnit.mk0 _ fun h => z.2 h
  let jR : R →+* Ω := IsLocalization.lift hjT
  let r : R →+* F := IsLocalization.lift htU
  have hjR : jR.comp (algebraMap T R) = jT := IsLocalization.lift_comp hjT
  have hr : r.comp (algebraMap T R) = tR := IsLocalization.lift_comp htU
  have hjRinj : Function.Injective jR := by
    refine (injective_iff_map_eq_zero jR).2 fun z hz => ?_
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    have hz' := hz
    simp only [jR] at hz'
    rw [IsLocalization.lift_mk', Units.mul_left_eq_zero] at hz'
    show IsLocalization.mk' R a b = 0
    rw [hinj (hz'.trans (map_zero jT).symm), IsLocalization.mk'_zero]
  let aR : F →+* R := (algebraMap T R).comp (algebraMap F T)
  have hjaR : ∀ a, jR (aR a) = em a := fun a => by
    show (jR.comp (algebraMap T R)) (algebraMap F T a) = em a
    rw [hjR, ← hcomp]; rfl
  have hraR : ∀ a, r (aR a) = a := fun a => by
    show (r.comp (algebraMap T R)) (algebraMap F T a) = a
    rw [hr]; exact htR a
  have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hu : IsUnit (m : R) := by
    have := (IsUnit.mk0 (m : F) hmF).map aR
    rwa [map_natCast] at this

  have hmo : ∀ i, ((Over.homMk s : Over.mk s ⟶ baseOver (Sp T)) ≫ y i) ^ (m ^ 2) = 1 := fun i => by
    rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  obtain ⟨w, hwR⟩ := GlobalTheory.Ex.Specialise.exists_isThetaPt_local hL hL2 P s hm hu _ hmo

  have e1 : spMap jR ≫ s = 𝟙 (Sp Ω) ≫ spMap jT := by
    rw [Category.id_comp, spMap_comp_spMap, hjR]
  have e2 : spMap r ≫ s = spMap tR := by rw [spMap_comp_spMap, hr]
  have hΩ := GlobalTheory.Ex.Specialise.isThetaPt_map hL2 P jR e1 hwR
  have hF := GlobalTheory.Ex.Specialise.isThetaPt_map hL2 P r e2 hwR

  let yΩ : I → (Over.mk (𝟙 (Sp Ω) ≫ spMap jT) ⟶ P.A) := fun i =>
    (Over.homMk (spMap jR) e1 : Over.mk (𝟙 (Sp Ω) ≫ spMap jT) ⟶ Over.mk s) ≫
      (Over.homMk s : Over.mk s ⟶ baseOver (Sp T)) ≫ y i
  have hyΩ : ∀ i, (yΩ i).left = (x i).left ≫ φ := fun i => by
    rw [hxy i]
    simp only [yΩ, Over.comp_left, Over.homMk_left]
    rw [← Category.assoc, e1, Category.id_comp]
  obtain ⟨eA, heA⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hp (𝟙 (Sp Ω)) (𝟙 (Sp Ω) ≫ spMap jT) rfl
  have hxo : ∀ i, x i ^ (m ^ 2) = 1 := fun i => by
    apply eA.injective
    rw [map_pow, map_one]
    have : eA (x i) = yΩ i := Over.OverMorphism.ext ((heA (x i)).trans (hyΩ i).symm)
    rw [this]
    simp only [yΩ]
    rw [← MonObj.comp_pow, ← MonObj.comp_pow, hy, MonObj.comp_one, MonObj.comp_one]
  have hA' := (GlobalTheory.ThetaPtUp.isThetaPt_iff (T := baseOver (Sp Ω)) (x₀ := yΩ) hp hw hyΩ hxo _).1 hA
  let eΩ : Γ(Sp Ω, ⊤) ≃+* Ω := (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv
  haveI : IsLocalRing Γ((Over.mk (𝟙 (Sp Ω) ≫ spMap jT)).left, ⊤) := eΩ.symm.isLocalRing
  obtain ⟨u, hu'⟩ := GlobalTheory.ThetaUniq.exists_unit_over hL.globalFns P hm
    (GlobalTheory.ThetaUniq.isThetaPtOver_of_local P _ hΩ) (GlobalTheory.ThetaUniq.isThetaPtOver_of_local P _ hA')
  let cΩ : Ωˣ := Units.map eΩ.toMonoidHom u
  have hc : ∀ i, em (v i) = (cΩ : Ω) * jR (w i) := fun i =>
    (eΩ.apply_symm_apply (em (v i))).symm.trans (((congrArg eΩ (hu' i)).trans (map_mul eΩ _ _)).trans
      (congrArg (_ * ·) (eΩ.apply_symm_apply (jR (w i)))))

  have hF' : IsThetaPt P m (fun i => (Over.homMk (spMap tR) : Over.mk (spMap tR) ⟶ baseOver (Sp T)) ≫ y i)
      (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (r (w i))) := by
    have hpts : (fun i => (Over.homMk (spMap tR) : Over.mk (spMap tR) ⟶ baseOver (Sp T)) ≫ y i) =
        fun i => (Over.homMk (spMap r) e2 : Over.mk (spMap tR) ⟶ Over.mk s) ≫
          (Over.homMk s : Over.mk s ⟶ baseOver (Sp T)) ≫ y i := funext fun i => by
      refine Over.OverMorphism.ext ?_
      simp only [Over.comp_left, Over.homMk_left]
      rw [← Category.assoc, e2]
    rw [hpts]
    exact hF
  obtain ⟨z, hz, hne⟩ := GlobalTheory.ThetaCoset.exists_ne_zero_over hL hL2 P (spMap tR) (k := m) (by omega) hmF
    (GlobalTheory.ThetaUniq.isThetaPtOver_of_local P _ hF') 1
  obtain ⟨i₀, hi₀⟩ := hcov z hz
  have hr0 : r (w i₀) ≠ 0 := fun h => hne i₀ (by rw [_root_.one_mul]; exact hi₀) (by
    show (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (r (w i₀)) = 0
    rw [h]; exact map_zero _)

  have hv0 : v i₀ ≠ 0 := fun h => hr0 (by
    have q := hc i₀
    rw [h, map_zero, eq_comm, Units.mul_right_eq_zero] at q
    rw [hjRinj (q.trans (map_zero jR).symm), map_zero])
  have key : ∀ i, w i * aR (v i₀) = w i₀ * aR (v i) := fun i => hjRinj (by
    rw [map_mul, map_mul, hjaR, hjaR, hc, hc]; ring)
  have hrw : ∀ i, r (w i) * v i₀ = r (w i₀) * v i := fun i => by
    have q := congrArg r (key i)
    rwa [map_mul, map_mul, hraR, hraR] at q
  have hd : r (w i₀) / v i₀ ≠ 0 := div_ne_zero hr0 hv0
  have hfin : ∀ i, (r (w i₀) / v i₀)⁻¹ * r (w i) = v i := fun i => by
    rw [inv_div, div_mul_eq_mul_div, div_eq_iff hr0]
    linear_combination hrw i
  have H := GlobalTheory.Ex.Specialise.isThetaPt_mul P hF' (inv_ne_zero hd)
  simp only [hfin] at H
  exact H

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaTermsOfMulIndexZeroTermEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem isThetaTerms_of_mul_eq_one : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (N₁ : ℕ) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V₁) (v : V₁) (c₀ : C), IsThetaTerms₀ D N₁ e T → T 0 c₀ * v = 1 → IsThetaTerms D N₁ e (fun mu c => T mu c * v) := by
  intro V₁ _ _ D N₁ X C _ e T v c₀ h hv
  obtain ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨(algebraMap V₁ (FractionRing V₁) v) • th, g, b, w, h₁, h₂, h₃, h₄, ?_, ⟨c₀, hv⟩⟩
  intro mu c z J hJ
  have H := h₅ mu c z J hJ
  rw [ReciprocityTheory.ChartRestriction.G.DVR.sval_smul _ _ _ _ z hJ]
  have e₁ : (lift (𝟙 (TF (R := V₁) (FractionRing V₁))) (g c).b).left ≫
      (fst (TF (R := V₁) (FractionRing V₁)) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst, Over.id_left]
  rw [e₁]
  have e₂ : GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (T mu c * v)) =
      GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) v) *
        GlobalTheory.UT.cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (T mu c)) := by
    simp only [GlobalTheory.UT.cst, map_mul]
    rw [gs_mul _ z ⊤ trivial, mul_comm]
  rw [e₂, _root_.mul_assoc, H]
  simp only [GlobalTheory.UT.cst, _root_.mul_assoc]

end GlobalTheory.Poinc.Sep
end
end

