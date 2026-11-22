import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0044
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Statements.LocalTrivialization.LocTrivOfRetraction
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TorusQuotientTorsionLift
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfIdModEpsThickening
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.EpsIso

theorem ker_fst_eq_span (K : Type) [Field K] :
    RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom =
      Ideal.span {(DualNumber.eps : DualNumber K)} := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hx
    have h0 : x.fst = 0 := hx
    refine ⟨TrivSqZeroExt.inl x.snd, ?_⟩
    ext
    · simp [h0]
    · simp
  · rintro ⟨y, rfl⟩
    show (DualNumber.eps * y).fst = 0
    simp

set_option maxHeartbeats 1000000 in
private theorem exists_eq_eps_mul_of_flat_of_eps_mul_eq_zero {K : Type} [Field K] {C : Type} [CommRing C] (a : DualNumber K →+* C)
    (ha : a.Flat) (c : C) (hc : a DualNumber.eps * c = 0) :
    ∃ d : C, c = a DualNumber.eps * d := by
  let _ : Algebra (DualNumber K) C := a.toAlgebra
  have _ : Module.Flat (DualNumber K) C := ha
  have hsum : ∑ _i : Unit, (DualNumber.eps : DualNumber K) • c = 0 := by
    rw [Fintype.sum_unique, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact hc
  obtain ⟨k, b, y, hy, hb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := DualNumber K) (M := C)
    (f := fun _ : Unit => (DualNumber.eps : DualNumber K)) (x := fun _ => c) hsum
  have hkill : ∀ i, b () i = DualNumber.eps * TrivSqZeroExt.inl (b () i).snd := by
    intro i
    have h1 : DualNumber.eps * b () i = 0 := by
      have h0 := hb i
      rwa [Fintype.sum_unique] at h0
    have h2 : (b () i).fst = 0 := by
      have h3 := congrArg TrivSqZeroExt.snd h1
      rw [DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, zero_mul, _root_.one_mul, zero_add,
        TrivSqZeroExt.snd_zero] at h3
      exact h3
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_mul, DualNumber.fst_eps, zero_mul, h2]
    · rw [DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps, zero_mul, zero_add, _root_.one_mul,
        TrivSqZeroExt.fst_inl]
  refine ⟨∑ i, a (TrivSqZeroExt.inl (b () i).snd) * y i, ?_⟩
  rw [show c = ∑ j, b () j • y j from hy (), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hki := hkill i
  rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  conv_lhs => rw [hki]
  rw [map_mul, _root_.mul_assoc]

theorem mem_span_of_flat {K : Type} [Field K] {C : Type} [CommRing C] (a : DualNumber K →+* C)
    (ha : a.Flat) (c : C) (hc : a DualNumber.eps * c = 0) :
    c ∈ Ideal.span {a DualNumber.eps} := by
  rw [Ideal.mem_span_singleton]
  exact exists_eq_eps_mul_of_flat_of_eps_mul_eq_zero a ha c hc

theorem bijective_of_mod_eps {K : Type} [Field K] {B C D : Type} [CommRing B] [CommRing C]
    [CommRing D] (a : DualNumber K →+* B) (φ : B →+* C) (jB : B →+* D) (jC : C →+* D)
    (hφ : ∀ b, jC (φ b) = jB b) (hs : Function.Surjective jB) (hfl : (φ.comp a).Flat)
    (hB : RingHom.ker jB = Ideal.span {a DualNumber.eps})
    (hC : RingHom.ker jC = Ideal.span {φ (a DualNumber.eps)}) : Function.Bijective φ := by
  have hee : a DualNumber.eps * a DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hk : jC (φ (a DualNumber.eps)) = 0 := by
    rw [← RingHom.mem_ker, hC]
    exact Ideal.mem_span_singleton_self _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro b hb
    have h1 : b ∈ RingHom.ker jB := by rw [RingHom.mem_ker, ← hφ, hb, map_zero]
    rw [hB, Ideal.mem_span_singleton] at h1
    obtain ⟨b1, rfl⟩ := h1
    have h2 : (φ.comp a) DualNumber.eps * φ b1 = 0 := by
      rw [RingHom.comp_apply, ← map_mul]
      exact hb
    have h3 := mem_span_of_flat (φ.comp a) hfl (φ b1) h2
    rw [Ideal.mem_span_singleton] at h3
    obtain ⟨c', hc'⟩ := h3
    have h4 : b1 ∈ RingHom.ker jB := by
      rw [RingHom.mem_ker, ← hφ, hc', map_mul, RingHom.comp_apply, hk, zero_mul]
    rw [hB, Ideal.mem_span_singleton] at h4
    obtain ⟨b2, rfl⟩ := h4
    rw [← _root_.mul_assoc, hee, zero_mul]
  · intro c
    obtain ⟨b, hb⟩ := hs (jC c)
    have h1 : c - φ b ∈ RingHom.ker jC := by rw [RingHom.mem_ker, map_sub, hφ, hb, sub_self]
    rw [hC, Ideal.mem_span_singleton] at h1
    obtain ⟨c1, hc1⟩ := h1
    obtain ⟨b1, hb1⟩ := hs (jC c1)
    have h2 : c1 - φ b1 ∈ RingHom.ker jC := by rw [RingHom.mem_ker, map_sub, hφ, hb1, sub_self]
    rw [hC, Ideal.mem_span_singleton] at h2
    obtain ⟨c2, hc2⟩ := h2
    have hφe : φ (a DualNumber.eps) * φ (a DualNumber.eps) = 0 := by
      rw [← map_mul, hee, map_zero]
    refine ⟨b + a DualNumber.eps * b1, ?_⟩
    rw [map_add, map_mul]
    linear_combination (-1 : C) * hc1 - φ (a DualNumber.eps) * hc2 - c2 * hφe

theorem fst_surjective (K : Type) [Field K] :
    Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom := by
  intro x
  exact ⟨algebraMap K (DualNumber K) x, by simp⟩

theorem isHomeomorph_of_isPullback {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K}
    {π : Y' ⟶ Sp (DualNumber K)} {j : Y ⟶ Y'}
    (h : IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)) :
    IsClosedImmersion j ∧ IsHomeomorph j := by
  have hsp : spMap (TrivSqZeroExt.fstHom K K K).toRingHom =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) := rfl
  have hsurj := fst_surjective K
  have hci : IsClosedImmersion (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    rw [hsp]
    exact IsClosedImmersion.spec_of_surjective _ hsurj
  have hsu : Surjective (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    have hr : Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom K K K).toRingHom) = Set.univ := by
      rw [range_comap_of_surjective (f := (TrivSqZeroExt.fstHom K K K).toRingHom)
        (hf := hsurj), PrimeSpectrum.zeroLocus_eq_univ_iff]
      intro x hx
      rw [SetLike.mem_coe, ker_fst_eq_span, Ideal.mem_span_singleton] at hx
      obtain ⟨y, rfl⟩ := hx
      show _ ∈ nilradical _
      rw [mem_nilradical]
      exact ⟨2, by rw [pow_two, _root_.mul_mul_mul_comm, DualNumber.eps_mul_eps, zero_mul]⟩
    rw [hsp]
    exact ⟨fun p => Set.range_eq_univ.1 hr p⟩
  have hcj : IsClosedImmersion j := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hci
  have hsj : Surjective j := MorphismProperty.of_isPullback (P := @Surjective) h.flip hsu
  refine ⟨hcj, ?_⟩
  rw [isHomeomorph_iff_isEmbedding_surjective]
  exact ⟨j.isClosedEmbedding.isEmbedding, hsj.surj⟩

theorem isAffineHom_of_isHomeomorph {X Y : Scheme.{0}} (e : X ⟶ Y) (he : IsHomeomorph e) :
    IsAffineHom e := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  obtain ⟨x, rfl⟩ := he.surjective y
  have hmem : e x ∈ (⊤ : Y.Opens) := trivial
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hmem
  obtain ⟨W, hW, hxW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x ∈ e ⁻¹ᵁ V from hxV)
  let O : Y.Opens := ⟨(⇑e) '' (W : Set X), he.isOpenMap _ W.isOpen⟩
  obtain ⟨g, hgO, hgy⟩ := (show IsAffineOpen V from hV).exists_basicOpen_le (V := O)
    ⟨e x, ⟨x, hxW, rfl⟩⟩ hxV
  have hsub : e ⁻¹ᵁ Y.basicOpen g ≤ W := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hgO hz
    rwa [← he.injective hwz]
  refine ⟨Y.basicOpen g, hgy, (show IsAffineOpen V from hV).basicOpen g, ?_⟩
  have heq : e ⁻¹ᵁ Y.basicOpen g =
      X.basicOpen (X.presheaf.map (homOfLE hWV).op (e.app V g)) := by
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact (inf_eq_right.2 hsub).symm
  rw [heq]
  exact (show IsAffineOpen W from hW).basicOpen _

end GlobalTheory.EpsIso

namespace GlobalTheory

theorem isIso_of_id_mod_eps : ∀ (K : Type) [Field K] (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (π' : Z' ⟶ Sp (DualNumber K)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by
  intro K _ Y Y' Z' q π π' j j' e h h' hfl hπ hj
  subst hπ hj
  obtain ⟨hcj, hhj⟩ := GlobalTheory.EpsIso.isHomeomorph_of_isPullback h
  obtain ⟨hcj', hhj'⟩ := GlobalTheory.EpsIso.isHomeomorph_of_isPullback h'
  have hcf : (⇑(j ≫ e) : Y → Z') = ⇑e ∘ ⇑j := rfl
  have hhe : IsHomeomorph e := by
    rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
    refine ⟨e.continuous, ?_, ?_⟩
    · intro F hF
      have hF' : (⇑e) '' F = (⇑(j ≫ e)) '' ((⇑j) ⁻¹' F) := by
        rw [hcf, Set.image_comp, Set.image_preimage_eq _ hhj.surjective]
      rw [hF']
      exact hhj'.isClosedMap _ (hF.preimage j.continuous)
    · have hb := hhj'.bijective
      rw [hcf] at hb
      exact (Function.Bijective.of_comp_iff _ hhj.bijective).1 hb
  have hA : IsAffineHom e := GlobalTheory.EpsIso.isAffineHom_of_isHomeomorph e hhe
  have hβ : Function.Surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    GlobalTheory.EpsIso.fst_surjective K
  have hker : RingHom.ker (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom).hom =
      Ideal.span {(DualNumber.eps : DualNumber K)} := GlobalTheory.EpsIso.ker_fst_eq_span K
  have hiso : ∀ W : Z'.Opens, IsAffineOpen W → IsIso (e.app W) := by
    intro W hW
    have hW' : IsAffineOpen (e ⁻¹ᵁ W) := IsAffineHom.isAffine_preimage W hW
    have hcomp : (e ≫ π').appLE ⊤ (e ⁻¹ᵁ W) le_top = π'.appLE ⊤ W le_top ≫ e.app W := by
      rw [Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE ..).symm
    have hB := GlobalTheory.ker_app_eq_map_appLE_of_isPullback hβ h' hW
    have hC := GlobalTheory.ker_app_eq_map_appLE_of_isPullback hβ h hW'
    rw [hker, Ideal.map_span, Set.image_singleton] at hB hC
    have hC' := hC.trans (congrArg
      (fun g => Ideal.span {((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ g).hom DualNumber.eps}) hcomp)
    have hfl' := HasRingHomProperty.appLE @Flat (e ≫ π') hfl ⟨⊤, isAffineOpen_top _⟩ ⟨e ⁻¹ᵁ W, hW'⟩ le_top
    have hfl2 := (congrArg (fun g => g.hom.Flat) hcomp).mp hfl'
    have hg : (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom.Flat :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
    have hflat : ((e.app W).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫
        π'.appLE ⊤ W le_top).hom).Flat := by
      have heq : (e.app W).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫
          π'.appLE ⊤ W le_top).hom = (π'.appLE ⊤ W le_top ≫ e.app W).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom := by
        exact RingHom.ext fun x => rfl
      rw [heq]
      exact RingHom.Flat.comp hg hfl2
    have := hcj'
    have hbij := GlobalTheory.EpsIso.bijective_of_mod_eps
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv ≫ π'.appLE ⊤ W le_top).hom
      (e.app W).hom ((j ≫ e).app W).hom (j.app (e ⁻¹ᵁ W)).hom (fun b => rfl)
      (Scheme.Hom.app_surjective (j ≫ e) W hW) hflat hB hC'
    exact (ConcreteCategory.isIso_iff_bijective _).2 hbij
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme.{0})
    (fun V : Z'.affineOpens => V.1) (iSup_affineOpens_eq_top Z') fun V => ?_
  have hsrc : IsAffine (e ⁻¹ᵁ V.1) := IsAffineHom.isAffine_preimage _ V.2
  have htgt : IsAffine V.1 := V.2
  refine ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (arrowIsoSpecΓOfIsAffine (e ∣_ V.1))).mpr ?_
  rw [MorphismProperty.isomorphisms.iff, morphismRestrict_appTop]
  have hV : IsAffineOpen (V.1.ι ''ᵁ ⊤) := by
    rw [Scheme.Opens.ι_image_top]
    exact V.2
  have hb1 : Function.Bijective (e.app (V.1.ι ''ᵁ ⊤)).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 (hiso _ hV)
  have hb2 : Function.Bijective
      (Y'.presheaf.map (eqToHom (image_morphismRestrict_preimage e V.1 ⊤)).op).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  exact isIso_SpecMap_iff.2 (hb2.comp hb1)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotSchemeLocalOfQuotSchemeSt
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TQCompare
open GlobalTheory.UU GlobalTheory.IndefiniteRowSideFullHecke.TorusQuotientTorsionLift

section Clauses
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem isGrpPullback_id_iff {B B' : Over S} [GrpObj B] [GrpObj B'] (β : B.left ⟶ B'.left) :
    IsGrpPullback B B' (𝟙 S) β ↔ ∃ e : B ≅ B', IsMonHom e.hom ∧ e.hom.left = β := by
  constructor
  · rintro ⟨hpb, hmul⟩
    have : IsIso β := hpb.isIso_fst_of_isIso
    have hw : β ≫ B'.hom = B.hom := by simpa using hpb.w
    obtain ⟨e, he⟩ : ∃ e : B ≅ B', e.hom.left = β := ⟨Over.isoMk (asIso β) hw, rfl⟩
    have key : ∀ (T : Over S) (x y : T ⟶ B), (x * y) ≫ e.hom = (x ≫ e.hom) * (y ≫ e.hom) := by
      intro T x y
      have h1 := hmul T x y (Over.homMk (x.left ≫ β) (by simp [hw])) (Over.homMk (y.left ≫ β) (by simp [hw]))
        rfl rfl
      apply Over.OverMorphism.ext
      simp only [Hom.mul_def, Over.comp_left, Over.lift_left, Over.homMk_left, Category.assoc, he] at h1 ⊢
      exact h1.symm
    have hone : ∀ {M : Over S} [GrpObj M], (1 : 𝟙_ (Over S) ⟶ M) = η[M] := by
      intro M _
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    refine ⟨e, ⟨?_, ?_⟩, he⟩
    · have h2 := key (𝟙_ (Over S)) 1 1
      rw [_root_.one_mul] at h2
      have h3 : (1 : 𝟙_ (Over S) ⟶ B) ≫ e.hom = 1 := _root_.mul_left_cancel (h2.symm.trans (_root_.mul_one _).symm)
      rw [hone, hone] at h3
      exact h3
    · have h3 := key _ (fst B B) (snd B B)
      rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h3
      rw [h3]
      congr 1
  · rintro ⟨e, he, rfl⟩
    have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
    refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, ?_⟩
    intro T x y x₀ y₀ hx hy
    have hm := (IsMonHom.monoidHom e.hom T).map_mul x y
    simp only [IsMonHom.monoidHom_apply] at hm
    have h4 := congrArg Over.Hom.left hm
    simp only [Hom.mul_def, Over.comp_left, Over.lift_left, Category.assoc] at h4 ⊢
    simp only [hx, hy]
    exact h4.symm

end Clauses

section At
variable (X : Type) [AddCommGroup X]

def ActGradeAt : Prop := ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G]
  (i : splitTorus S X ⟶ G), IsMonHom i → ∀ V : G.left.Opens, IsAffineOpen V →
  (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V →
  (∀ u : Γ(G.left, V), ∃ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) ∧ u = a.sum fun _ x => x) ∧
  ∀ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) → (a.sum fun _ x => x) = 0 → a = 0

def TQUniqAt : Prop := ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G]
  (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F → ∀ (Q : TQ G X) (Q' : TQ G' X),
  TorusCompat f F Q'.i Q.i → ∃ β : Q'.B.left ⟶ Q.B.left, Q'.q.left ≫ β = F ≫ Q.q.left ∧ IsGrpPullback Q'.B Q.B f β

def TQUniqIdAt : Prop := ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (Q Q' : TQ G X),
  TorusCompat (𝟙 S) (𝟙 G.left) Q'.i Q.i →
    ∃ β : Q'.B.left ⟶ Q.B.left, Q'.q.left ≫ β = 𝟙 G.left ≫ Q.q.left ∧ IsGrpPullback Q'.B Q.B (𝟙 S) β

def TQBaseAt : Prop := ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G]
  (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F → ∀ Q : TQ G X,
  ∃ Q' : TQ G' X, TorusCompat f F Q'.i Q.i

end At

def ForAllGroups (P : ∀ (X : Type) [AddCommGroup X], Prop) : Prop := ∀ (X : Type) [AddCommGroup X], P X

def ForLattices (P : ∀ (X : Type) [AddCommGroup X], Prop) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], P X

def PointLiftComm : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (Q : TQ G X) (R : Type) [CommRing R] [IsLocalRing R] (p : Spec (CommRingCat.of R) ⟶ S)
    (b : pt p ⟶ Q.B), ∃ x : pt p ⟶ G, x ≫ Q.q = b

def TQDimOfExists : Prop :=
  ∀ (S : Scheme.{0}) [Nonempty S] (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (Q : TQ G X), (∃ g, SmoothOfRelativeDimension g G.hom) →
    (∃ g', SmoothOfRelativeDimension g' Q.B.hom) →
    (∀ g' : ℕ, SmoothOfRelativeDimension (g' + Module.finrank ℤ X) G.hom ↔ SmoothOfRelativeDimension g' Q.B.hom) ∧
    (Nonempty S → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → Module.finrank ℤ X ≤ g)

def QuotSchemeLocal : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsNilpotent J →
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
  [IsCommMonObj G] [Smooth G.hom] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left),
  IsGrpPullback G₀ G (red J) F → ∀ (Q₀ : TQ G₀ X) (i : splitTorus _ X ⟶ G), IsMonHom i → TorusCompat (red J) F Q₀.i i →
  ∃ (B : Over (Spec (CommRingCat.of A))) (q : G ⟶ B) (j : Q₀.B.left ⟶ B.left),
    IsPullback j Q₀.B.hom B.hom (red J) ∧ Q₀.q.left ≫ j = F ≫ q.left ∧ IsAffineHom q.left ∧
    ∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ IsAffineOpen V ∧
      (∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a) ∧ Function.Injective (q.left.app V).hom ∧
      (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ∧
      ∃ u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ, ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ

end GlobalTheory.TQCompare
end
end

