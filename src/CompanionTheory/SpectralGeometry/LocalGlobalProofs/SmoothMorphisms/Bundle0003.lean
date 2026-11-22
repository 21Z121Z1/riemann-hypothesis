import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.Bundle0001
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.Bundle0002
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.AbelianSchemeSpreadsOutFiniteTypeSubringImports
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0301

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.AbelianSchemeSpreadsOut
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isCommMonObj_of_iso {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] {M N : C}
    [MonObj M] [MonObj N] [IsCommMonObj N] (e : M ≅ N) [IsMonHom e.hom] : IsCommMonObj M where
  mul_comm := by
    rw [← cancel_mono e.hom, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm N]

theorem isAbelianScheme_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G]
    [GrpObj (Over.mk (pullback.snd G.hom f))] (φ : pullback G.hom f ⟶ G.left)
    (h : IsGrpPullback (Over.mk (pullback.snd G.hom f)) G f φ) (hG : IsAbelianScheme G) :
    IsAbelianScheme (Over.mk (pullback.snd G.hom f)) := by
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  refine ⟨isCommMonObj_of_iso e, ?_, ?_, ?_⟩
  · show Smooth (pullback.snd G.hom f); infer_instance
  · show IsProper (pullback.snd G.hom f); infer_instance
  · show GeometricallyConnected (pullback.snd G.hom f); infer_instance

theorem exists_model_relDim : ∀ (R : Type) [CommRing R] (g : ℕ) (A : Over (Sp R)) [GrpObj A] (F : Finset R),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B)
      (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧
        SmoothOfRelativeDimension g B.hom ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  intro R _ g A _ F hA hg
  obtain ⟨S, B, instB, φ, hFS, hS, hB, hφ⟩ := GlobalTheory.T.abelianScheme_spreads_out_finiteType_subring R A F hA
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  have := hB.smooth
  have := hB.proper
  have hsnd : SmoothOfRelativeDimension g (pullback.snd B.hom (spMap (algebraMap S R))) := by
    have hp : IsPullback φ A.hom B.hom (spMap S.subtype) := hφ.1
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    have key : ∀ e : pullback B.hom (spMap S.subtype) ≅ A.left, e.hom ≫ A.hom = pullback.snd _ _ →
        SmoothOfRelativeDimension g (pullback.snd B.hom (spMap S.subtype)) := fun e he =>
      MorphismProperty.of_isPullback (IsPullback.of_horiz_isIso (fst := e.hom) (g := 𝟙 (Sp R))
        ⟨by rw [Category.comp_id, he]⟩) hg
    exact key hp.isoPullback.symm hp.isoPullback_inv_snd
  obtain ⟨R', hR'fg, hR'⟩ := exists_fg_smoothOfRelativeDimension S R B.left B.hom g inferInstance inferInstance hsnd
  obtain ⟨instB₂, φ₁, hB₂, hAB₂, -⟩ := model_passes_to_subalgebra S R A B φ hφ R'
  refine ⟨R'.toSubring, Over.mk (pullback.snd B.hom (spMap (algebraMap S R'))), instB₂, φ₁, ?_, ?_, ?_, hR', hAB₂⟩
  · intro x hx
    exact R'.algebraMap_mem ⟨x, hFS hx⟩
  · have : Algebra.FiniteType S R' := (Subalgebra.fg_iff_finiteType R').1 hR'fg
    have h1 : Algebra.FiniteType ℤ R' := Algebra.FiniteType.trans (S := S) hS this
    exact h1
  · exact isAbelianScheme_of_isGrpPullback _ hB₂ hB

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.ExistsModelAbelianLb
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_model_abelian_lb : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ L : LB A.left, L.IsLB →
      ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left) (M : LB B.left),
        Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ ∧
          M.IsLB ∧ LBIso L (M.pull φ) := by
  intro R _ A _ hA L hL
  obtain ⟨S0, B, gB, φ, -, hft, hB, hpb⟩ := GlobalTheory.T.abelianScheme_spreads_out_finiteType_subring R A ∅ hA
  have hpb' : IsGrpPullback A B (spMap (algebraMap S0 R)) φ := hpb
  haveI : IsProper B.hom := IsAbelianScheme.proper (A := B)
  have hqc : QuasiCompact B.hom := inferInstance
  have hsep : IsSeparated B.hom := inferInstance
  obtain ⟨R', hR', M, hM, hσ⟩ :=
    GlobalTheory.T.line_bundle_spreads_out S0 R B.left A.left B.hom A.hom φ hqc hsep hpb'.1 L hL
  obtain ⟨gB', φ₁, hB'B, hAB', hφ₁⟩ := GlobalTheory.T.abelianScheme_model_baseChange_subalgebra S0 R A B φ hpb' R'
  refine ⟨R'.toSubring, Over.mk (pullback.snd B.hom (spMap (algebraMap S0 R'))), gB', φ₁, M,
    ?_, ?_, hAB', hM, ?_⟩
  · have h1 : Algebra.FiniteType S0 R' := (Subalgebra.fg_iff_finiteType R').mp hR'
    have h2 : Algebra.FiniteType ℤ R' := Algebra.FiniteType.trans hft h1
    exact h2
  · exact GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hB'B
  · exact hσ φ₁ hφ₁ hAB'.1.w

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.SmoothMorphisms.ImportsFurther
section

end

