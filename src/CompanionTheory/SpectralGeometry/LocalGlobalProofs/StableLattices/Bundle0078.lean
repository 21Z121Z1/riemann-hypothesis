import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechCohomologyFinrank
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PicardGroupOfFieldTrivial
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PicField

theorem pic_eq_zero (k : Type) [Field k] (c : Pic (Sp k)) : c = 0 := by
  obtain ⟨p⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero c p
  have hV' : V = ⊤ := by
    have hs : Subsingleton (Sp k) := by
      unfold Sp; infer_instance
    ext x
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    exact (Subsingleton.elim x p) ▸ hV
  subst hV'
  have : IsIso (⊤ : (Sp k).Opens).ι := (Sp k).topIso.isIso_hom
  have e : c = CechPic.pull (inv (⊤ : (Sp k).Opens).ι) (CechPic.pull (⊤ : (Sp k).Opens).ι c) := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  rw [e, hc, map_zero]

end GlobalTheory.CompanionTheory.PicField
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TrzCob
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.KerPull

section Twist

variable {X Y : Scheme.{0}}

structure Trz (f : X ⟶ Y) (u : Γ(pullback f f, ⊤)ˣ) (N : LB Y) (τ : ∀ j : N.ι, Γ(X, f ⁻¹ᵁ N.U j)ˣ) : Prop where
  compat : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (i j : N.ι), f (r z) ∈ N.U i → f (r z) ∈ N.U j →
    gm r z _ (τ i) = gm (r ≫ f) z _ (N.g i j) * gm r z _ (τ j)
  twist : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (e : g₁ ≫ f = g₂ ≫ f) (z : Z) (j : N.ι), f (g₂ z) ∈ N.U j →
    gm g₁ z _ (τ j) = gm (pullback.lift g₁ g₂ e) z ⊤ u * gm g₂ z _ (τ j)

def cob (f : X ⟶ Y) (v : Γ(X, ⊤)ˣ) : Γ(pullback f f, ⊤)ˣ :=
  (show Γ(pullback f f, ⊤)ˣ from pullU (pullback.fst f f) ⊤ v) *
    (show Γ(pullback f f, ⊤)ˣ from pullU (pullback.snd f f) ⊤ v)⁻¹

end Twist

section Points

variable {S : Scheme.{0}} {A A' H T W : Over S}

abbrev fT (q : A ⟶ A') (T : Over S) : (A ⊗ T).left ⟶ (A' ⊗ T).left := (lift (fst A T ≫ q) (snd A T)).left

abbrev atPt (χ : Γ((H ⊗ T).left, ⊤)) (h : W ⟶ H) (t : W ⟶ T) : Γ(W.left, ⊤) := (lift h t).left.appTop χ

end Points

end GlobalTheory.CompanionTheory.KerPull
end
end

