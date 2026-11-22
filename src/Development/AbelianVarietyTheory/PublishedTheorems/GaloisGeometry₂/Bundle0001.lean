import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsSepClosedResidueFieldPowerSeriesComplex
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.SmoothNearbyCycles
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory.Published

open GlobalTheory.NCyc in

def SmoothNearbyCycles : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [HenselianLocalRing O]
    [IsSepClosed (ResidueField O)]
    (Ω : Type) [Field Ω] [Algebra O Ω] [IsAlgClosed Ω] [FaithfulSMul O Ω] [Algebra.IsAlgebraic O Ω]
    (l : ℕ) [Fact l.Prime], IsUnit (l : O) →
  ∀ (Λ : Type) [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ], Finite Λ → DiscreteTopology Λ →
    (∃ k : ℕ, ((l ^ k : ℕ) : Λ) = 0) →
  ∀ (X Y : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of O)) [LocallyOfFiniteType p] (q : Y ⟶ Spec (CommRingCat.of O))
    (f : Y ⟶ X) [Smooth f] (hf : f ≫ p = q) (y : SpecialPoint q) (x : SpecialPoint p), f y.1 = x.1 →
  ∀ (L : StrictLoc Y y.1) (M : StrictLoc X x.1) (h : L.scheme ⟶ M.scheme) (hh : h ≫ M.toX = L.toX ≫ f) (n : ℕ),
    Function.Bijective (stalkPull Λ Ω f hf L M h hh n)

open GlobalTheory.NCyc in

example (H : SmoothNearbyCycles) (n : ℕ) : True := by
  letI := henselian_powerSeries_complex
  letI := isSepClosed_residueField_powerSeries_complex
  letI := faithfulSMul_powerSeries_complex
  letI := isAlgebraic_powerSeries_complex
  letI : TopologicalSpace (ZMod 3) := ⊥
  haveI : DiscreteTopology (ZMod 3) := ⟨rfl⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hu : IsUnit ((3 : ℕ) : PowerSeries ℂ) := by
    rw [← map_natCast (algebraMap ℂ (PowerSeries ℂ))]
    exact (IsUnit.mk0 _ (by norm_num)).map _
  have := H (PowerSeries ℂ) (AlgebraicClosure (FractionRing (PowerSeries ℂ))) 3 hu (ZMod 3) inferInstance
    inferInstance ⟨1, by decide⟩ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (Category.id_comp _) (SpecialPoint.closed _)
    (SpecialPoint.closed _) rfl (StrictLoc.ofStrictlyHenselian _) (StrictLoc.ofStrictlyHenselian _) (𝟙 _)
    (by rw [Category.id_comp, Category.comp_id]) n
  trivial

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateHonda
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et
open scoped TensorProduct DirectSum

namespace GlobalTheory.Published

open ReciprocityTheory.ChartRestriction.G.Semi in

def TateHonda : Prop :=
  ∀ (k Ω : Type) [Field k] [Finite k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (φ : Ω ≃ₐ[k] Ω), (∀ x, φ x = x ^ Nat.card k) →
    (∀ (l : ℕ) [Fact l.Prime], (l : k) ≠ 0 → ∀ (A B : Over (Spec (CommRingCat.of k))) [GrpObj A] [GrpObj B]
      [IsAbelianScheme A] [IsAbelianScheme B],
      (∀ f : H ℚ_[l] 1 (geom Ω B.hom) →ₗ[ℚ_[l]] H ℚ_[l] 1 (geom Ω A.hom),
        (∀ σ, f ∘ₗ gal ℚ_[l] Ω B.hom 1 σ = gal ℚ_[l] Ω A.hom 1 σ ∘ₗ f) →
        f ∈ Submodule.span ℚ_[l] {g | ∃ u : A ⟶ B, IsMonHom u ∧ g = pull ℚ_[l] 1 (geomMap Ω A.hom u.left (Over.w u))}) ∧
      ∀ [Module.Finite ℚ_[l] (H ℚ_[l] 1 (geom Ω A.hom))] [Module.Finite ℚ_[l] (H ℚ_[l] 1 (geom Ω B.hom))],
        (gal ℚ_[l] Ω A.hom 1 φ⁻¹).charpoly = (gal ℚ_[l] Ω B.hom 1 φ⁻¹).charpoly →
        ∃ u : A ⟶ B, IsMonHom u ∧ IsFinite u.left ∧ Surjective u.left) ∧
    ∀ P : Polynomial ℤ, P.Monic → Irreducible P → (∀ z : ℂ, Polynomial.aeval z P = 0 → ‖z‖ ^ 2 = (Nat.card k : ℝ)) →
      ∃ (A : Over (Spec (CommRingCat.of k))) (_ : GrpObj A) (_ : IsAbelianScheme A) (e : ℕ), 1 ≤ e ∧
        ∀ (l : ℕ) [Fact l.Prime], (l : k) ≠ 0 → ∀ [Module.Finite ℚ_[l] (H ℚ_[l] 1 (geom Ω A.hom))],
          (gal ℚ_[l] Ω A.hom 1 φ⁻¹).charpoly = (P ^ e).map (Int.castRingHom ℚ_[l])

end GlobalTheory.Published

end
end

