import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0076
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
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechFlatComplex
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AffineCoverOfProductFibresStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_cover_of_product_fibres : ∀ {k : Type} [Field k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X) (q : Z ⟶ T)
    (H : IsPullback p q a b) {V : T.Opens} (hV : IsAffineOpen V) {κ : Type} [LinearOrder κ] [Fintype κ]
    (D : κ → X.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤) (G : LB Z) (hG : G.IsLB), (∀ i, IsAffineOpen (p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V)) ∧
    ∃ (Y : Scheme.{0}) (π : Y ⟶ Z) (f : Y ⟶ Spec Γ(T, V)) (E : κ → Y.Opens),
      IsPullback π f q hV.fromSpec ∧ (∀ i, IsAffineOpen (E i)) ∧ ⨆ i, E i = ⊤ ∧
      Nonempty (cechLB (f ≫ hV.fromSpec ≫ b) (G.pull π) E ≅ cechLB (p ≫ a) G fun i => p ⁻¹ᵁ D i ⊓ q ⁻¹ᵁ V) := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjectivity.over_affineOpen_of_isPullback | exact GlobalTheory.CompanionTheory.PointSurjectivity.over_affineOpen_of_isPullback | (intros; apply GlobalTheory.CompanionTheory.PointSurjectivity.over_affineOpen_of_isPullback <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AffineCoverSeparatingFiniteClosedPointsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_cover_separating_finite_closed_points : ∀ (X : Scheme.{0}) [CompactSpace X] (F : Set X) (hF : F.Finite) (hc : ∀ x ∈ F, IsClosed ({x} : Set X)), ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens), (∀ j, IsAffineOpen (V j)) ∧ ⨆ j, V j = ⊤ ∧
      ∀ x ∈ F, ∀ i j, x ∈ V i → x ∈ V j → i = j := by
  first | exact @GlobalTheory.CompanionTheory.CoverPoints.exists_affine_cover_finite_closed_points | exact GlobalTheory.CompanionTheory.CoverPoints.exists_affine_cover_finite_closed_points | (intros; apply GlobalTheory.CompanionTheory.CoverPoints.exists_affine_cover_finite_closed_points <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechComplexTrivialLineBundleNotAcyclicStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_complex_trivial_line_bundle_not_acyclic : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} [Nonempty X] (f : X ⟶ Spec (CommRingCat.of R)) (N : LB X)
    (hN : N.IsLB) (hT : Triv N) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hc : ⨆ i, D i = ⊤), ¬ (cechLB f N D).Acyclic := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjectivity.not_acyclic_cechLB_of_triv | exact GlobalTheory.CompanionTheory.PointSurjectivity.not_acyclic_cechLB_of_triv | (intros; apply GlobalTheory.CompanionTheory.PointSurjectivity.not_acyclic_cechLB_of_triv <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechFlatComplexStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CechFlatComplex : CIFlat := by
  first | exact @GlobalTheory.CompanionTheory.CIFlatPf.ciFlat | exact GlobalTheory.CompanionTheory.CIFlatPf.ciFlat | (intros; apply GlobalTheory.CompanionTheory.CIFlatPf.ciFlat <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CechSliceAcyclicOfTruncationStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_slice_acyclic_of_truncation : ∀ {ν κ : Type} [LinearOrder ν] [LinearOrder κ] [Finite ν] [Finite κ] {R : Type} [CommRing R]
    (A : GlobalTheory.Cube.{0} (ν ⊕ₗ κ) R)
    (hA : ∀ t : Finset κ, 2 ≤ t.card → (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst A t)).Acyclic)
    (hT : ∀ n, Limits.IsZero ((GlobalTheory.cubeComplex (GlobalTheory.Cube.trunc₂ A)).homology (n + 2))) (j : κ), (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst A {j})).Acyclic := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjectivity.cechComplex_sliceFst_singleton_acyclic_of_trunc₂ | exact GlobalTheory.CompanionTheory.PointSurjectivity.cechComplex_sliceFst_singleton_acyclic_of_trunc₂ | (intros; apply GlobalTheory.CompanionTheory.PointSurjectivity.cechComplex_sliceFst_singleton_acyclic_of_trunc₂ <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibreAcyclicityOfSections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

noncomputable section

namespace GlobalTheory.CompanionTheory.PointSurjTotal

theorem acyclic_over_affineOpen {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}}
    (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X) (q : Z ⟶ T) (H : IsPullback p q a b)
    (ha : IsProjBy a) [IsProper a] [Flat a] [IsProper b] (G : LB Z) (hG : G.IsLB)
    (hfib : ∀ (y : Sp k ⟶ T) (σ : X ⟶ Z), y ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X → σ ≫ q = a ≫ y →
      FibAc a (G.pull σ))
    {κ : Type} [LinearOrder κ] [Fintype κ] (B : κ → X.Opens) (hB : ∀ i, IsAffineOpen (B i))
    (hc : ⨆ i, B i = ⊤) {V : T.Opens} (hV : IsAffineOpen V) :
    (cechLB (p ≫ a) G fun i => p ⁻¹ᵁ B i ⊓ q ⁻¹ᵁ V).Acyclic := by
  obtain ⟨-, Y, π, f, E, Hy, hE, hEc, ⟨i₁⟩⟩ := over_affineOpen_of_isPullback a b p q H hV B hB hc G hG
  have h := fibAc_of_closed_fibres a b p q H ha G hG Γ(T, V) hV.fromSpec Y π f Hy
    (fun s σ h₁ h₂ h₃ => hfib (s ≫ hV.fromSpec) σ (by simpa using h₁) h₂ (by simpa using h₃))
    κ E hE hEc
  exact fun m => (GlobalTheory.MumfordCohom.acyclic_cechLB_of_acyclic f _ _ E h m).of_iso i₁

theorem fibAc_comp_of_fibres : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsProper a] [Flat a] [IsProper b] (G : LB Z) (hG : G.IsLB)
    (hfib : ∀ (y : Sp k ⟶ T) (σ : X ⟶ Z), y ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X → σ ≫ q = a ≫ y → FibAc a (G.pull σ)), FibAc (p ≫ a) G := by
  intro k _ _ X T Z a b p q H ha _ _ _ G hG hfib κ _ _ D hD hc n
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from a]; infer_instance⟩
  have : T.IsSeparated := ⟨by rw [← terminal.comp_from b]; infer_instance⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace b
  obtain ⟨m, B, hB, hBc⟩ := GlobalTheory.PicZeroVan.exists_fin_affine_cover X
  obtain ⟨r, E, hE, hEc⟩ := GlobalTheory.PicZeroVan.exists_fin_affine_cover T
  let V : Fin (r + 1) → T.Opens := Fin.cons ⊥ E
  have hV : ∀ j, IsAffineOpen (V j) := fun j => by
    refine Fin.cases ?_ (fun j => ?_) j
    · exact isAffineOpen_bot T
    · exact hE j
  have hVc : ⨆ j, V j = ⊤ := by
    rw [← top_le_iff, ← hEc]
    exact iSup_le fun j => le_iSup V j.succ
  have hsep : IsSeparated (p ≫ a) := by
    have : IsSeparated p := MorphismProperty.of_isPullback (P := @IsSeparated) H.flip inferInstance
    infer_instance
  obtain ⟨e₁⟩ := cechLB_homology_equiv_trunc₂ k Z (p ≫ a) G κ D (Fin m) (fun i => p ⁻¹ᵁ B i)
    (Fin (r + 1)) (fun j => q ⁻¹ᵁ V j) hG hsep hD hc
    (by rw [← Scheme.Hom.preimage_iSup, hBc, Scheme.Hom.preimage_top])
    (by rw [← Scheme.Hom.preimage_iSup, hVc, Scheme.Hom.preimage_top])
    (fun i _ h => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hB i) h)
    (fun j _ h => GlobalTheory.MumfordCohom.isAffineOpen_preimage_inf _ (hV j) h)
    (fun i j => (over_affineOpen_of_isPullback a b p q H (hV j) B hB hBc G hG).1 i) n
  have e₂ := trunc₂HomologyIsoFstSingleton (0 : Fin (r + 1)) (secCube (p ≫ a) G
    fun u : Fin m ⊕ₗ Fin (r + 1) =>
      Sum.elim (fun i => p ⁻¹ᵁ B i) (fun j => q ⁻¹ᵁ V j) (ofLex u))
    (fun t ht _ => by
      have hVt : IsAffineOpen (⨅ j ∈ t, V j) :=
        IsAffineOpen.biInf _ t.finite_toSet ht fun j _ => hV j
      obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ a) G
        (fun i => p ⁻¹ᵁ B i) (fun j => q ⁻¹ᵁ V j) t _ (preimage_biInf V q t)
      exact fun l => (acyclic_over_affineOpen a b p q H ha G hG hfib B hB hBc hVt l).of_iso i₂) n
  obtain ⟨i₂⟩ := GlobalTheory.MumfordCohom.nonempty_cech_sliceFst_iso (p ≫ a) G
    (fun i => p ⁻¹ᵁ B i) (fun j => q ⁻¹ᵁ V j) {0} (q ⁻¹ᵁ V 0) (by simp)
  have h₀ := (acyclic_over_affineOpen a b p q H ha G hG hfib B hB hBc (hV 0) n).of_iso i₂
  have z := h₀.isZero_homology.of_iso e₂
  have : Subsingleton _ := ModuleCat.subsingleton_of_isZero z
  have := e₁.toEquiv.subsingleton
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (ModuleCat.isZero_of_subsingleton _)

end GlobalTheory.CompanionTheory.PointSurjTotal
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibrewiseAcyclicityBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibrewise_acyclicity_base_change : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsSeparated a] [Flat a] (G : LB Z) (hG : G.IsLB)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) [LocallyOfFiniteType (t ≫ b)] (Y : Scheme.{0})
    (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)) (Hy : IsPullback π f q t)
    (hfib : ∀ (s : Sp k ⟶ Spec (CommRingCat.of R)) (σ : X ⟶ Z), s ≫ t ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X →
      σ ≫ q = a ≫ s ≫ t → FibAc a (G.pull σ)), FibAc f (G.pull π) := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjectivity.fibAc_of_closed_fibres | exact GlobalTheory.CompanionTheory.PointSurjectivity.fibAc_of_closed_fibres | (intros; apply GlobalTheory.CompanionTheory.PointSurjectivity.fibAc_of_closed_fibres <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteCommutativeGroupDualCharacter
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.KerPull

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.KerPull.Cartier

section Alg

open scoped TensorProduct
open Coalgebra WithConv

variable (k D : Type) [Field k] [CommRing D] [Bialgebra k D] [Module.Finite k D]

abbrev Du := WithConv (Module.Dual k D)

variable {k D} {R : Type} [CommRing R]

def pair (a : D → R) (β : Du k D → R) : R :=
  ∑ i, a (Module.finBasis k D i) * β (toConv ((Module.finBasis k D).coord i))

variable [Algebra k R]

theorem pair_counit [IsCocomm k D] (β : Du k D →ₐ[k] R) :
    pair (fun d => algebraMap k R (counit (R := k) d)) β = 1 := by
  have h : ∑ i, counit (R := k) (Module.finBasis k D i) • (toConv ((Module.finBasis k D).coord i) : Du k D) = 1 := by
    apply ofConv_injective
    have := (Module.finBasis k D).sum_dual_apply_smul_coord (counit (R := k) (A := D))
    rw [LinearMap.convOne_def]
    refine Eq.trans ?_ (this.trans ?_)
    · ext d; simp
    · ext d; simp
  unfold pair
  rw [← map_one β, ← h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def]

theorem pair_mul [IsCocomm k D] (a a' : D →ₗ[k] R) (β : Du k D →ₐ[k] R) (ψ : D ⊗[k] D →+ R)
    (hψ : ∀ x y, ψ (x ⊗ₜ y) = a x * a' y) (c : D → R) (hc : ∀ d, c d = ψ (comul (R := k) d)) :
    pair c β = pair a β * pair a' β := by
  set b := Module.finBasis k D with hb
  let cc : _ → Du k D := fun i => toConv (b.coord i)
  have hexp : ∀ (f : D →ₗ[k] R) (d : D), f d = ∑ j, b.coord j d • f (b j) := by
    intro f d
    calc f d = f (∑ j, b.repr d j • b j) := by rw [b.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, Module.Basis.coord_apply]
  have key1 : ∀ x : D ⊗[k] D, ψ x = ∑ j, ∑ l,
      (LinearMap.mul' k k (TensorProduct.map (b.coord j) (b.coord l) x)) • (a (b j) * a' (b l)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u v =>
      rw [hψ, hexp a u, hexp a' v, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, Algebra.smul_def, map_mul]
      ring
    | add x y hx hy =>
      simp only [map_add, add_smul, Finset.sum_add_distrib, hx, hy]
  have key2 : ∀ j l, β (cc j) * β (cc l) = ∑ i,
      (LinearMap.mul' k k (TensorProduct.map (b.coord j) (b.coord l) (comul (R := k) (b i)))) • β (cc i) := by
    intro j l
    rw [← map_mul]
    have h := b.sum_dual_apply_smul_coord (cc j * cc l).ofConv
    have h' : cc j * cc l = ∑ i, (cc j * cc l).ofConv (b i) • cc i := by
      apply ofConv_injective
      refine h.symm.trans ?_
      ext d; simp [cc]
    rw [h', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 1
  unfold pair
  simp only [← hb]
  rw [Finset.sum_mul_sum]
  simp only [hc, key1, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have := key2 j l
  simp only [cc] at this
  calc _ = (a (b j) * a' (b l)) * ∑ i, (LinearMap.mul' k k (TensorProduct.map (b.coord j) (b.coord l) (comul (R := k) (b i)))) • β (toConv (b.coord i)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Algebra.smul_def]; ring
    _ = _ := by rw [← this]; ring

end Alg

section Sch

open scoped TensorProduct
open Coalgebra WithConv

def fnR {X : Scheme.{0}} {A : Type} [CommRing A] (x : X ⟶ Spec (.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ x.appTop).hom

theorem fnR_comp {X Y : Scheme.{0}} {A : Type} [CommRing A] (f : Y ⟶ X) (x : X ⟶ Spec (.of A)) (a : A) :
    fnR (f ≫ x) a = f.appTop (fnR x a) := by
  rw [fnR, fnR, Scheme.Hom.comp_appTop]
  rfl

theorem fnR_specMap {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (x : X ⟶ Spec (.of B)) (a : A) :
    fnR (x ≫ Spec.map (CommRingCat.ofHom φ)) a = fnR x (φ a) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have h2 := congr($h a)
  simp only [fnR, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h2 ⊢
  simp only [CommRingCat.hom_ofHom] at h2
  rw [h2]

variable {k : Type} [Field k]

@[reducible] def wAlg (W : Over (Sp k)) : Algebra k Γ(W.left, ⊤) := (fnR W.hom).toAlgebra

theorem fnR_algebraMap {W : Over (Sp k)} {A : Type} [CommRing A] [Algebra k A]
    (x : W ⟶ (Spec (.of A)).asOver (Spec (.of k))) (c : k) :
    fnR x.left (algebraMap k A c) = fnR W.hom c := by
  have h : x.left ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = W.hom := Over.w x
  exact (fnR_specMap (algebraMap k A) x.left c).symm.trans (congrArg (fun y => fnR y c) h)

def ptr {W : Over (Sp k)} {A : Type} [CommRing A] [Algebra k A]
    (x : W ⟶ (Spec (.of A)).asOver (Spec (.of k))) :
    letI := wAlg W
    A →ₐ[k] Γ(W.left, ⊤) :=
  letI := wAlg W
  { fnR x.left with
    commutes' := fun c => by
      exact fnR_algebraMap x c }

variable {D : Type} [CommRing D] [HopfAlgebra k D]

theorem fn_mul {W : Over (Sp k)} (x y : W ⟶ (Spec (.of D)).asOver (Spec (.of k))) :
    ∃ ψ : D ⊗[k] D →+ Γ(W.left, ⊤), (∀ u v, ψ (u ⊗ₜ v) = fnR x.left u * fnR y.left v) ∧
      ∀ d, fnR (x * y).left d = ψ (comul (R := k) d) := by
  let L : W.left ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap k D))) (Spec.map (CommRingCat.ofHom (algebraMap k D))) :=
    (lift x y).left
  let M : W.left ⟶ Spec (.of (D ⊗[k] D)) := L ≫ (pullbackSpecIso k D D).hom
  have hf : L ≫ pullback.fst _ _ = x.left := by
    have := congrArg Over.Hom.left (lift_fst x y)
    rw [Over.comp_left, Over.fst_left] at this
    exact this
  have hs : L ≫ pullback.snd _ _ = y.left := by
    have := congrArg Over.Hom.left (lift_snd x y)
    rw [Over.comp_left, Over.snd_left] at this
    exact this
  have h1 : M ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = x.left :=
    (Category.assoc _ _ _).trans ((congrArg (fun z => L ≫ z) (pullbackSpecIso_hom_fst k D D)).trans hf)
  have h2 : M ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : D →ₐ[k] D ⊗[k] D).toRingHom) = y.left :=
    (Category.assoc _ _ _).trans ((congrArg (fun z => L ≫ z) (pullbackSpecIso_hom_snd k D D)).trans hs)
  refine ⟨(fnR M).toAddMonoidHom, fun u v => ?_, fun d => ?_⟩
  · have e : u ⊗ₜ[k] v = Algebra.TensorProduct.includeLeftRingHom u *
        (Algebra.TensorProduct.includeRight : D →ₐ[k] D ⊗[k] D).toRingHom v := by simp
    show fnR M _ = _
    rw [e, map_mul, ← fnR_specMap, ← fnR_specMap, h1, h2]
  · have hμ : (x * y).left = M ≫ Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom k D).toRingHom) := by
      rw [Hom.mul_def, Over.comp_left, mul_spec_asOver_spec_left (R := .of k) (A := .of D)]
      simp only [M, L]
      rfl
    rw [hμ, fnR_specMap]
    rfl

theorem fn_one {W : Over (Sp k)} (d : D) :
    fnR (1 : W ⟶ (Spec (.of D)).asOver (Spec (.of k))).left d = fnR W.hom (counit (R := k) d) := by
  have h : (1 : W ⟶ (Spec (.of D)).asOver (Spec (.of k))).left =
      W.hom ≫ Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom k D).toRingHom) := by
    rw [Hom.one_def, Over.comp_left, one_spec_asOver_spec_left (R := .of k) (A := .of D)]
    rfl
  rw [h, fnR_specMap]
  rfl

end Sch

section Aff

open scoped TensorProduct
open Coalgebra WithConv

variable (k D : Type) [Field k] [CommRing D] [HopfAlgebra k D]

abbrev GD : Over (Sp k) := (Spec (.of D)).asOver (Spec (.of k))

variable [Module.Finite k D] [IsCocomm k D]

abbrev TE : Over (Sp k) := (Spec (.of (Du k D))).asOver (Spec (.of k))

variable {k D}

def P {W : Over (Sp k)} (x : W ⟶ GD k D) (t : W ⟶ TE k D) : Γ(W.left, ⊤) :=
  pair (fnR x.left) (fnR t.left)

theorem twoPow_mul_twoPow {W : Over (Sp k)} (x y : W ⟶ GD k D) (t : W ⟶ TE k D) :
    P (x * y) t = P x t * P y t := by
  obtain ⟨ψ, h1, h2⟩ := fn_mul x y
  letI := wAlg W
  exact pair_mul (ptr x).toLinearMap (ptr y).toLinearMap (ptr t) ψ h1 _ h2

theorem P_one {W : Over (Sp k)} (t : W ⟶ TE k D) : P (1 : W ⟶ GD k D) t = 1 := by
  letI := wAlg W
  have h : (fnR (1 : W ⟶ GD k D).left : D → Γ(W.left, ⊤)) =
      fun d => algebraMap k Γ(W.left, ⊤) (counit (R := k) d) := by
    funext d
    exact fn_one d
  unfold P
  rw [h]
  exact pair_counit (ptr t)

theorem pullback_comp₂ {W W' : Over (Sp k)} (f : W' ⟶ W) (x : W ⟶ GD k D) (t : W ⟶ TE k D) :
    f.left.appTop (P x t) = P (f ≫ x) (f ≫ t) := by
  simp only [P, pair, map_sum, map_mul, Over.comp_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg₂ (· * ·) (fnR_comp f.left x.left _).symm (fnR_comp f.left t.left _).symm

def chi : Γ((GD k D ⊗ TE k D).left, ⊤) := P (fst _ _) (snd _ _)

def chiU : Γ((GD k D ⊗ TE k D).left, ⊤)ˣ where
  val := chi
  inv := P (fst _ _)⁻¹ (snd _ _)
  val_inv := by rw [chi, ← twoPow_mul_twoPow, mul_inv_cancel, P_one]
  inv_val := by rw [chi, ← twoPow_mul_twoPow, inv_mul_cancel, P_one]

end Aff

section Main

open scoped TensorProduct
open Coalgebra WithConv

variable {k : Type} [Field k]

end Main

end GlobalTheory.CompanionTheory.KerPull.Cartier
end
end

