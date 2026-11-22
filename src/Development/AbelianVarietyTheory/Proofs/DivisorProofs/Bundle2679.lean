import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2562
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesO1OfProjectiveRankCup
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDualStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianDeRham_poincareDuality_of_cube_dual : GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham.Free → GlobalTheory.Published.AbelianDeRham.Duality := by
  first | exact @GlobalTheory.CubeDual.abelianDeRham_duality | exact GlobalTheory.CubeDual.abelianDeRham_duality | (intros; apply GlobalTheory.CubeDual.abelianDeRham_duality <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftDeRhamUniqueStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_lift_crystalline_comparison : GlobalTheory.Published.GrothendieckDeformation → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I),
    IsNilDP κ → ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
      (h : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (O : Type) [CommRing O] (a₀ : OAct O A₀), (∀ (x : O), ∀ d ∈ liftFil κ h, act κ (spMap π) a₀ x d ∈ liftFil κ h) →
      ∃ a : OAct O A, ∀ x, (a₀.act x).left ≫ i = i ≫ (a.act x).left := by
  first | exact @GlobalTheory.OActLift.exists_oAct_lift | exact GlobalTheory.OActLift.exists_oAct_lift | (intros; apply GlobalTheory.OActLift.exists_oAct_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftReductionStandardFactsStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianLift_reduction_standard_facts : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → AllPrim (dp0 R) (𝟙 _) A' ∧ AllPrim (dp0 R₀) (𝟙 _) A₀ ∧ AllPrim (divided₂ hI) (spMap π) A₀ ∧ Function.Bijective (liftMor (divided₂ hI) h').pull ∧ Module.Finite R (Cr hI π A₀.hom) ∧ Module.Projective R (Cr hI π A₀.hom) ∧ IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension g A₀.hom := by
  first | exact @GlobalTheory.LiftSys.abelianLift_facts | exact GlobalTheory.LiftSys.abelianLift_facts | (intros; apply GlobalTheory.LiftSys.abelianLift_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianOfFieldExtensionPullbackProper
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem abelian_of_field_of_pullback : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (G : Over (Sp K)) [GrpObj G] (B : Over (Sp K')) [GrpObj B] (φ : B.left ⟶ G.left) (g : ℕ), IsSemiAbelian G → IsGrpPullback B G (spMap i) φ → IsProper B.hom → SmoothOfRelativeDimension g B.hom → IsAbelianScheme G ∧ SmoothOfRelativeDimension g G.hom := by
  intro K K' _ _ i G _ B _ φ g hG h hP hB
  have hc := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  have : Flat (spMap i) := inferInstance
  have : Surjective (spMap i) := inferInstance
  have : UniversallyClosed G.hom := MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.1.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have hp : IsProper G.hom := ⟨⟩
  have : ConnectedSpace G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := G.hom) (𝟙 _) (𝟙 _) G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected G.hom (eSec G (default : PrimeSpectrum K))
  have hd' : SmoothOfRelativeDimension d B.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback h.1 hd
  have e : d = g := ReciprocityTheory.ChartRestriction.G.H1.dim_unique B.hom hd' hB (eSec B (default : PrimeSpectrum K'))
  subst e
  exact ⟨⟨hc, inferInstance, hp, inferInstance⟩, hd⟩

end GlobalTheory.Mum.GenDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentDataChartsCommonStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeDescentData_charts_common : ∀ σ : Setup, σ.Common := by
  first | exact @GlobalTheory.Desc.setup_common | exact GlobalTheory.Desc.setup_common | (intros; apply GlobalTheory.Desc.setup_common <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeEndomorphismExtOfDensePoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory

theorem abelianScheme_end_ext_of_dense : ∀ (W : Scheme.{0}) [IsIntegral W] (G : Over W) [GrpObj G], IsAbelianScheme G → ∀ (Ω : Type) [Field Ω] (pt : Sp Ω ⟶ W), Dense (Set.range pt) → ∀ (f f' : G ⟶ G), pullback.fst G.hom pt ≫ f.left = pullback.fst G.hom pt ≫ f'.left → f = f' := by
  intro W _ G _ hG Ω _ pt hpt f f' h
  have : Smooth G.hom := hG.smooth
  have : IsProper G.hom := hG.proper
  have : IsDominant pt := ⟨hpt⟩
  have : QuasiCompact pt := inferInstance
  have := IsSchemeTheoreticallyDominant.of_isDominant pt
  have : IsSchemeTheoreticallyDominant (pullback.fst G.hom pt) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback G.hom pt).flip
  exact Over.OverMorphism.ext (ext_of_schDom G.hom ((Over.w f).trans (Over.w f').symm)
    (pullback.fst G.hom pt) h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHodgeFiltrationFunctionalExtends
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem exists_extend_hodgeFiltration_functional_split {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hO : Function.Injective (cmpO s)) (h1 : Function.Surjective (cmp1 s))
    (hsurj : Function.Surjective (toHO1 s)) [Module.Projective R (HO1 s)]
    (ψ : F1 s →ₗ[R] R) : ∃ H : FirstDeRham s →ₗ[R] R, ∀ c : F1 s, H c = ψ c := by
  let f : FirstDeRham s →ₗ[R] HO1 s := (toHO1 s).comp (cmp1 s)
  have hf : Function.Surjective f := hsurj.comp h1
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hker : ∀ c : FirstDeRham s, f c = 0 ↔ c ∈ F1 s := fun c ↦ by
    change toHO1 s (cmp1 s c) = 0 ↔ toH1O s c = 0
    rw [structureSheaf_comparison_comm]
    exact ⟨fun h ↦ hO (h.trans (map_zero _).symm), fun h ↦ by rw [h, map_zero]⟩
  let p : FirstDeRham s →ₗ[R] F1 s := LinearMap.codRestrict (F1 s) (LinearMap.id - σ.comp f) fun c ↦ by
    rw [← hker]
    have : f (σ (f c)) = f c := LinearMap.congr_fun hσ (f c)
    simp [this]
  refine ⟨ψ.comp p, fun c ↦ ?_⟩
  have hc : f c = 0 := (hker c).2 c.2
  have : p c = c := Subtype.ext (by simp [p, hc])
  simp [this]

end GlobalTheory.CechDR

namespace GlobalTheory.AbelianExtend

open GlobalTheory.CechDR

theorem abelianScheme_hodgeFiltration_functional_extends' : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R]
    (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ ψ : F1 (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R, ∃ H : FirstDeRham (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R,
      ∀ c : F1 (A.hom ≫ 𝟙 (Sp R)), H c = ψ c := by
  intro hC hH R _ A _ g hab hdim ψ
  obtain ⟨-, -, -, ⟨-, hproj, -⟩, ⟨-, -, hsurj⟩, -⟩ := hH R A g hab hdim
  haveI := hab.smooth
  haveI := hab.proper
  have hsm : Smooth (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have hsep : IsSeparated (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have hqc : QuasiCompact (A.hom ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; infer_instance
  have h1 := (GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth hC R A.left (A.hom ≫ 𝟙 (Sp R)) hsm hsep hqc).1.2
  have hO := GlobalTheory.T.structure_sheaf_comparison_injective R A.left (A.hom ≫ 𝟙 (Sp R))
  have hs' : Function.Surjective (toHO1 (A.hom ≫ 𝟙 (Sp R))) := by rw [Category.comp_id]; exact hsurj
  haveI : Module.Projective R (HO1 (A.hom ≫ 𝟙 (Sp R))) := by rw [Category.comp_id]; exact hproj
  exact GlobalTheory.CechDR.exists_extend_hodgeFiltration_functional_split _ hO h1 hs' ψ

end GlobalTheory.AbelianExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomEqOfKerLeOfNilpotentReductionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_hom_eq_of_ker_le_of_nilpotent_reduction : ∀ (A κ : Type) [CommRing A] [CommRing κ] (π : A →+* κ), Function.Surjective π → IsNilpotent (RingHom.ker π) → ∀ (G B : Over (Sp A)) [GrpObj G] [GrpObj B], IsAbelianScheme B → ∀ (q₁ q₂ : G ⟶ B), IsMonHom q₁ → IsMonHom q₂ → Flat q₁.left → Surjective q₁.left → QuasiCompact q₁.left → (∀ (T : Over (Sp A)) (x : T ⟶ G), x ≫ q₁ = 1 → x ≫ q₂ = 1) → pullback.fst G.hom (spMap π) ≫ q₁.left = pullback.fst G.hom (spMap π) ≫ q₂.left → q₁ = q₂ := by
  first | exact @GlobalTheory.Mum.QuotEq.eq_of_ker_le_of_reduction | exact GlobalTheory.Mum.QuotEq.eq_of_ker_le_of_reduction | (intros; apply GlobalTheory.Mum.QuotEq.eq_of_ker_le_of_reduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLiftAlongNilpotentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_lift_along_split_surjection : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀) (s : R₀ →+* R), π.comp s = RingHom.id R₀ →
    ∀ (A₀ : Over (Sp R₀)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom →
      ∃ (A : Over (Sp R)) (_ : GrpObj A) (i : A₀.left ⟶ A.left) (_ : IsGrpPullback A₀ A (spMap π) i),
        IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom := by
  first | exact @GlobalTheory.abelianScheme_constLift | exact GlobalTheory.abelianScheme_constLift | (intros; apply GlobalTheory.abelianScheme_constLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePresentedBySystemStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_presented_by_system : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ S : Sys I π A₀.hom, S.Presents A'.hom i' → S.Full hI ∧ ∃ N, IsCompl (S.K hI) N := by
  first | exact @GlobalTheory.LiftSys.full_and_isCompl | exact GlobalTheory.LiftSys.full_and_isCompl | (intros; apply GlobalTheory.LiftSys.full_and_isCompl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareGlobalOneFormEqZeroOfAxes
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AbCoh.AxesForm

open GlobalTheory.AbCoh.PrimForm

theorem eq_zero_of_axes : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ y : GlobForm (A ⊗ A).hom, GlobalTheory.AbCoh.pF (lift (𝟙 A) (toUnit A ≫ η[A])) y = 0 → GlobalTheory.AbCoh.pF (lift (toUnit A ≫ η[A]) (𝟙 A)) y = 0 → y = 0 := by
  intro R _ A _ g hA hg y h₁ h₂
  obtain ⟨hA2, hg2⟩ := (GlobalTheory.T.abelian_square_affine_h1_vanish R).1 A g hA hg
  obtain ⟨f1, p1, r1⟩ := GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hg
  obtain ⟨f2, p2, r2⟩ := GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R (A ⊗ A) (g + g) hA2 hg2
  let N : GlobForm (A ⊗ A).hom →ₗ[R] GlobForm A.hom × GlobForm A.hom :=
    LinearMap.prod (pF (lift (𝟙 A) (toUnit A ≫ η[A]))) (pF (lift (toUnit A ≫ η[A]) (𝟙 A)))
  let P : GlobForm A.hom × GlobForm A.hom →ₗ[R] GlobForm (A ⊗ A).hom :=
    LinearMap.coprod (pF (fst A A)) (pF (snd A A))
  have hNP : N ∘ₗ P = LinearMap.id := by
    refine LinearMap.ext fun x ↦ Prod.ext ?_ ?_
    · show pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (fst A A) x.1 + pF (snd A A) x.2) = x.1
      rw [map_add, pF_comp, pF_comp, lift_fst, lift_snd, pF_id, pF_unit, add_zero]
    · show pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (fst A A) x.1 + pF (snd A A) x.2) = x.2
      rw [map_add, pF_comp, pF_comp, lift_fst, lift_snd, pF_id, pF_unit, zero_add]
  have hinj := GlobalTheory.Obs.Axes.injective_of_section N P hNP (fun p ↦ by
    rw [Module.rankAtStalk_prod, Pi.add_apply, r1, r2])
  refine hinj (?_ : N y = N 0)
  rw [map_zero]
  exact Prod.ext h₁ h₂

end GlobalTheory.AbCoh.AxesForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleBundlesDescendFgSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.AbFGSpread

theorem sym_transfer {X Y : Scheme.{0}} {L : LB X} {N : LB Y} (hL : L.IsLB) (hN : N.IsLB) (jX : X ⟶ X)
    (jj : Y ⟶ Y) (φ : Y ⟶ X) (e : jj ≫ φ = φ ≫ jX) (hw : LBIso N (L.pull φ)) (hs : LBIso (N.pull jj) N) :
    LBIso ((L.pull jX).pull φ) (L.pull φ) := by
  have h1 : LBIso ((L.pull jX).pull φ) (L.pull (jj ≫ φ)) := by
    rw [e]; exact (FibreNef.lbIso_pull_comp hL jX φ).symm
  have h2 : LBIso (L.pull (jj ≫ φ)) ((L.pull φ).pull jj) := FibreNef.lbIso_pull_comp hL φ jj
  have h3 : LBIso ((L.pull φ).pull jj) (N.pull jj) := RigidBundleGlue.LBIso.pull hw.symm jj
  have p := fun (f : Y ⟶ X) => pull_isLB hL f
  refine LBIso.trans (pull_isLB (pull_isLB hL jX) φ) (p _) (p φ) h1 ?_
  refine LBIso.trans (p _) (pull_isLB (p φ) _) (p φ) h2 ?_
  refine LBIso.trans (pull_isLB (p φ) _) (pull_isLB hN _) (p φ) h3 ?_
  exact LBIso.trans (pull_isLB hN _) hN (p φ) hs hw

theorem sym_of_pull {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (jX : X ⟶ X) (jj : Y ⟶ Y) (φ : Y ⟶ X)
    (e : jj ≫ φ = φ ≫ jX) (hs : LBIso ((L.pull jX).pull φ) (L.pull φ)) :
    LBIso ((L.pull φ).pull jj) (L.pull φ) := by
  have p := fun {Z : Scheme.{0}} (f : Z ⟶ X) => pull_isLB hL f
  have h1 : LBIso ((L.pull φ).pull jj) (L.pull (jj ≫ φ)) := (FibreNef.lbIso_pull_comp hL φ jj).symm
  have h2 : LBIso (L.pull (jj ≫ φ)) ((L.pull jX).pull φ) := by
    rw [e]; exact FibreNef.lbIso_pull_comp hL jX φ
  refine LBIso.trans (pull_isLB (p φ) _) (p _) (p φ) h1 ?_
  exact LBIso.trans (p _) (pull_isLB (p jX) _) (p φ) h2 hs

theorem spread_to_fg_subfield : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → ∃ (k₀ : IntermediateField ℚ K) (A₀ : Over (Sp k₀)) (_ : GrpObj A₀) (π : A.left ⟶ A₀.left) (L₀ M₀ : LB A₀.left), k₀.FG ∧ IsAbelianScheme A₀ ∧ IsGrpPullback A A₀ (spMap (algebraMap k₀ K)) π ∧ L₀.IsLB ∧ M₀.IsLB ∧ RelAmple A₀ L₀ ∧ RelAmple A₀ M₀ ∧ LBIso (L₀.pull (GrpObj.inv : A₀ ⟶ A₀).left) L₀ ∧ LBIso (M₀.pull (GrpObj.inv : A₀ ⟶ A₀).left) M₀ ∧ LBIso L (L₀.pull π) ∧ LBIso M (M₀.pull π) := by
  intro K _ _ A _ hA L M hL hM hLa hMa hLs hMs
  classical
  obtain ⟨s₀, H₀⟩ := GlobalTheory.exists_finset_isProjOver_descends K ⊥ A.left A.hom
    (GlobalTheory.ProjSpace.isProjOver_of_relAmple hLa)
  let K₀ : Subfield K := Subfield.closure (s₀ : Set K)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ K₀ bot_le Subfield.subset_closure
  have : IsProper p₀ := by
    obtain ⟨N, i, hi, rfl⟩ := hp₀
    have := isProper_str K₀ N
    infer_instance
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := GlobalTheory.grpObj_descends_to_large_subfield K K₀ (Over.mk p₀) A φ sq
  obtain ⟨s₂, H₂⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ A.left p₀ A.hom φ L hL sq
  obtain ⟨s₃, H₃⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ A.left p₀ A.hom φ M hM sq
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃
  let K₁ : Subfield K := Subfield.closure (s : Set K)
  have sub : ∀ t : Finset K, t ⊆ s → (t : Set K) ⊆ K₁ := fun t ht =>
    PolCountableDescent.subset_closure_of_subset ht
  have h : K₀ ≤ K₁ := Subfield.closure_mono (Finset.coe_subset.2 (fun y hy => by simp [s, hy]))
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp K₁) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : A.left ⟶ A₁.left := sq₁.lift φ (A.hom ≫ spMap K₁.subtype)
    (by rw [Category.assoc, PolCountableDescent.spMap_subtype_comp h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = A.hom ≫ spMap K₁.subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ K₁ h (sub s₁ (fun y hy => by simp [s, hy])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hLL⟩ := H₂ K₁ h (sub s₂ (fun y hy => by simp [s, hy])) A₁.left A₁.hom φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨M₁, hM₁, hMM⟩ := H₃ K₁ h (sub s₃ (fun y hy => by simp [s, hy])) A₁.left A₁.hom φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨hab₁, -⟩ := GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend K₁ K K₁.subtype A₁ A ψ hG hA
  have : IsProper A₁.hom := hab₁.proper
  have e₁ := PolDescent.inv_left_comp hG
  have symL := sym_transfer hL₁ hL _ _ ψ e₁ hLL hLs
  have symM := sym_transfer hM₁ hM _ _ ψ e₁ hMM hMs
  obtain ⟨s₄, H₄⟩ := lbIso_descends_to_subfield_containing_finset K₁ K K₁.subtype A₁ A ψ _ L₁ hG.1
    inferInstance inferInstance (pull_isLB hL₁ _) hL₁ symL
  obtain ⟨s₅, H₅⟩ := lbIso_descends_to_subfield_containing_finset K₁ K K₁.subtype A₁ A ψ _ M₁ hG.1
    inferInstance inferInstance (pull_isLB hM₁ _) hM₁ symM
  let t : Finset K := s ∪ s₄ ∪ s₅
  let k₀ : IntermediateField ℚ K := IntermediateField.adjoin ℚ (t : Set K)
  let K₂ : Subfield K := k₀.toSubfield
  have mem₂ : ∀ y ∈ t, y ∈ K₂ := fun y hy => IntermediateField.subset_adjoin ℚ (t : Set K) hy
  have h₁₂ : K₁ ≤ K₂ := Subfield.closure_le.2 (fun y hy => mem₂ y (by simp [t, Finset.mem_coe.1 hy]))
  have rng : ∀ u : Finset K, u ⊆ t → (u : Set K) ⊆ Set.range K₂.subtype := fun u hu y hy =>
    ⟨⟨y, mem₂ y (hu hy)⟩, rfl⟩
  let inc₂ := spMap (Subfield.inclusion h₁₂)
  let A₂ : Over (Sp K₂) := (Over.pullback inc₂).obj A₁
  have hP : IsGrpPullback A₂ A₁ inc₂ (pullback.fst A₁.hom inc₂) := isGrpPullback_pullback A₁ inc₂
  let χ : A₂.left ⟶ A₁.left := pullback.fst A₁.hom inc₂
  let π : A.left ⟶ A₂.left := pullback.lift ψ (A.hom ≫ spMap K₂.subtype)
    (by rw [hψ₂, Category.assoc, PolCountableDescent.spMap_subtype_comp h₁₂])
  have hπ₁ : π ≫ χ = ψ := pullback.lift_fst _ _ _
  have hπ₂ : π ≫ A₂.hom = A.hom ≫ spMap K₂.subtype := pullback.lift_snd _ _ _
  have hG₂ : IsGrpPullback A A₂ (spMap K₂.subtype) π :=
    IsGrpPullback.cancel hP (by rw [PolCountableDescent.spMap_subtype_comp h₁₂, hπ₁]; exact hG) hπ₂
  obtain ⟨hab₂, -⟩ := GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend K₂ K K₂.subtype A₂ A π hG₂ hA
  have e₂ := PolDescent.inv_left_comp hP
  have symL₂ := H₄ K₂ (Subfield.inclusion h₁₂) K₂.subtype rfl (rng s₄ (fun y hy => by simp [t, hy]))
    A₂ χ hP.1
  have symM₂ := H₅ K₂ (Subfield.inclusion h₁₂) K₂.subtype rfl (rng s₅ (fun y hy => by simp [t, hy]))
    A₂ χ hP.1
  have isoL : LBIso L ((L₁.pull χ).pull π) := by
    refine LBIso.trans hL (pull_isLB hL₁ _) (pull_isLB (pull_isLB hL₁ _) _) hLL ?_
    rw [← hπ₁]; exact FibreNef.lbIso_pull_comp hL₁ χ π
  have isoM : LBIso M ((M₁.pull χ).pull π) := by
    refine LBIso.trans hM (pull_isLB hM₁ _) (pull_isLB (pull_isLB hM₁ _) _) hMM ?_
    rw [← hπ₁]; exact FibreNef.lbIso_pull_comp hM₁ χ π
  refine ⟨k₀, A₂, inferInstance, π, L₁.pull χ, M₁.pull χ, ⟨t, rfl⟩, hab₂, hG₂, pull_isLB hL₁ _,
    pull_isLB hM₁ _, ?_, ?_, sym_of_pull hL₁ _ _ χ e₂ symL₂, sym_of_pull hM₁ _ _ χ e₂ symM₂, isoL, isoM⟩
  · exact AmpleDescent.relAmple_of_fieldExtension K₂ K K₂.subtype A₂ A π _ L hab₂ hG₂ (pull_isLB hL₁ _) hL isoL hLa
  · exact AmpleDescent.relAmple_of_fieldExtension K₂ K K₂.subtype A₂ A π _ M hab₂ hG₂ (pull_isLB hM₁ _) hM isoM hMa

end GlobalTheory.AbFGSpread
end
end

