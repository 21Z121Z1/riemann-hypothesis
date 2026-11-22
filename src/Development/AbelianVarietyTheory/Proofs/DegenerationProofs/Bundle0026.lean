import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyAutomorphismShiftsJacobianOrder
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProductFormulaPlacesFunctionField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfDefectZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyAutomorphismShiftsJacobianOrderStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_automorphism_shifts_jacobianOrder : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ f : A ≅ A, ∃ c : ℤ, ∀ (M : Model R A) (n : ℤ), HasOrd M D π n → HasOrd (M.twist f) D π (n + c) := by
  first | exact @GlobalTheory.SS.OrdTwist.main | exact GlobalTheory.SS.OrdTwist.main | (intros; apply GlobalTheory.SS.OrdTwist.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DefectBoundedStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_defect_bound_of_smooth_away : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R), Irreducible π → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B], Algebra.Smooth R (Localization.Away (algebraMap R B π)) → ∃ c : ℕ, ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (a : B →ₐ[R] R'), Defect a π c := by
  first | exact @GlobalTheory.SS.defect_bounded | exact GlobalTheory.SS.defect_bounded | (intros; apply GlobalTheory.SS.defect_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineUnitChartSmoothGroupScheme
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
namespace GlobalTheory.SS.ArcInf

theorem exists_isChart : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (j : algOver k A ⟶ G) (ε : A →ₐ[k] k) (r : ℕ) (f : Fin r → A), IsChart G j ε f := by
  intro k _ G _ hG
  have hs : Smooth G.hom := hG.2.1
  let e : algOver k k ⟶ G := 1
  let x0 : (Sp k) := IsLocalRing.closedPoint k
  obtain ⟨R, i, hi, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := G.left) (x := e.left x0) (U := ⊤) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ G.hom : Spec R ⟶ Spec (CommRingCat.of k))
  letI : Algebra k R := φ.hom.toAlgebra
  have hft : Algebra.FiniteType k R := by
    have h1 : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h1
  let j : algOver k R ⟶ G := Over.homMk i hφ.symm
  have hr : Set.range e.left ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    have : y = x0 := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [this]; exact hx
  let l : algOver k k ⟶ algOver k R := Over.homMk (IsOpenImmersion.lift i e.left hr) (by
    have := Over.w e
    rw [← this]
    show _ ≫ Spec.map φ = _
    rw [hφ, IsOpenImmersion.lift_fac_assoc])
  obtain ⟨ε, hε⟩ := algOverHom_surjective l
  obtain ⟨s, hsg⟩ := hft.out
  refine ⟨R, inferInstance, inferInstance, j, ε, s.card,
    fun n => (s.equivFin.symm n : R) - algebraMap k R (ε (s.equivFin.symm n)), hi, ?_, ?_, ?_⟩
  · rw [hε]
    ext1
    exact IsOpenImmersion.lift_fac i e.left hr
  · rw [eq_top_iff, ← hsg, Algebra.adjoin_le_iff]
    intro a ha
    have h1 : a - algebraMap k R (ε a) ∈ Algebra.adjoin k (Set.range fun n =>
        (s.equivFin.symm n : R) - algebraMap k R (ε (s.equivFin.symm n))) :=
      Algebra.subset_adjoin ⟨s.equivFin ⟨a, ha⟩, by simp⟩
    have h2 := add_mem h1 (Subalgebra.algebraMap_mem _ (ε a))
    simpa using h2
  · intro n
    simp

end GlobalTheory.SS.ArcInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAlgHomLocalizationAwayOfRationalPointsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algHom_localizationAway_of_rational_points' : ∀ (k : Type) [Field k] [Infinite k] (A : Type) [CommRing A] [Algebra k A] (r : ℕ) (f : Fin r → A) (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)), Algebra.adjoin k (Set.range f) = ⊤ → Pd ≠ 0 → (∀ t, t ≠ 0 → Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) → ∃ χ : A →ₐ[k] Localization.Away (Polynomial.X * Pd), ∀ i, χ (f i) * algebraMap (Polynomial k) _ Pd = algebraMap (Polynomial k) _ (P i) := by
  first | exact @GlobalTheory.exists_algHom_localizationAway_of_rational_points | exact GlobalTheory.exists_algHom_localizationAway_of_rational_points | (intros; apply GlobalTheory.exists_algHom_localizationAway_of_rational_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasicOpenFactorFieldPointAffineOpen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
noncomputable section
namespace GlobalTheory.SS.ArcInf

theorem exists_basicOpen_factor : ∀ (k : Type) [CommRing k] (G : Over (Sp k)) (A B F : Type) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Field F] [Algebra k F] (j : algOver k A ⟶ G) (φ : algOver k B ⟶ G) (δ : B →ₐ[k] F) (χ₀ : A →ₐ[k] F), IsOpenImmersion j.left → algOverHom δ ≫ φ = algOverHom χ₀ ≫ j → ∃ e : B, δ e ≠ 0 ∧ ∀ (B' : Type) [CommRing B'] [Algebra k B'] (ρ : B →ₐ[k] B'), IsUnit (ρ e) → ∃ χ : A →ₐ[k] B', algOverHom χ ≫ j = algOverHom ρ ≫ φ := by
  intro k _ G A B F _ _ _ _ _ _ j φ δ χ₀ hj h
  let U : (Spec (CommRingCat.of B)).Opens := φ.left ⁻¹ᵁ j.left.opensRange
  let p₀ : PrimeSpectrum F := ⟨⊥, Ideal.isPrime_bot⟩
  let p : PrimeSpectrum B := PrimeSpectrum.comap (δ : B →+* F) p₀
  have hl : (algOverHom δ).left ≫ φ.left = (algOverHom χ₀).left ≫ j.left := by
    have := congrArg (fun x => x.left) h
    simpa only [Over.comp_left] using this
  have hp : p ∈ (U : Set (Spec (CommRingCat.of B))) := by
    refine ⟨(algOverHom χ₀).left p₀, ?_⟩
    have := congrArg (fun x => x p₀) hl
    simp only [Scheme.Hom.comp_apply] at this
    exact this.symm
  obtain ⟨_, ⟨e, rfl⟩, he, heU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp U.isOpen
  refine ⟨e, fun h0 => he (show δ e ∈ (⊥ : Ideal F) from h0), ?_⟩
  intro B' _ _ ρ hρ
  have hr : Set.range ((algOverHom ρ).left ≫ φ.left) ⊆ Set.range j.left := by
    rintro _ ⟨q, rfl⟩
    have hq : PrimeSpectrum.comap (ρ : B →+* B') q ∈ PrimeSpectrum.basicOpen e := by
      intro hm
      exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ (show ρ e ∈ q.asIdeal from hm) hρ)
    rw [Scheme.Hom.comp_apply]
    exact heU hq
  have hf := IsOpenImmersion.lift_fac j.left ((algOverHom ρ).left ≫ φ.left) hr
  let ψ : algOver k B' ⟶ algOver k A :=
    Over.homMk (IsOpenImmersion.lift j.left ((algOverHom ρ).left ≫ φ.left) hr) (by
      rw [← Over.w j, ← Category.assoc, hf, Category.assoc, Over.w φ, Over.w (algOverHom ρ)])
  obtain ⟨χ, hχ⟩ := algOverHom_surjective ψ
  refine ⟨χ, ?_⟩
  rw [hχ]
  ext1
  exact hf

end GlobalTheory.SS.ArcInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorOfRangeSubset
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory.SS.ArcInf
namespace GlobalTheory.SS.ArcInf

theorem exists_factor_of_range_subset {k : Type} [CommRing k] {G : Over (Sp k)} {A B : Type} [CommRing A]
    [Algebra k A] [CommRing B] [Algebra k B] (j : algOver k A ⟶ G) (hj : IsOpenImmersion j.left)
    (a : algOver k B ⟶ G) (hr : Set.range a.left ⊆ Set.range j.left) :
    ∃ χ : A →ₐ[k] B, algOverHom χ ≫ j = a := by
  have hf := IsOpenImmersion.lift_fac j.left a.left hr
  let l : algOver k B ⟶ algOver k A := Over.homMk (IsOpenImmersion.lift j.left a.left hr) (by
    rw [← Over.w j, ← Category.assoc, hf, Over.w a])
  obtain ⟨χ, hχ⟩ := algOverHom_surjective l
  refine ⟨χ, ?_⟩
  rw [hχ]
  ext1
  exact hf

theorem exists_extend_of_localSubring : ∀ (k : Type) [CommRing k] (G : Over (Sp k)) (O K F : Type) [CommRing O] [Algebra k O] [Field K] [Algebra k K] [Field F] [Algebra k F] (em : O →ₐ[k] K) (σ : K →ₐ[k] F) (L : Subalgebra k F), IsLocalRing L → Function.Injective em → (∀ x, σ x ∈ L → x ∈ Set.range em) → ∀ (a : algOver k K ⟶ G) (b' : algOver k L ⟶ G), algOverHom σ ≫ a = algOverHom L.val ≫ b' → ∃ b : algOver k O ⟶ G, algOverHom em ≫ b = a := by
  intro k _ G O K F _ _ _ _ _ _ em σ L hL hem hsub a b' hab
  let x0 : (Sp L) := IsLocalRing.closedPoint L
  obtain ⟨R, i, hi, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := G.left)
    (x := b'.left x0) (U := ⊤) trivial
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ G.hom : Spec R ⟶ Spec (CommRingCat.of k))
  letI : Algebra k R := φ.hom.toAlgebra
  let j : algOver k R ⟶ G := Over.homMk i hφ.symm
  have hj : IsOpenImmersion j.left := hi
  have hrb : Set.range b'.left ⊆ Set.range j.left := by
    rintro _ ⟨y, rfl⟩
    have hs : y ⤳ x0 := IsLocalRing.specializes_closedPoint (R := L) y
    have hs' := hs.map b'.left.continuous
    exact hs'.mem_open j.left.isOpenEmbedding.isOpen_range hx
  have hra : Set.range a.left ⊆ Set.range j.left := by
    rintro _ ⟨y, rfl⟩
    let p : (Sp F) := IsLocalRing.closedPoint F
    have hy : y = (algOverHom σ).left p := Subsingleton.elim (α := PrimeSpectrum K) _ _
    have hl : (algOverHom σ).left ≫ a.left = (algOverHom L.val).left ≫ b'.left := by
      rw [← Over.comp_left, ← Over.comp_left, hab]
    apply hrb
    refine ⟨(algOverHom L.val).left p, ?_⟩
    rw [hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hl]
  obtain ⟨χL, hχL⟩ := exists_factor_of_range_subset j hj b' hrb
  obtain ⟨χK, hχK⟩ := exists_factor_of_range_subset j hj a hra
  have hc : σ.comp χK = L.val.comp χL := by
    apply eq_of_comp_eq hj
    rw [algOverHom_comp, algOverHom_comp, Category.assoc, Category.assoc, hχK, hχL, hab]
  have hmem : ∀ x, χK x ∈ em.range := fun x => by
    apply hsub
    have : σ (χK x) = (χL x : F) := DFunLike.congr_fun hc x
    rw [this]
    exact (χL x).2
  let χO : R →ₐ[k] O :=
    ((AlgEquiv.ofInjective em hem).symm : em.range →ₐ[k] O).comp (χK.codRestrict em.range hmem)
  have hO : em.comp χO = χK := by
    ext x
    have := AlgEquiv.ofInjective_apply em hem ((AlgEquiv.ofInjective em hem).symm ⟨χK x, hmem x⟩)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨algOverHom χO ≫ j, ?_⟩
  rw [← Category.assoc, ← algOverHom_comp, hO, hχK]

end GlobalTheory.SS.ArcInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValuesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_of_definition_of_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (x : Sp Ω ⟶ X), ∃ E : Subfield Ω, (∀ τ τ' : Ω →+* Ω, spMap τ ≫ x = spMap τ' ≫ x ↔ ∀ c ∈ E, τ c = τ' c) ∧ (∀ (K' : Type) [Field K'] (j : K' →+* Ω), E ≤ j.fieldRange ↔ ∃ y : Sp K' ⟶ X, spMap j ≫ y = x) ∧ ∀ (K : Type) [Field K] [Algebra K Ω] (s : X ⟶ Sp K), LocallyOfFiniteType s → x ≫ s = spMap (algebraMap K Ω) → Algebra.IsAlgebraic K Ω → ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ L.toSubfield = E := by
  first | exact @GlobalTheory.SS.exists_fieldOfValues | exact GlobalTheory.SS.exists_fieldOfValues | (intros; apply GlobalTheory.SS.exists_fieldOfValues <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFinsetModelOfIsAffine
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_finset_isPushout_model (K A : Type) [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] :
    ∃ s : Finset K, ∀ (k : Type) [Field k] (β : k →+* K), (s : Set K) ⊆ Set.range β →
      ∃ (A₀ : CommRingCat.{0}) (f : CommRingCat.of k ⟶ A₀) (g : A₀ ⟶ CommRingCat.of A),
        IsPushout f (CommRingCat.ofHom β) g (CommRingCat.ofHom (algebraMap K A)) := by
  haveI : Algebra.FinitePresentation K A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let P := Algebra.Presentation.ofFinitePresentation K A
  refine ⟨P.finite_coeffs.toFinset, fun k _ β hs => ?_⟩
  letI : Algebra k K := β.toAlgebra
  letI : Algebra k A := ((algebraMap K A).comp β).toAlgebra
  haveI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  haveI : P.HasCoeffs k := ⟨fun x hx => hs (by simpa using hx)⟩
  let e := P.tensorModelOfHasCoeffsEquiv k
  have h := (CommRingCat.isPushout_tensorProduct k K (P.ModelOfHasCoeffs k)).flip
  refine ⟨CommRingCat.of (P.ModelOfHasCoeffs k), CommRingCat.ofHom (algebraMap k _),
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom) ≫
      e.toRingEquiv.toCommRingCatIso.hom, ?_⟩
  refine h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso
    ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · ext x
    exact e.commutes x

theorem exists_finset_model_of_isAffine :
    ∀ (K : Type) [Field K] (X : Over (Sp K)), IsAffine X.left → LocallyOfFiniteType X.hom →
      ∃ s : Finset K, ∀ (k : Type) [Field k] (β : k →+* K), (s : Set K) ⊆ Set.range β →
        ∃ (X₀ : Over (Sp k)) (φ : X.left ⟶ X₀.left), IsPullback φ X.hom X₀.hom (spMap β) := by
  intro K _ X hX hft
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := CommRingCat.of K) (S := Γ(X.left, ⊤))
    (X.left.isoSpec.inv ≫ X.hom)
  have h1 : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h1
  letI : Algebra K Γ(X.left, ⊤) := ψ.hom.toAlgebra
  haveI : Algebra.FiniteType K Γ(X.left, ⊤) := h1
  obtain ⟨s, hs⟩ := exists_finset_isPushout_model K Γ(X.left, ⊤)
  refine ⟨s, fun k _ β hβ => ?_⟩
  obtain ⟨A₀, f, g, h⟩ := hs k β hβ
  have h2 : IsPullback (Spec.map g) (Spec.map ψ) (Spec.map f) (spMap β) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ h
  refine ⟨Over.mk (Spec.map f), X.left.isoSpec.hom ≫ Spec.map g, ?_⟩
  refine h2.of_iso X.left.isoSpec.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp [hψ]
  · simp
  · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProductFormulaPlacesFunctionFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_productFormulaPlaces_function_field : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (t : K), Transcendental k t → FiniteDimensional (IntermediateField.adjoin k {t}) K → Algebra.IsSeparable (IntermediateField.adjoin k {t}) K → ∃ Pl : Places k K, ∀ x : K, (∀ i, x ∈ Pl.O i) → IsAlgebraic k x := by
  first | exact @GlobalTheory.SS.PlacesExt.exists_places | exact GlobalTheory.SS.PlacesExt.exists_places | (intros; apply GlobalTheory.SS.PlacesExt.exists_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothFreeAwayStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_free_away' : ∀ (k C : Type) [Field k] [PerfectField k] [CommRing C] [Nontrivial C] [IsReduced C] [Algebra k C] [Algebra.FiniteType k C] (M : Type) [AddCommGroup M] [Module C M] [Module.Finite C M], ∃ f : C, f ≠ 0 ∧ Algebra.Smooth k (Localization.Away f) ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  first | exact @GlobalTheory.SS.exists_smooth_free_away | exact GlobalTheory.SS.exists_smooth_free_away | (intros; apply GlobalTheory.SS.exists_smooth_free_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfDefectZeroStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_of_defect_zero' : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R), Irreducible π → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B], Algebra.Smooth R (Localization.Away (algebraMap R B π)) → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), Unr π R' → Defect a π 0 → ∃ f : B, IsUnit (a f) ∧ Algebra.Smooth R (Localization.Away f) := by
  first | exact @GlobalTheory.SS.exists_smooth_of_defect_zero | exact GlobalTheory.SS.exists_smooth_of_defect_zero | (intros; apply GlobalTheory.SS.exists_smooth_of_defect_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelExtensionOfDefinedAtPointsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_model_extension_of_definedAtPoints : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A A' : Over (Sp K)) (M : Model R A) (N : Model R A') (f : A ⟶ A'), (∀ y, DefAt M N f y) → ∃! g : M.Y ⟶ N.Y, M.j ≫ g.left = f.left ≫ N.j := by
  first | exact @GlobalTheory.SS.existsUnique_extension_of_forall_defAt | exact GlobalTheory.SS.existsUnique_extension_of_forall_defAt | (intros; apply GlobalTheory.SS.existsUnique_extension_of_forall_defAt <;> assumption)
end

