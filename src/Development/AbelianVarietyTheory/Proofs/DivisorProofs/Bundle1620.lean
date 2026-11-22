import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0637
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeEndomorphismFiniteOfGeometricFibres
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbEnd

theorem isFinite_of_isFinite_geomFibres :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (φ : A ⟶ A),
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), IsFinite ((Over.pullback t).map φ).left) →
    IsFinite φ.left := by
  intro S A _ hA φ hgeo
  haveI : IsProper A.hom := hA.proper
  haveI : IsProper (φ.left ≫ A.hom) := by rw [Over.w φ]; infer_instance
  haveI : IsProper φ.left := IsProper.of_comp φ.left A.hom
  haveI : LocallyQuasiFinite φ.left := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton φ.left fun y => ?_
    let K := AlgebraicClosure (A.left.residueField y)
    let u : Spec (CommRingCat.of K) ⟶ A.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (A.left.residueField y) K)) ≫
        A.left.fromSpecResidueField y
    let t := u ≫ A.hom
    haveI := hgeo K t
    let φ' := ((Over.pullback t).map φ).left
    let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
    have hup : u p = y := Scheme.fromSpecResidueField_apply y _
    let v : Spec (CommRingCat.of K) ⟶ pullback A.hom t := pullback.lift u (𝟙 _) (by simp [t])
    refine ((φ'.finite_preimage_singleton (v p)).image (pullback.fst A.hom t)).subset fun x hx => ?_
    have hx' : φ.left x = u p := by rw [hup]; exact hx
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ.left) (g := u) x p hx'
    let m : pullback φ.left u ⟶ pullback A.hom t :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
        rw [← Over.w φ, ← Category.assoc, pullback.condition, Category.assoc])
    have hm1 : m ≫ pullback.fst A.hom t = pullback.fst _ _ := pullback.lift_fst _ _ _
    have hφ1 : φ' ≫ pullback.fst A.hom t = pullback.fst A.hom t ≫ φ.left :=
      (GlobalTheory.AbLaw.MulN.isPullback_baseChange t φ).w.symm
    have hφ2 : φ' ≫ pullback.snd A.hom t = pullback.snd A.hom t := pullback.lift_snd _ _ _
    have hmv : m ≫ φ' = pullback.snd φ.left u ≫ v := by
      apply pullback.hom_ext
      · rw [Category.assoc, hφ1, ← Category.assoc, hm1, Category.assoc, pullback.lift_fst, pullback.condition]
      · rw [Category.assoc, hφ2, pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
    refine ⟨m w, ?_, ?_⟩
    · change φ' (m w) = v p
      rw [← Scheme.Hom.comp_apply, hmv, Scheme.Hom.comp_apply, hw2]
    · rw [← Scheme.Hom.comp_apply, hm1, hw1]
  exact IsFinite.of_isProper_of_locallyQuasiFinite φ.left

end GlobalTheory.AbEnd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsPrimitive
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.AbCoh

theorem primF_of_abelian (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hs : SmoothOfRelativeDimension g A.hom) : PrimF A := by
  obtain ⟨-, -, hAA, hsAA⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs
  have hax := (GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A).2.1
  have hM : FP R (GlobForm A.hom × GlobForm A.hom) (g + g) :=
    (GlobalTheory.T.fgProjectiveConstantRank_extension_and_prod).2 R _ _ g g (GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hs) (GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hs)
  have hN : FP R (GlobForm (A ⊗ A).hom) (g + g) := GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R (A ⊗ A) (g + g) hAA hsAA
  let i₁ : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ η[A])
  let i₂ : A ⟶ A ⊗ A := lift (toUnit A ≫ η[A]) (𝟙 A)
  let f : (GlobForm A.hom × GlobForm A.hom) →ₗ[R] GlobForm (A ⊗ A).hom :=
    (pF (fst A A)).coprod (pF (snd A A))
  let r : GlobForm (A ⊗ A).hom →ₗ[R] (GlobForm A.hom × GlobForm A.hom) :=
    (pF i₁).prod (pF i₂)
  have hr : ∀ y, r y = (pF i₁ y, pF i₂ y) := fun y ↦ by simp [r, LinearMap.prod_apply, Function.prod]
  have hrf : ∀ x, r (f x) = x := by
    rintro ⟨a, b⟩
    obtain ⟨h1, h2, -, h4, h5, -⟩ := hax a
    obtain ⟨k1, k2, -, k4, k5, -⟩ := hax b
    have hf : f (a, b) = pF (fst A A) a + pF (snd A A) b := by simp [f]
    rw [hr, hf, map_add, map_add, h1, k2, h4, k5, add_zero, zero_add]
  have hbij := GlobalTheory.T.bijective_of_split_injective_fgProjectiveConstantRank R _ _ (g + g) hM hN f r hrf
  have hrinj : Function.Injective r := by
    intro y y' h
    obtain ⟨x, rfl⟩ := hbij.2 y
    obtain ⟨x', rfl⟩ := hbij.2 y'
    rw [hrf, hrf] at h; rw [h]
  intro x
  obtain ⟨-, -, h3, -, -, h6⟩ := hax x
  have e1 : r (pF μ[A] x) = (x, x) := (hr _).trans (Prod.ext h3 h6)
  exact (hrinj (e1.trans (hrf (x, x)).symm)).trans (LinearMap.coprod_apply _ _ _)

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsoLineBundleSectionsTransferStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_iso_line_bundle_sections_transfer : ∀ (K W K' : Type) [Field K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra K K'], ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, ∀ (H : LB A.left) (m : ℕ) (s₁ : Fin (m + 1) → H.Sec) (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) (N : ℕ) (t : Fin (N + 1) → M.Sec), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy A.hom H s₁ → M.IsLB → w.IsGen → (∀ u : M.Sec, ∃! c : Fin (N + 1) → W, u = ∑ j, GlobalTheory.AbLaw.cst G.hom ⊤ (c j) • t j) → ∃ (s : Fin (N + 1) → H.Sec) (g : Matrix (Fin (N + 1)) (Fin (N + 1)) K'), GlobalTheory.AbLaw.VeryAmpleBy A.hom H s ∧ IsUnit g.det ∧ (∀ j, GlobalTheory.Cartier.SecMaps w (GlobalTheory.Cartier.secPull (t j) (pullback.fst G.hom (spMap (algebraMap W K')))) (∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (g j k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))) ∧ ∀ c c' : Fin (N + 1) → K', ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (c k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) = ∑ k, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (c' k) • GlobalTheory.Cartier.secPull (s k) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) → c = c' := by
  first | exact @GlobalTheory.BasisMatch.exists_basis_match | exact GlobalTheory.BasisMatch.exists_basis_match | (intros; apply GlobalTheory.BasisMatch.exists_basis_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointTrivialOfGeometric
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionRigid

theorem eq_one_of_geometric (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (T : Over S) (x : T ⟶ A) (c : ℕ) (hc : IsUnit (c : Γ(T.left, ⊤)))
    (hx : x ^ c = 1)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (z : Sp k ⟶ S)
      (g : Over.mk z ⟶ T), g ≫ x = 1) : x = 1 := by
  have := hA.smooth
  let AT := (Over.pullback T.hom).obj A
  have hft : LocallyOfFiniteType AT.hom := by
    change LocallyOfFiniteType (pullback.snd A.hom T.hom); infer_instance
  let f := ((Over.pullback T.hom).map (mulN A c)).left
  have hfu : FormallyUnramified f := by
    have h := GlobalTheory.GrpTangent.formallyUnramified_mulN AT hc
    rw [← GlobalTheory.GrpTangent.pullback_map_mulN] at h
    exact h
  have hff : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ AT.hom) := by
      rw [show f ≫ AT.hom = AT.hom from Over.w ((Over.pullback T.hom).map (mulN A c))]
      infer_instance
    exact locallyOfFiniteType_of_comp f AT.hom
  let sec : (T ⟶ A) → (T.left ⟶ AT.left) := fun y =>
    pullback.lift y.left (𝟙 T.left) (by rw [Over.w y, Category.id_comp])
  have sec_fst : ∀ y : T ⟶ A, sec y ≫ pullback.fst A.hom T.hom = y.left := fun y =>
    pullback.lift_fst _ _ _
  have sec_snd : ∀ y : T ⟶ A, sec y ≫ pullback.snd A.hom T.hom = 𝟙 _ := fun y =>
    pullback.lift_snd _ _ _
  have f_fst : f ≫ pullback.fst A.hom T.hom = pullback.fst A.hom T.hom ≫ (mulN A c).left :=
    pullback.lift_fst _ _ _
  have f_snd : f ≫ pullback.snd A.hom T.hom = pullback.snd A.hom T.hom :=
    pullback.lift_snd _ _ _
  have sec_f : ∀ y : T ⟶ A, sec y ≫ f = sec (y ^ c) := by
    intro y
    apply pullback.hom_ext
    · rw [Category.assoc, f_fst, ← Category.assoc, sec_fst, sec_fst,
        ← GlobalTheory.GrpTangent.comp_mulN]
      rfl
    · rw [Category.assoc, f_snd, sec_snd, sec_snd]
  have key : sec x ≫ f = sec 1 ≫ f := by rw [sec_f, sec_f, hx, one_pow]
  let Y : Over AT.left := Over.mk f
  let X : Over AT.left := Over.mk (sec 1 ≫ f)
  let fx : X ⟶ Y := Over.homMk (sec x) key
  let f1 : X ⟶ Y := Over.homMk (sec 1) rfl
  haveI : LocallyOfFiniteType Y.hom := hff
  haveI : FormallyUnramified Y.hom := hfu
  have hpt : ∀ t : T.left, t ∈ Set.range (GlobalTheory.FinEt.agreeι fx f1) := by
    intro t
    obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point T.left t
    have hk : (c : k) ≠ 0 := (GlobalTheory.GrpTangent.isUnit_natCast_of_point hc a).ne_zero
    have h1 := H k hk (a ≫ T.hom) (Over.homMk a rfl)
    have h2 : a ≫ x.left = a ≫ (1 : T ⟶ A).left := by
      have := congrArg CommaMorphism.left
        (h1.trans (comp_one (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T)).symm)
      exact this
    have h3 : a ≫ fx.left = a ≫ f1.left := by
      change a ≫ sec x = a ≫ sec 1
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, sec_fst, sec_fst, h2]
      · rw [Category.assoc, Category.assoc, sec_snd, sec_snd]
    have h4 := (GlobalTheory.FinEt.comp_eq_comp_iff_range fx f1 a).mp h3
    apply h4
    rw [ha]; rfl
  have hsec : sec x = sec 1 := by
    have := (GlobalTheory.FinEt.comp_eq_comp_iff_range fx f1 (𝟙 _)).mpr (by
      rintro _ ⟨t, rfl⟩; exact hpt _)
    simpa [fx, f1] using this
  ext1
  rw [← sec_fst x, hsec, sec_fst]

end GlobalTheory.TorsionRigid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExtendsUnramifiedStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_variety_extends_unramified : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ (P : Over (Sp R)), QuasiSeparated P.hom → ∀ (A : Over (Sp K)), QuasiCompact A.hom → ∀ (G : Over (Sp W)), QuasiCompact G.hom → Flat G.hom → ∀ (e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A) (iA : A.left ⟶ P.left) (hA : iA ≫ P.hom = A.hom ≫ spMap (algebraMap R K)), IsClosedImmersion (pullback.lift iA A.hom hA) → ∀ (iG : G.left ⟶ P.left) (hG : iG ≫ P.hom = G.hom ≫ spMap (algebraMap R W)), IsClosedImmersion (pullback.lift iG G.hom hG) → e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ iA = pullback.fst G.hom (spMap (algebraMap W K')) ≫ iG → ∃ (X : Over (Sp R)) (a : A.left ⟶ X.left) (g : G.left ⟶ X.left), IsPullback a A.hom X.hom (spMap (algebraMap R K)) ∧ IsPullback g G.hom X.hom (spMap (algebraMap R W)) ∧ e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ a = pullback.fst G.hom (spMap (algebraMap W K')) ≫ g := by
  first | exact @GlobalTheory.UnramifiedClosure.closure_baseChange | exact GlobalTheory.UnramifiedClosure.closure_baseChange | (intros; apply GlobalTheory.UnramifiedClosure.closure_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietySepClosedPointDivisibleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_sepClosed_point_divisible : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ n : ℕ, (n : K) ≠ 0 → ∀ x : ptOver K Ω ⟶ A, ∃ y, y ^ n = x := by
  first | exact @GlobalTheory.SepClosedDiv.exists_pow_eq | exact GlobalTheory.SepClosedDiv.exists_pow_eq | (intros; apply GlobalTheory.SepClosedDiv.exists_pow_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleLinearEquivMapsOpenFiniteSubgroupToOpenStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeleLinearEquiv_maps_open_finite_subgroup_to_open : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)))
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) →
      ∃ M' : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (M' : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) ∧
        ∀ m' ∈ M', ∃ m ∈ M, B (GlobalTheory.WeilAdm.finE2 F m) = GlobalTheory.WeilAdm.finE2 F m' := by
  first | exact @GlobalTheory.WeilAdm.fintrans | exact GlobalTheory.WeilAdm.fintrans | (intros; apply GlobalTheory.WeilAdm.fintrans <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleLinearEquivRestrictsRealLinearEquivArchimedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeleLinearEquiv_restricts_realLinearEquiv_archimedean : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (B : ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) ≃ₗ[AdeleRing (𝓞 F) F] ((κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))),
      ∃ L : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
        ∀ v, B (GlobalTheory.WeilAdm.mixedSpaceVecPairAsAdeles F v) = GlobalTheory.WeilAdm.mixedSpaceVecPairAsAdeles F (L v) := by
  first | exact @GlobalTheory.WeilAdm.infLin_main | exact GlobalTheory.WeilAdm.infLin_main | (intros; apply GlobalTheory.WeilAdm.infLin_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesContinuousFiniteRealPointStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLinearCoordinates_continuous_finite_real_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT N : ℕ)
    (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
    Continuous e ∧ Continuous e.symm ∧
      (∀ x : Formalism.IndefR.DatumF.WOF F E nS nT, x.map (Formalism.IndefR.DatumF.finPartF F E) = 0 ↔ GlobalTheory.SWQ.fin (e x).1 = 0 ∧ GlobalTheory.SWQ.fin (e x).2 = 0) ∧
      (∀ x : Formalism.IndefR.DatumF.WOF F E nS nT, x.map (Formalism.IndefR.DatumF.infPartF F E) = 0 ↔ GlobalTheory.SWQ.inf (e x).1 = 0 ∧ GlobalTheory.SWQ.inf (e x).2 = 0) := by
  first | exact @GlobalTheory.AdelicCoordF.coord | exact GlobalTheory.AdelicCoordF.coord | (intros; apply GlobalTheory.AdelicCoordF.coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesRationalSurjectiveOfCMStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLinearCoordinates_rational_surjective_of_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT N : ℕ)
    (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
    (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F, e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
    ∀ y z : Fin N → F, ∃ x : Matrix (Fin nT) (Fin nS) E, e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := by
  first | exact @GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps_F | exact GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps_F | (intros; apply GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps_F <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineLineMorphismConstantOfConstOnNonzeroStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineLine_morphism_constant_of_const_on_nonzero : ∀ (k : Type) [Field k] [IsAlgClosed k] (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsSeparated q] [LocallyOfFiniteType q] (f : Sp (Polynomial k) ⟶ Y), f ≫ q = spMap (algebraMap k (Polynomial k)) → (∀ c : k, c ≠ 0 → spMap (Polynomial.evalRingHom c) ≫ f = spMap (Polynomial.evalRingHom 1) ≫ f) → ∀ a b : Polynomial k →ₐ[k] k, spMap a.toRingHom ≫ f = spMap b.toRingHom ≫ f := by
  first | exact @GlobalTheory.ConstAffineLine.eq_of_const_nonzero | exact GlobalTheory.ConstAffineLine.eq_of_const_nonzero | (intros; apply GlobalTheory.ConstAffineLine.eq_of_const_nonzero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicDbarChernFormOfGramMatrixEqZero
section
set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm.ChernDbar

variable {n : ℕ}

theorem dbar_dbar_comm {u : V n → ℂ} {z : V n} (hu : ContDiffAt ℝ 2 u z) (v w : V n) :
    dbar (fun x => dbar u x v) z w = dbar (fun x => dbar u x w) z v := by
  have h := (differentiableAt_fderiv_of_contDiffAt_two hu)
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have e (a b : V n) : dbar (fun x => dbar u x a) z b = (1 / 4 : ℂ) * (fderiv ℝ (fderiv ℝ u) z b a
      + Complex.I * fderiv ℝ (fderiv ℝ u) z (Complex.I • b) a + Complex.I * fderiv ℝ (fderiv ℝ u) z b (Complex.I • a)
      - fderiv ℝ (fderiv ℝ u) z (Complex.I • b) (Complex.I • a)) := by
    have e0 : (fun x => dbar u x a) = fun x => (1 / 2 : ℂ) • (fderiv ℝ u x a + Complex.I • fderiv ℝ u x (Complex.I • a)) :=
      funext fun x => dbar_apply u x a
    rw [e0, dbar_const_smul _ ((h1 _).fun_add ((h1 _).fun_const_smul Complex.I)),
      dbar_add (h1 _) ((h1 _).fun_const_smul Complex.I), dbar_const_smul _ (h1 _)]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, dbar_apply,
      fderiv_fderiv_apply hu, smul_eq_mul]
    linear_combination (1 / 4 : ℂ) * fderiv ℝ (fderiv ℝ u) z (Complex.I • b) (Complex.I • a) * Complex.I_mul_I
  rw [e, e, hs.eq w v, hs.eq (Complex.I • w) v, hs.eq w (Complex.I • v), hs.eq (Complex.I • w) (Complex.I • v)]
  ring

theorem dbarAt_sum_smul {ι : Type} [Fintype ι] {v : V n} {g : ι → V n → ℂ} (hg : ∀ p, DifferentiableAt ℝ (g p) v)
    (c : ι → Alt n) : dbarAt (fun x => ∑ p, g p x • c p) v =
      ∑ a, ∑ p, dbar (g p) v (coordVec a) • (dzb a * c p) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  have : coefwise (fun f => dbar f v (coordVec a)) (fun x => ∑ p, g p x • c p) =
      ∑ p, dbar (g p) v (coordVec a) • c p := by
    refine (bas n).ext_elem fun S => ?_
    rw [FormMul.repr_coefwise]
    simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [dbar_sum (A := fun p x => g p x * (bas n).repr (c p) S) (fun p _ => (hg p).mul (differentiableAt_const _)),
      ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [dbar_mul (hg p) (differentiableAt_const _)]
    simp
  rw [this, Finset.mul_sum]
  simp only [mul_smul_comm]

theorem differentiableAt_sum_smul {ι : Type} [Fintype ι] {v : V n} {g : ι → V n → ℂ}
    (hg : ∀ p, DifferentiableAt ℝ (g p) v) (c : ι → Alt n) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun x => (bas n).repr (∑ p, g p x • c p) S) v := by
  simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact DifferentiableAt.fun_sum fun p _ => (hg p).mul (differentiableAt_const _)

theorem dbarAt_add {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    dbarAt (fun x => F x + G x) v = dbarAt F v + dbarAt G v := by
  simp only [dbarAt, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl fun a _ => congrArg _ ((bas n).ext_elem fun S => ?_)
  simp only [map_add, Finsupp.add_apply, FormMul.repr_coefwise]
  rw [dbar_add (hF S) (hG S), ContinuousLinearMap.add_apply]

theorem dbarAt_const (c : Alt n) (v : V n) : dbarAt (fun _ => c) v = 0 := by
  simp [dbarAt, coefwise]

def IsClosedAt (v : V n) (F : V n → Ev n) : Prop :=
  (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x : Alt n) S) v) ∧ dbarAt (fun x => (F x : Alt n)) v = 0

theorem isClosedAt_const (v : V n) (c : Ev n) : IsClosedAt v fun _ => c :=
  ⟨fun _ => differentiableAt_const _, dbarAt_const _ _⟩

def closedAt (v : V n) : Subsemiring (V n → Ev n) where
  carrier := {F | IsClosedAt v F}
  mul_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    refine ⟨fun S => ?_, ?_⟩
    · rw [show (fun x => (bas n).repr ((F * G) x : Alt n) S) = _ from
        funext fun x => FormMul.repr_mul (F x : Alt n) (G x : Alt n) S]
      exact DifferentiableAt.fun_sum fun p _ => ((hF _).mul (hG _)).mul (differentiableAt_const _)
    · obtain ⟨y, hy⟩ := FormMul.dbarAt_mul hF hG
      simp only [Pi.mul_apply, Subalgebra.coe_mul]
      rw [hy, hF0, hG0, zero_mul, mul_zero, add_zero]
  one_mem' := isClosedAt_const v 1
  add_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    refine ⟨fun S => ?_, ?_⟩
    · simp only [Pi.add_apply, Subalgebra.coe_add, map_add, Finsupp.add_apply]
      exact (hF S).add (hG S)
    · simp only [Pi.add_apply, Subalgebra.coe_add]
      rw [dbarAt_add hF hG, hF0, hG0, add_zero]
  zero_mem' := isClosedAt_const v 0

theorem const_mem (v : V n) (c : Ev n) : (fun _ => c) ∈ closedAt v := isClosedAt_const v c

def closedRing (v : V n) : Subring (V n → Ev n) :=
  { closedAt v with
    neg_mem' := fun {F} hF => by
      have := (closedAt v).mul_mem (const_mem v (-1)) hF
      have e : (fun _ => (-1 : Ev n)) * F = -F := funext fun x => neg_one_mul _
      rwa [e] at this }

theorem dzb_dz_dzb (a b c : Fin n) : dzb c * (dz a * dzb b) = -(dzb b * (dz a * dzb c)) := by
  have h (b c : Fin n) : dzb c * (dz a * dzb b) = dz a * dzb b * dzb c :=
    Subalgebra.mem_center_iff.1 (sym (a, b)).2 (dzb c)
  rw [h, h, mul_assoc, mul_assoc, ← mul_neg]
  exact congrArg _ (eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _))

theorem dbar_form_mem {v : V n} {θ : Fin n → V n → ℂ} (hθ : ∀ a, ContDiffAt ℝ 2 (θ a) v) :
    (fun x => ∑ a, ∑ b, dbar (θ a) x (coordVec b) • sym (a, b)) ∈ closedRing v := by
  have e (x : V n) : ((∑ a, ∑ b, dbar (θ a) x (coordVec b) • sym (a, b) : Ev n) : Alt n) =
      ∑ p : Fin n × Fin n, dbar (θ p.1) x (coordVec p.2) • (dz p.1 * dzb p.2) := by
    simp only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, sym, Fintype.sum_prod_type]
  have hd (p : Fin n × Fin n) : DifferentiableAt ℝ (fun x => dbar (θ p.1) x (coordVec p.2)) v :=
    differentiableAt_dbar_apply (hθ p.1) _
  change IsClosedAt v _
  refine ⟨fun S => ?_, ?_⟩
  · simp only [e]
    exact differentiableAt_sum_smul hd _ S
  · simp only [e]
    rw [dbarAt_sum_smul hd]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    set s : Alt n := ∑ c, ∑ b, dbar (fun x => dbar (θ a) x (coordVec b)) v (coordVec c) • (dzb c * (dz a * dzb b))
      with hs
    have h2 : s = -s := by
      conv_lhs => rw [hs, Finset.sum_comm]
      rw [hs, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [dzb_dz_dzb a b c, dbar_dbar_comm (hθ a), smul_neg]
    have h3 : (2 : ℂ) • s = 0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.2 h2
    exact (smul_eq_zero.1 h3).resolve_left two_ne_zero

theorem coeff_charpolyRev_map {A B r : Type} [CommRing A] [CommRing B] [Fintype r] [DecidableEq r] (f : A →+* B)
    (M : Matrix r r A) (j : ℕ) : (M.map f).charpolyRev.coeff j = f (M.charpolyRev.coeff j) := by
  rw [← Polynomial.coeff_map, charpolyRev, charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 2
  ext i k : 2
  by_cases h : i = k <;> simp [h, Matrix.one_apply]

theorem dbarAt_chernAt : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)),
    IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ), ∀ v ∈ s,
    dbarAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  intro n r _ _ H s hs hH hu j v hv
  have h3 : MContDiffAt 3 H v := fun a b => ((hH a b).contDiffAt (hs.mem_nhds hv)).of_le (by norm_cast)
  have hθ (i k : r) (a : Fin n) : ContDiffAt ℝ 2 (fun x => conn H x (coordVec a) i k) v :=
    h3.conn (hu v hv) (by norm_num) (coordVec a) i k
  let M : Matrix r r (closedRing v) := Matrix.of fun i k => ⟨_, dbar_form_mem (hθ i k)⟩
  have key (w : V n) : MvPolynomial.aeval sym (chernPoly H w j) = (M.charpolyRev.coeff j : V n → Ev n) w := by
    have h1 := coeff_charpolyRev_map (MvPolynomial.aeval (R := ℂ) (sym (n := n))).toRingHom (-curvPoly H w) j
    have h2 := coeff_charpolyRev_map ((Pi.evalRingHom (fun _ : V n => Ev n) w).comp (closedRing v).subtype) M j
    refine h1.symm.trans (Eq.trans ?_ h2)
    congr 2
    ext i k : 2
    simp [M, curvPoly, curv, Algebra.smul_def]
  have hm : IsClosedAt v _ := (closedRing v).mul_mem (const_mem v (algebraMap ℂ _ (kappa ^ j))) (M.charpolyRev.coeff j).2
  have e : (fun w => (chernAt H w j : Alt n)) = fun w =>
      ((algebraMap ℂ (Ev n) (kappa ^ j) * (M.charpolyRev.coeff j : V n → Ev n) w : Ev n) : Alt n) :=
    funext fun w => by rw [chernAt, key, Algebra.smul_def]
  rw [e]
  exact hm.2

end GlobalTheory.CxForm.ChernDbar
end
end

