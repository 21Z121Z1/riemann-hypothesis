import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2587
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0781
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsStableBasOfPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2645
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2379
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2588
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrLocalFiniteExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_dvr_local_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (p : ℕ) (hp : p.Prime) (W₀ : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W₀.nonunits) (i : Idx H p) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ₁ : R →+* V₁) (b₁ : ↥(i.c.V W₀) →+* V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective ρ₁ ∧ ρ₁.Finite ∧ IsLocalHom ρ₁ ∧ Function.Injective b₁ := by
  first | exact @GlobalTheory.TraitPlace.exists_place_finite_ext | exact GlobalTheory.TraitPlace.exists_place_finite_ext | (intros; apply GlobalTheory.TraitPlace.exists_place_finite_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalGaloisCoverOfFinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.GalCover

theorem exists_isCN_galois_of_finite : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing R] [IsDomain R] (b : A →+* R), IsCN A → b.Finite → Function.Injective b → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (θ : R →+* R'), IsCN R' ∧ IsLocalHom θ ∧ Function.Injective θ ∧ θ.Finite ∧ ∀ r : R, (∀ σ : R' ≃+* R', IsOfFinOrder σ → (∀ a, σ (θ (b a)) = θ (b a)) → σ (θ r) = θ r) → r ∈ b.range := by
  intro A R _ _ _ _ _ b hA hfin hinj
  obtain ⟨hnoeth, hnorm, hcomp, hchar⟩ := hA
  letI : Algebra A R := b.toAlgebra
  haveI : Module.Finite A R := hfin
  haveI : Algebra.IsIntegral A R := Algebra.IsIntegral.of_finite A R
  let K := FractionRing A
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  let Ω := AlgebraicClosure K
  have hιK : Function.Injective (algebraMap A Ω) := by
    rw [IsScalarTower.algebraMap_eq A K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective A K)
  haveI : Module.IsTorsionFree A R := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  haveI : Module.IsTorsionFree A Ω := Module.isTorsionFree_iff_algebraMap_injective.2 hιK
  haveI : Algebra.IsAlgebraic A R := Algebra.IsIntegral.isAlgebraic
  let φ : R →ₐ[A] Ω := IsAlgClosed.lift
  have hφinj : Function.Injective φ := by
    have hk : (RingHom.ker (φ : R →+* Ω)).comap (algebraMap A R) = ⊥ := by
      refine eq_bot_iff.2 fun a ha => ?_
      have h1 : φ (algebraMap A R a) = 0 := ha
      rw [φ.commutes] at h1
      exact (Ideal.mem_bot).2 (hιK (h1.trans (map_zero _).symm))
    have h2 := Ideal.eq_bot_of_comap_eq_bot hk
    exact (RingHom.injective_iff_ker_eq_bot _).2 h2
  have hint : ∀ x : R, IsIntegral A (φ x) := fun x => (Algebra.IsIntegral.isIntegral (R := A) x).map φ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := R)
  let L : IntermediateField K Ω := IntermediateField.adjoin K ((φ '' (s : Set R)) : Set Ω)
  have hintK : ∀ x : R, IsIntegral K (φ x) := fun x => (hint x).tower_top
  haveI : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨x, -, rfl⟩
    exact hintK x)
  have hmemL : ∀ x : R, φ x ∈ L := fun x => by
    have hx : x ∈ Submodule.span A (s : Set R) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin K _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem L
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [map_smul, Algebra.smul_def]
      refine mul_mem ?_ hy
      rw [IsScalarTower.algebraMap_apply A K Ω]
      exact L.algebraMap_mem _
  let M : IntermediateField K Ω := IntermediateField.normalClosure K L Ω
  have hmem : ∀ x : R, φ x ∈ M := fun x => IntermediateField.le_normalClosure L (hmemL x)
  let W := integralClosure A M
  haveI hWf : Module.Finite A W := IsIntegralClosure.finite A K M W
  haveI : IsLocalRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := A) W
  have hAM : Function.Injective (algebraMap A M) := by
    rw [IsScalarTower.algebraMap_eq A K M]
    exact (algebraMap K M).injective.comp (IsFractionRing.injective A K)
  have hinjW : Function.Injective (algebraMap A W) := fun x y h => hAM (congrArg Subtype.val h)
  let φM : R →+* M := (φ : R →+* Ω).codRestrict M hmem
  have hran : ∀ x : R, φM x ∈ W := fun x => by
    show IsIntegral A (φM x)
    exact (isIntegral_algHom_iff ((IntermediateField.val M).restrictScalars A) Subtype.val_injective).1 (hint x)
  let θ : R →+* W := φM.codRestrict W hran
  have hθval : ∀ x : R, (((θ x : M)) : Ω) = φ x := fun x => rfl
  have hθinj : Function.Injective θ := fun x y h => hφinj (by
    rw [← hθval, ← hθval, h])
  have hcomm : θ.comp b = algebraMap A W := RingHom.ext fun a => by
    apply Subtype.val_injective
    apply Subtype.val_injective
    exact φ.commutes a
  haveI : CharZero W := charZero_of_injective_algebraMap hinjW
  have hθfin : θ.Finite := RingHom.Finite.of_comp_finite (f := b) (by rw [hcomm]; exact RingHom.finite_algebraMap.2 hWf)
  have hθloc : IsLocalHom θ := RingHom.IsIntegral.isLocalHom hθfin.to_isIntegral hθinj

  let res : (M ≃ₐ[K] M) →* (W ≃+* W) :=
    { toFun := fun σ =>
        { toFun := fun x => ⟨σ (x : M), x.2.map ((σ : M →ₐ[K] M).restrictScalars A)⟩
          invFun := fun x => ⟨σ.symm (x : M), x.2.map ((σ.symm : M →ₐ[K] M).restrictScalars A)⟩
          left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : M))
          right_inv := fun x => Subtype.ext (σ.apply_symm_apply (x : M))
          map_mul' := fun x y => Subtype.ext (map_mul σ (x : M) y)
          map_add' := fun x y => Subtype.ext (map_add σ (x : M) y) }
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨W, inferInstance, inferInstance, inferInstance, θ,
    ⟨IsNoetherianRing.of_finite A W, integralClosure.isIntegrallyClosedOfFiniteExtension K,
      GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local A W, inferInstance⟩,
    hθloc, hθinj, hθfin, fun r hr => ?_⟩
  have hfix : ∀ σ : M ≃ₐ[K] M, σ (θ r : M) = (θ r : M) := fun σ => by
    have h1 := hr (res σ) (res.isOfFinOrder (isOfFinOrder_of_finite σ)) (fun a => by
      rw [← RingHom.comp_apply θ b, hcomm]
      apply Subtype.ext
      show σ (algebraMap A M a) = algebraMap A M a
      rw [IsScalarTower.algebraMap_apply A K M]
      exact σ.commutes _)
    exact congrArg Subtype.val h1
  obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (θ r : M)).2 hfix
  have hkint : IsIntegral A k := by
    have : IsIntegral A (algebraMap K M k) := hk ▸ (θ r).2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K M) (algebraMap K M).injective).1 this
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hkint
  refine ⟨a, hφinj ?_⟩
  show φ (algebraMap A R a) = φ r
  rw [φ.commutes, ← hθval, ← hk, ← ha, IsScalarTower.algebraMap_apply A K Ω]
  rfl

end GlobalTheory.GalCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteTraitOverClosedPointModification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_cDvr_injective_isLocalHom (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [CharZero A] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (ψ : A →+* W),
      GlobalTheory.LN.CDvr W ∧ Function.Injective ψ ∧ IsLocalHom ψ := by
  by_cases h : IsField A
  · letI := h.toField
    refine ⟨PowerSeries A, inferInstance, inferInstance, inferInstance, PowerSeries.C, ⟨inferInstance, ?_, ?_⟩,
      RingHom.injective _, inferInstance⟩
    · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
    · exact charZero_of_injective_ringHom (f := PowerSeries.C (R := A)) (RingHom.injective _)
  · obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := exists_complete_discreteValuationRing_dominating A h
    exact ⟨O, inferInstance, inferInstance, inferInstance, φ,
      ⟨inferInstance, inferInstance, charZero_of_injective_ringHom h1⟩, h1, h2⟩

theorem exists_trait_over_closedPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (M : Modif R) (x₀ : M.S), M.π x₀ = closedPoint R →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (ξ : Sp W ⟶ M.S),
        GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧ ξ (closedPoint W) = x₀ := by
  intro R _ _ _ hB M x₀ hx
  have : IsNoetherianRing R := hB.1.1
  have : CharZero R := hB.2
  have := M.integral
  have := M.proper
  have := LocallyOfFiniteType.isLocallyNoetherian M.π
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (M.S.fromSpecStalk x₀ ≫ M.π)
  have hpt : ∀ q, (Spec.map θ) q = M.π (M.S.fromSpecStalk x₀ q) := fun q => by
    rw [hθ, Scheme.Hom.comp_apply]
  have hloc : IsLocalHom θ.hom := by
    apply ((local_hom_TFAE θ.hom).out 0 4).2
    have e := hpt (closedPoint (M.S.presheaf.stalk x₀) : Spec (M.S.presheaf.stalk x₀))
    rw [Scheme.fromSpecStalk_closedPoint, hx] at e
    exact congrArg PrimeSpectrum.asIdeal e
  have hinj : Function.Injective θ.hom := by
    let pt : Sp (FractionRing R) := closedPoint (FractionRing R)
    obtain ⟨q, hq⟩ : M.gp pt ∈ Set.range (M.S.fromSpecStalk x₀) := by
      rw [Scheme.range_fromSpecStalk]
      show _ ⤳ x₀
      rw [specializes_iff_mem_closure]
      have hd := M.dominant.denseRange
      have hs : Set.range M.gp.base ⊆ {M.gp pt} := by
        rintro _ ⟨y, rfl⟩
        rw [Subsingleton.elim y (closedPoint _)]
        rfl
      exact closure_mono hs (hd.closure_range ▸ Set.mem_univ x₀)
    have h1 : (Spec.map θ) q = jK R pt := by
      rw [hpt, hq]
      exact (Scheme.Hom.comp_apply M.gp M.π pt).symm.trans (by rw [M.gp_π])
    have h2 := congrArg PrimeSpectrum.asIdeal h1
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h3 : a ∈ Ideal.comap θ.hom q.asIdeal := by
      rw [Ideal.mem_comap, ha]; exact Ideal.zero_mem _
    have h4 : algebraMap R (FractionRing R) a ∈ maximalIdeal (FractionRing R) := by
      have h5 : a ∈ ((jK R) pt).asIdeal := by
        rw [← h2]; exact h3
      exact h5
    have h6 : algebraMap R (FractionRing R) a = 0 := by
      by_contra hne
      exact (maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ h4 (isUnit_iff_ne_zero.2 hne))
    exact IsFractionRing.injective R (FractionRing R) (h6.trans (map_zero _).symm)
  have : CharZero (M.S.presheaf.stalk x₀) := charZero_of_injective_ringHom hinj
  obtain ⟨W, _, _, _, ψ, hW, hψi, hψl⟩ := exists_cDvr_injective_isLocalHom (M.S.presheaf.stalk x₀)
  refine ⟨W, inferInstance, inferInstance, inferInstance, ψ.comp θ.hom, spMap ψ ≫ M.S.fromSpecStalk x₀, hW,
    hψi.comp hinj, RingHom.isLocalHom_comp _ _, ?_, ?_⟩
  · rw [Category.assoc, ← hθ, ← Spec.map_comp]
    rfl
  · exact (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (M.S.fromSpecStalk x₀) (IsLocalRing.comap_closedPoint ψ))
        (Scheme.fromSpecStalk_closedPoint (x := x₀)))

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFibreExponentialFullLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.FibreExp

theorem exists_exp_lattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G →
    SmoothOfRelativeDimension g G.hom → ∀ y : Sp ℂ ⟶ X, ∃ (e : (Fin g → ℂ) → (Over.mk y ⟶ G))
      (Λ : Submodule ℤ (Fin g → ℂ)), IsExp y e ∧ DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧
        ∀ z, e z = 1 ↔ z ∈ Λ := by
  intro X G _ _ g hG hgG y
  letI : GrpObj ((Over.pullback y).obj G) := Functor.grpObjObj
  have hj := isGrpPullback_pullback G y
  have hA : IsAbelianScheme ((Over.pullback y).obj G) := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hj
  have hgA : SmoothOfRelativeDimension g ((Over.pullback y).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hj.1 hgG
  obtain ⟨L, ⟨u⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif _ g hA hgA
  obtain ⟨h1, h2⟩ := GlobalTheory.UnifTangent.tangent_bijection u hgA
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv hj (𝟙_ _) y (Category.id_comp _).symm
  have he := GlobalTheory.PointUnif.isExp_push hj u h1 h2 Φ hΦ
  exact ⟨fun z => Φ (u.ex z), u.Λ, he, u.discrete, u.full,
    fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)⟩

end GlobalTheory.FibreExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatePolynomialSubMemMaximalIdealPow
section
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory

theorem exists_mem_closure_sub_mem_maximalIdeal_pow
    (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    (inc : R →+* A) (ev : A →+* R) (hev : ∀ r, ev (inc r) = r) (n : ℕ) (z : Fin n → A)
    (hm : maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z))
    (k : ℕ) (f : A) :
    ∃ p ∈ Subring.closure (Set.range inc ∪ Set.range z), f - p ∈ maximalIdeal A ^ k := by
  set P := Subring.closure (Set.range inc ∪ Set.range z) with hP
  set m := maximalIdeal A with hmdef
  have incP : ∀ r, inc r ∈ P := fun r => Subring.subset_closure (Or.inl ⟨r, rfl⟩)
  have zP : ∀ i, z i ∈ P := fun i => Subring.subset_closure (Or.inr ⟨i, rfl⟩)
  have hker : ∀ x : A, x - inc (ev x) ∈ m := by
    intro x
    have h1 : x - inc (ev x) ∈ RingHom.ker ev := by
      simp [RingHom.mem_ker, hev]
    exact le_maximalIdeal (RingHom.ker_ne_top ev) h1
  let C : ℕ → Ideal A := fun j =>
    { carrier := {x | ∃ q ∈ P, q ∈ m ^ j ∧ x - q ∈ m ^ (j + 1)}
      add_mem' := by
        rintro a b ⟨q, hq, hqm, hqe⟩ ⟨q', hq', hqm', hqe'⟩
        refine ⟨q + q', P.add_mem hq hq', Ideal.add_mem _ hqm hqm', ?_⟩
        have : a + b - (q + q') = (a - q) + (b - q') := by ring
        rw [this]; exact Ideal.add_mem _ hqe hqe'
      zero_mem' := ⟨0, P.zero_mem, Ideal.zero_mem _, by simp⟩
      smul_mem' := by
        rintro c x ⟨q, hq, hqm, hqe⟩
        refine ⟨inc (ev c) * q, P.mul_mem (incP _) hq, Ideal.mul_mem_left _ _ hqm, ?_⟩
        have hx : x ∈ m ^ j := by
          have : x = q + (x - q) := by ring
          rw [this]; exact Ideal.add_mem _ hqm (Ideal.pow_le_pow_right (Nat.le_succ j) hqe)
        have : c • x - inc (ev c) * q = inc (ev c) * (x - q) + (c - inc (ev c)) * x := by
          simp only [smul_eq_mul]; ring
        rw [this]
        refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hqe) ?_
        rw [pow_succ']
        exact Ideal.mul_mem_mul (hker c) hx }
  have memC : ∀ j x, x ∈ C j ↔ ∃ q ∈ P, q ∈ m ^ j ∧ x - q ∈ m ^ (j + 1) := fun _ _ => Iff.rfl
  have hC1 : m ≤ C 1 := by
    calc m = _ := hm
      _ ≤ C 1 := by
        refine sup_le ?_ ?_
        · rw [Ideal.map_le_iff_le_comap]
          intro r hr
          refine (memC _ _).2 ⟨inc r, incP r, ?_, by simp⟩
          rw [pow_one, hm]; exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hr)
        · rw [Ideal.span_le]
          rintro _ ⟨i, rfl⟩
          refine (memC _ _).2 ⟨z i, zP i, ?_, by simp⟩
          rw [pow_one, hm]; exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  have hCj : ∀ j, m ^ j ≤ C j := by
    intro j
    induction j with
    | zero =>
      intro x _
      exact (memC _ _).2 ⟨inc (ev x), incP _, by simp, by simpa using hker x⟩
    | succ j ih =>
      rw [pow_succ]
      refine Ideal.mul_le.2 fun y hy w hw => ?_
      obtain ⟨q, hq, hqm, hqe⟩ := (memC _ _).1 (ih hy)
      obtain ⟨q1, hq1, hq1m, hq1e⟩ := (memC _ _).1 (hC1 hw)
      refine (memC _ _).2 ⟨q * q1, P.mul_mem hq hq1, ?_, ?_⟩
      · rw [pow_succ]; exact Ideal.mul_mem_mul hqm (by simpa using hq1m)
      · have : y * w - q * q1 = q * (w - q1) + (y - q) * w := by ring
        rw [this]
        refine Ideal.add_mem _ ?_ ?_
        · have : m ^ (j + 1 + 1) = m ^ j * m ^ (1 + 1) := by rw [← pow_add]
          rw [this]; exact Ideal.mul_mem_mul hqm hq1e
        · rw [pow_succ]; exact Ideal.mul_mem_mul hqe hw
  induction k with
  | zero => exact ⟨0, P.zero_mem, by simp⟩
  | succ k ih =>
    obtain ⟨p, hp, hfp⟩ := ih
    obtain ⟨q, hq, -, hqe⟩ := (memC _ _).1 (hCj k hfp)
    refine ⟨p + q, P.add_mem hp hq, ?_⟩
    rw [show f - (p + q) = f - p - q by ring]
    exact hqe

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesLogVectorFieldsDeterminant
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

theorem GlobalTheory.LogPole.exists_coord_logDet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)) (x₀ : TF.Y.X), x₀ ∈ U.1 → ∃ (x : Fin Dw.dim → Γ(TF.Y.X, U.1)) (U' : TF.Y.X.affineOpens) (hU' : U'.1 ≤ U.1), x₀ ∈ U'.1 ∧ TopForm.IsFrame (TopForm.dOn TF.Y.s fun i => resG TF.Y.X hU' (x i)) ∧ (LogKS.boundary TF.Y).ideal U' = Ideal.span {resG TF.Y.X hU' (logDet (fun j => (b j).1) x)} := by
  intro E _ _ _ H Dw l Xo c TF U b x₀ hx₀
  classical
  have hres : ∀ (V W : TF.Y.X.Opens) (hW : IsAffineOpen W) (h : W ≤ V) (hVU : V ≤ U.1)
      (f : Fin Dw.dim → Γ(TF.Y.X, U.1)), TopForm.IsFrame (TopForm.dOn TF.Y.s fun i => resG TF.Y.X hVU (f i)) →
      TopForm.IsFrame (TopForm.dOn TF.Y.s fun i => resG TF.Y.X (h.trans hVU) (f i)) := by
    intro V W hW h hVU f hf
    have h' := hf.res hW h
    rw [TopForm.resForm_dOn] at h'
    simpa only [LB.resG_resG] using h'
  obtain ⟨hreg, m, a, J, hRsp, hIa⟩ := GlobalTheory.T.snc_stalk_regularParameters_from_affineOpen TF.Y.X (LogKS.boundary TF.Y) TF.snc U x₀ hx₀
  haveI := TF.smooth
  obtain ⟨hfp, hfree, hfin, hrank⟩ := GlobalTheory.T.smooth_affineOpen_finitePresentation_stalkKaehler_free_rank c.F TF.Y.X TF.Y.s Dw.dim U x₀ hx₀
  letI : Algebra c.F Γ(TF.Y.X, U.1) := (algX TF.Y.s U.1).toAlgebra
  letI : Algebra Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) :=
    TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf ⟨x₀, hx₀⟩
  letI : Algebra c.F (TF.Y.X.presheaf.stalk x₀) :=
    ((TF.Y.X.presheaf.germ U.1 x₀ hx₀).hom.comp (algX TF.Y.s U.1)).toAlgebra
  haveI : IsScalarTower c.F Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hloc := U.2.isLocalization_stalk ⟨x₀, hx₀⟩
  haveI : IsNoetherianRing Γ(TF.Y.X, U.1) := Algebra.FiniteType.isNoetherianRing c.F _
  haveI : IsNoetherianRing (TF.Y.X.presheaf.stalk x₀) :=
    IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨x₀, hx₀⟩).asIdeal.primeCompl _ inferInstance
  have h3 := GlobalTheory.T.exists_coordinates_extending_regular_parameters c.F Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀)
    (U.2.primeIdealOf ⟨x₀, hx₀⟩).asIdeal Dw.dim hrank m a hRsp
  obtain ⟨x, e, hxe, bs, hbs⟩ := h3
  have hxe' : (fun j => x (e j)) = a := funext hxe
  have hI : ((LogKS.boundary TF.Y).ideal U).map (algebraMap Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀)) =
      Ideal.span {algebraMap Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) (∏ j ∈ J, x (e j))} := by
    simp only [hxe]; exact hIa
  have hspan : ∀ D : Derivation ℤ Γ(TF.Y.X, U.1) Γ(TF.Y.X, U.1),
      (∀ c', D (algebraMap c.F Γ(TF.Y.X, U.1) c') = 0) → (∀ f ∈ (LogKS.boundary TF.Y).ideal U, D f ∈ (LogKS.boundary TF.Y).ideal U) →
      ∃ cf : Fin Dw.dim → Γ(TF.Y.X, U.1), D = ∑ j, cf j • (b j).1 := by
    intro D h0 h1
    let D' : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U := ⟨D, h0, h1⟩
    refine ⟨b.repr D', ?_⟩
    have := congrArg Subtype.val (b.sum_repr D')
    rw [Submodule.coe_sum] at this
    exact this.symm
  have h4 := GlobalTheory.T.logDerivation_det_eq_unit_mul_prod_normalCrossings c.F Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) (U.2.primeIdealOf ⟨x₀, hx₀⟩).asIdeal
    Dw.dim m x e J (by simp only [hxe]; exact hRsp) ⟨bs, hbs⟩ ((LogKS.boundary TF.Y).ideal U) hI
    (fun j => (b j).1) (fun j c' => (b j).2.1 c') (fun j => (b j).2.2) hspan
  obtain ⟨u, hu⟩ := h4
  have hd : ((LogKS.boundary TF.Y).ideal U).map (TF.Y.X.presheaf.germ U.1 x₀ hx₀).hom =
      Ideal.span {(TF.Y.X.presheaf.germ U.1 x₀ hx₀).hom (logDet (fun j => (b j).1) x)} := by
    change ((LogKS.boundary TF.Y).ideal U).map (algebraMap Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀)) =
      Ideal.span {algebraMap Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) (logDet (fun j => (b j).1) x)}
    exact hI.trans ((Ideal.span_singleton_mul_left_unit u.isUnit _).symm.trans (congrArg (fun y => Ideal.span {y}) hu.symm))
  have h5 := GlobalTheory.T.idealSheaf_eq_span_on_basicOpens_of_stalk_principal TF.Y.X (LogKS.boundary TF.Y) U x₀ hx₀ _ inferInstance hd
  obtain ⟨s₂, hs₂, hid⟩ := h5
  have h2 := GlobalTheory.T.exists_basicOpen_topFormFrame_of_stalkKaehlerBasis c.F TF.Y.X TF.Y.s Dw.dim U x₀ hx₀ x ⟨bs, hbs⟩
  obtain ⟨s₁, hs₁, hfr⟩ := h2
  have hle₁ : TF.Y.X.basicOpen (s₁ * s₂) ≤ TF.Y.X.basicOpen s₁ := by
    rw [Scheme.basicOpen_mul]; exact inf_le_left
  have hle₂ : TF.Y.X.basicOpen (s₁ * s₂) ≤ TF.Y.X.basicOpen s₂ := by
    rw [Scheme.basicOpen_mul]; exact inf_le_right
  refine ⟨x, TF.Y.X.affineBasicOpen (s₁ * s₂), TF.Y.X.basicOpen_le _, ?_, ?_, hid _ hle₂⟩
  · show x₀ ∈ TF.Y.X.basicOpen (s₁ * s₂)
    rw [Scheme.basicOpen_mul]; exact ⟨hs₁, hs₂⟩
  · exact hres _ _ (U.2.basicOpen (s₁ * s₂)) hle₁ _ x hfr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectedLocIsoOfDefectCoboundaryStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_corrected_locIso_of_defect_coboundary : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ → ∀ E : GlobForm s₀ →+ C0 S'.F, (∀ w, S'.IsIdealValuedLiftSystemCochain (E w)) → (∀ (r : R) w, E (π r • w) = r • E w) → (∀ (w : GlobForm s₀) U V a, θ U V a (w.1 U) = d0 S'.F (E w) U V a) → ∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b) := by
  first | exact @GlobalTheory.LiftSys.exists_corr_of_defect | exact GlobalTheory.LiftSys.exists_corr_of_defect | (intros; apply GlobalTheory.LiftSys.exists_corr_of_defect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalSymmetricStructureOfGenericSymmetriStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cubicalSymmetricStructure_of_genericSymmetric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R], ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsProper (pullback.snd G.hom (jK R)) → ∀ L : LB G.left, L.IsLB → Out.Sym ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) → ∃ P : GlobalTheory.UU.CP G, P.L.L = L := by
  first | exact @GlobalTheory.CubSymPkg.exists_cp_of_generic_sym | exact GlobalTheory.CubSymPkg.exists_cp_of_generic_sym | (intros; apply GlobalTheory.CubSymPkg.exists_cp_of_generic_sym <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefectCoboundaryOfObstructionClassZeroStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_defect_coboundary_of_obstructionClass_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (w : Glob1 F) (θ : ∀ (T T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), Ω[F.obj T⁄R₀] →+ L.B T''), L.IsObs θ → L.IsOb2 α w 0 → ∃ g : ∀ (T T' : C) (_ : T ⟶ T'), L.B T', (∀ T T' a, g T T' a ∈ I.map (algebraMap R (L.B T'))) ∧ ∀ T T' T'' a b, θ T T' T'' a b (w.1 T) = L.ρ b (g T T' a) - g T T'' (a ≫ b) + g T' T'' b := by
  first | exact @GlobalTheory.ObsCob.exists_cob | exact GlobalTheory.ObsCob.exists_cob | (intros; apply GlobalTheory.ObsCob.exists_cob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationValuesAlgClosedField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.MumValues

theorem exists_values : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∃ N : NumD F, Nonempty (NumOf D.toPre F N) := by
  intro R _ _ _ hR D F _ _ _
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨N, ν, -⟩ := GlobalTheory.ValuesExist.exists_integral_values GlobalTheory.allSixLaws.1 R D.toPre D.psi_even D.tau_bimult F ⊤
    (fun _ => trivial)
  exact ⟨N, ⟨ν⟩⟩

end GlobalTheory.MumValues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorsDoubleFlagSpaceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divisors_doubleFlagSpace : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (gr : Root m → Y.Dv), ∀ B ∈ E'.S (genericPoint Y.X), (∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t) → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹) → ∃ (D₁ D₂ : Root m → CartierDiv W.Z) (Θ : CartierDiv W.Z), (∀ x, IsPull W.p₁ (D₁ x) (gr x)) ∧ (∀ x, IsPull W.p₂ (D₂ x) (gr x)) ∧ (∀ x, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → toPic (D₁ x) = toPic (D₂ x)) ∧ toPic (D₁ ⟨τ, a⟩) + toPic (D₁ ⟨τ, b⟩) = toPic (D₂ ⟨τ, a⟩) + toPic (D₂ ⟨τ, b⟩) ∧ toPic Θ = toPic (D₂ ⟨τ, b⟩) - toPic (D₁ ⟨τ, a⟩) ∧ Θ.Eff ∧ (Θ.supp : Set W.Z) = Set.range W.δ := by
  first | exact @GlobalTheory.FlagPush.DivOn.exists_divisors | exact GlobalTheory.FlagPush.DivOn.exists_divisors | (intros; apply GlobalTheory.FlagPush.DivOn.exists_divisors <;> assumption)
end

