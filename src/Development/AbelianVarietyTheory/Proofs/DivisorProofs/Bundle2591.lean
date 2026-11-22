import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0702
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2449
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2475
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrLiftOfGeometricPoint
section
noncomputable section

namespace GlobalTheory.GeomTrait

section Algebra

open IsLocalRing

theorem dimensionLEOne_of_forall_mem {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {f : R} (hf : f ≠ 0) (h : ∀ q : Ideal R, q.IsPrime → q ≠ ⊥ → f ∈ q) : Ring.DimensionLEOne R := by
  classical
  refine ⟨fun {q} hq0 hq => ?_⟩
  by_contra hqm
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {f})
  have hle : q ≤ maximalIdeal R := le_maximalIdeal hq.ne_top
  have hns : ¬ ((maximalIdeal R : Set R) ⊆ ⋃ i ∈ (hfin.toFinset : Set (Ideal R)), (id i : Ideal R)) := by
    rw [Ideal.subset_union_prime (f := id) ⊥ ⊥ (fun i hi _ _ => (hfin.mem_toFinset.1 hi).1.1)]
    rintro ⟨p, hp, hmp⟩
    have hp' := hfin.mem_toFinset.1 hp
    have h1 : p ≤ q := hp'.2 ⟨hq, (Ideal.span_singleton_le_iff_mem _).2 (h q hq hq0)⟩
      (hle.trans hmp)
    exact hqm (le_antisymm hle (le_trans hmp h1) ▸ maximalIdeal.isMaximal R)
  obtain ⟨g, hgm, hg⟩ := Set.not_subset.1 hns
  have hne : Ideal.span {g} ≠ ⊤ := fun e => hgm (Ideal.span_singleton_eq_top.1 e)
  obtain ⟨⟨p, hp⟩⟩ := Ideal.nonempty_minimalPrimes hne
  have hpp : p.IsPrime := hp.1.1
  have hgp : g ∈ p := hp.1.2 (Ideal.subset_span rfl)
  have hht : p.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp
  have hfm : Ideal.span {f} ≠ ⊤ := fun e =>
    hq.ne_top (q.eq_top_of_isUnit_mem (h q hq hq0) (Ideal.span_singleton_eq_top.1 e))
  have hg0 : g ≠ 0 := by
    rintro rfl
    obtain ⟨⟨p', hp'⟩⟩ := Ideal.nonempty_minimalPrimes hfm
    exact hg (Set.mem_iUnion₂.2 ⟨p', hfin.mem_toFinset.2 hp', p'.zero_mem⟩)
  have hp0 : p ≠ ⊥ := fun e => hg0 (by simpa [e] using hgp)
  obtain ⟨p', hp', hp'p⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).2 (h p hpp hp0))
  have hp'p' : p'.IsPrime := hp'.1.1
  have hp'0 : p' ≠ ⊥ := fun e => hf (by simpa [e] using hp'.1.2 (Ideal.subset_span rfl))
  have e : p' = p := by
    by_contra hne'
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hp'p hne')
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.2 hp'0)
    have h3 : (⊥ : Ideal R).height + 1 + 1 ≤ 1 := ((add_le_add_left h2 1).trans h1).trans hht
    have h4 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr; exact le_add_self) h3
    exact absurd h4 (by decide)
  exact hg (Set.mem_iUnion₂.2 ⟨p', hfin.mem_toFinset.2 hp', e ▸ hgp⟩)

theorem exists_prime_dimensionLEOne {O : Type*} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] {f : O}
    (p₀ : Ideal O) (hp₀ : p₀.IsPrime) (hf : f ∉ p₀) :
    ∃ (P : Ideal O) (_ : P.IsPrime), f ∉ P ∧ Ring.DimensionLEOne (O ⧸ P) := by
  obtain ⟨P, ⟨hP, hfP⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian O O)
    {P : Ideal O | P.IsPrime ∧ f ∉ P} ⟨p₀, hp₀, hf⟩
  have hl : IsLocalRing (O ⧸ P) := .of_surjective' _ Ideal.Quotient.mk_surjective
  refine ⟨P, hP, hfP, dimensionLEOne_of_forall_mem (f := Ideal.Quotient.mk P f)
    (fun e => hfP (Ideal.Quotient.eq_zero_iff_mem.1 e)) fun q hq hq0 => ?_⟩
  by_contra hn
  refine hmax (q.comap (Ideal.Quotient.mk P)) ⟨inferInstance, hn⟩ (lt_of_le_of_ne ?_ fun e => hq0 ?_)
  · intro a ha
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
  · rw [eq_bot_iff]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : a ∈ P := e ▸ ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 this

theorem exists_dvr_of_dimensionLEOne {R Ω : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [Ring.DimensionLEOne R] (hR : ¬ IsField R) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω) [IsLocalHom φ] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (ψ : R →+* W) (ι : ResidueField W →+* Ω),
      Function.Injective ψ ∧ (ι.comp (residue W)).comp ψ = φ := by
  obtain ⟨V, hV, h⟩ := exists_discreteValuationSubring_dominating R (FractionRing R) (FractionRing R) hR
  obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).mp h
  have hi : Function.Injective ((algebraMap R (FractionRing R)).codRestrict V h1) :=
    fun a b hab => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val hab)
  letI : Algebra R V := ((algebraMap R (FractionRing R)).codRestrict V h1).toAlgebra
  have : FaithfulSMul R V := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hloc : IsLocalHom (algebraMap R V) := h2
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (isField_iff_maximalIdeal_eq.not.mp hR)
  have hfin := finite_quotient_span_of_birational (A := R) (B := V) (fun x => by
    obtain ⟨y, c, hc, hx⟩ := IsFractionRing.div_surjective (A := R) (x : FractionRing R)
    refine ⟨c, nonZeroDivisors.ne_zero hc, y, Subtype.ext ?_⟩
    change algebraMap R (FractionRing R) c * x = algebraMap R (FractionRing R) y
    rw [← hx]
    exact mul_div_cancel₀ _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc)) ha0
  have hle : Ideal.span {algebraMap R V a} ≤ maximalIdeal V :=
    (Ideal.span_singleton_le_iff_mem _).2 (map_nonunit _ a ha)
  have hf2 : Module.Finite R (ResidueField V) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ R hle).toLinearMap (Ideal.Quotient.factor_surjective hle)
  have hf3 : Module.Finite (ResidueField R) (ResidueField V) := Module.Finite.of_restrictScalars_finite R _ _
  letI : Algebra (ResidueField R) Ω := (ResidueField.lift φ).toAlgebra
  let ι₀ : ResidueField V →ₐ[ResidueField R] Ω := IsAlgClosed.lift
  let W := AdicCompletion (maximalIdeal V) V
  let e : ResidueField V ≃+* ResidueField W :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap V W)) (AdicCompletion.residueField_map_bijective V)
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, (algebraMap V W).comp (algebraMap R V),
    ι₀.toRingHom.comp e.symm.toRingHom, (algebraMap_adicCompletion_injective_of_dvr V).comp hi, ?_⟩
  ext r
  have h3 : residue W (algebraMap V W (algebraMap R V r)) = e (residue V (algebraMap R V r)) := rfl
  change ι₀ (e.symm (residue W (algebraMap V W (algebraMap R V r)))) = φ r
  rw [h3, e.symm_apply_apply]
  exact ι₀.commutes (residue R r)

theorem exists_dvr {O Ω : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] {f : O} (hfm : f ∈ maximalIdeal O)
    (p₀ : Ideal O) (hp₀ : p₀.IsPrime) (hf : f ∉ p₀) [Field Ω] [IsAlgClosed Ω] (φ : O →+* Ω) [IsLocalHom φ] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (ψ : O →+* W) (ι : ResidueField W →+* Ω),
      ψ f ≠ 0 ∧ (ι.comp (residue W)).comp ψ = φ := by
  obtain ⟨P, hP, hfP, hd⟩ := exists_prime_dimensionLEOne p₀ hp₀ hf
  have hl : IsLocalRing (O ⧸ P) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hF : ¬ IsField (O ⧸ P) := fun h =>
    hfP (eq_maximalIdeal (Ideal.Quotient.maximal_of_isField P h) ▸ hfm)
  have hk : ∀ a ∈ P, φ a = 0 := fun a ha => by
    by_contra h
    exact hP.ne_top (P.eq_top_of_isUnit_mem ha (isUnit_of_map_unit φ a (IsUnit.mk0 _ h)))
  have : IsLocalHom (Ideal.Quotient.lift P φ hk) := ⟨fun a ha => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact (isUnit_of_map_unit φ a ha).map _⟩
  obtain ⟨W, _, _, _, _, ψ, ι, h1, h2⟩ := exists_dvr_of_dimensionLEOne hF (Ideal.Quotient.lift P φ hk)
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, ψ.comp (Ideal.Quotient.mk P), ι,
    fun e => hfP (Ideal.Quotient.eq_zero_iff_mem.1 (h1 (e.trans (map_zero ψ).symm))), ?_⟩
  rw [← RingHom.comp_assoc, h2]
  rfl

end Algebra

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

theorem isOpen_preimage_bot {A O : Type} [CommRing A] [IsDedekindDomain A] [CommRing O] [IsLocalRing O]
    (g : PrimeSpectrum O → PrimeSpectrum A) (hg : Continuous g) : IsOpen (g ⁻¹' {⊥}) := by
  have hs : ∀ q, g q ≤ g (closedPoint O) := fun q =>
    (PrimeSpectrum.le_iff_specializes _ _).2 ((specializes_closedPoint q).map hg)
  by_cases h : g (closedPoint O) = ⊥
  · have : g ⁻¹' {⊥} = Set.univ := Set.eq_univ_of_forall fun q => le_bot_iff.1 (h ▸ hs q)
    exact this ▸ isOpen_univ
  · have hm : ∀ p : PrimeSpectrum A, p ≠ ⊥ → p.asIdeal.IsMaximal := fun p hp =>
      Ring.DimensionLEOne.maximalOfPrime (fun e => hp (PrimeSpectrum.ext e)) p.isPrime
    have : g ⁻¹' {⊥} = g ⁻¹' {g (closedPoint O)}ᶜ := by
      ext q
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff]
      refine ⟨fun e e' => h (e' ▸ e), fun e => ?_⟩
      by_contra e'
      exact e (PrimeSpectrum.ext ((hm _ e').eq_of_le (g (closedPoint O)).isPrime.ne_top (hs q)))
    rw [this]
    exact ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 (hm _ h)).isOpen_compl.preimage hg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem isOpen_preimage_range (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) {O : CommRingCat.{0}} [IsLocalRing O]
    (a : Spec O ⟶ Z.X) : IsOpen (a ⁻¹' Set.range Z.j) := by
  have := Z.jQ_open
  have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
  obtain ⟨U, hU, hU'⟩ := (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.isInducing.isOpen_iff.1
    Z.jQ.isOpenEmbedding.isOpen_range
  have hb : Set.range (spMap (algebraMap (𝓞 c.F) c.F)) = {(⊥ : PrimeSpectrum (𝓞 c.F))} := by
    have h0 : ∀ t, spMap (algebraMap (𝓞 c.F) c.F) t = (⊥ : PrimeSpectrum (𝓞 c.F)) := fun t => by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap (𝓞 c.F) c.F) t.asIdeal = ⊥
      rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
    ext p
    exact ⟨fun ⟨t, ht⟩ => ht ▸ h0 t, fun hp => ⟨(⊥ : PrimeSpectrum c.F), (h0 _).trans hp.symm⟩⟩
  have hr : Set.range Z.j = U ∩ Z.s ⁻¹' {(⊥ : PrimeSpectrum (𝓞 c.F))} := by
    rw [← hb, ← Scheme.Pullback.range_fst, ← Set.image_preimage_eq_inter_range, hU', ← Set.range_comp]
    rfl
  rw [hr, Set.preimage_inter]
  exact (hU.preimage a.continuous).inter
    (isOpen_preimage_bot (fun q => Z.s (a q)) (Z.s.continuous.comp a.continuous))

theorem exists_trait_through : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] (x : Sp Ω ⟶ Z.X), ∃ (T : Formalism.L2.Pj.CDVR) (χ : Sp T.V ⟶ Z.X) (y : Sp T.Fr ⟶ Xo.XF c)
    (ι : IsLocalRing.ResidueField T.V →+* Ω),
    y ≫ Z.j = Out.jK T.V ≫ χ ∧ spMap ι ≫ spMap (IsLocalRing.residue T.V) ≫ χ = x := by
  intro E _ _ _ H D l Xo c Z Ω _ _ x
  obtain ⟨h₁, -, -, _, _, _, _⟩ := GlobalTheory.ModelRelCompare.densePart Z (GlobalTheory.ModelRelCompare.isDedFrac_in_use c).1
  by_cases hx : x (closedPoint Ω) ∈ Set.range Z.j
  · obtain ⟨u, hu⟩ := GlobalTheory.HomExt.exists_lift_of_range_subset Z.j x (by
      rintro _ ⟨t, rfl⟩
      rwa [Subsingleton.elim (α := PrimeSpectrum Ω) t (closedPoint Ω)])
    have : CharZero Ω := GlobalTheory.TorRef.charZero_of_point (K := .of Ω) u
    obtain ⟨h₁, h₂, h₃⟩ := GlobalTheory.FrameCmp.cDvr_powerSeries Ω
    have : IsLocalHom (PowerSeries.constantCoeff (R := Ω)) := ⟨fun a ha => PowerSeries.isUnit_iff_constantCoeff.2 ha⟩
    refine ⟨{ V := PowerSeries Ω }, spMap (PowerSeries.C (R := Ω)) ≫ x,
      Out.jK _ ≫ spMap (PowerSeries.C (R := Ω)) ≫ u, ResidueField.lift PowerSeries.constantCoeff, ?_, ?_⟩
    · simp only [Category.assoc, hu]
    · have e : spMap (ResidueField.lift (PowerSeries.constantCoeff (R := Ω))) ≫ spMap (residue (PowerSeries Ω)) ≫
          spMap (PowerSeries.C (R := Ω)) = 𝟙 _ := by
        rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id]
        congr 1
      simpa only [Category.assoc, Category.id_comp] using congrArg (· ≫ x) e
  · let ξ := x (closedPoint Ω)
    let O := Z.X.presheaf.stalk ξ
    obtain ⟨η, hη, hs⟩ := exists_mem_genericPoints_specializes ξ
    have hη' := genericPoints_subset_range_of_isDominant Z.j hη
    have h1 : η ∈ Set.range (Z.X.fromSpecStalk ξ) := by
      rw [Scheme.range_fromSpecStalk]
      exact hs
    obtain ⟨q, rfl⟩ := h1
    obtain ⟨_, ⟨f, rfl⟩, hqf, hf⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := q) hη' (isOpen_preimage_range Z (Z.X.fromSpecStalk ξ))
    have hfm : f ∈ maximalIdeal O := by
      by_contra hn
      have : Z.X.fromSpecStalk ξ (closedPoint (Z.X.presheaf.stalk ξ)) ∈ Set.range Z.j :=
        hf (show closedPoint O ∈ PrimeSpectrum.basicOpen f from hn)
      rw [Scheme.fromSpecStalk_closedPoint] at this
      exact hx this
    obtain ⟨W, _, _, _, _, ψ, ι, hψ, hι⟩ := exists_dvr (O := O) (Ω := Ω) hfm q.asIdeal q.isPrime hqf
      (Scheme.stalkClosedPointTo x).hom
    let a : Sp W ⟶ Z.X := Spec.map (CommRingCat.ofHom ψ) ≫ Z.X.fromSpecStalk ξ
    obtain ⟨y, hy⟩ := GlobalTheory.HomExt.exists_lift_of_range_subset Z.j
      (spMap (algebraMap W (FractionRing W)) ≫ a) (by
        rintro _ ⟨t, rfl⟩
        have : spMap (algebraMap W (FractionRing W)) t = (⊥ : PrimeSpectrum W) := by
          apply PrimeSpectrum.ext
          change Ideal.comap (algebraMap W (FractionRing W)) t.asIdeal = ⊥
          rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
          exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
        rw [Scheme.Hom.comp_apply, this]
        exact hf (a := PrimeSpectrum.comap ψ ⊥) hψ)
    have hc : CharZero (FractionRing W) := GlobalTheory.TorRef.charZero_of_point (K := .of (FractionRing W)) y
    have hc' : CharZero W := ⟨fun p q e => Nat.cast_injective (R := FractionRing W) (by
      simpa using congrArg (algebraMap W (FractionRing W)) e)⟩
    refine ⟨{ V := W }, a, y, ι, hy, ?_⟩
    have e : spMap ι ≫ spMap (residue W) ≫ Spec.map (CommRingCat.ofHom ψ) =
        Spec.map (Scheme.stalkClosedPointTo x) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext hι
    refine Eq.trans ?_ (Scheme.Spec_stalkClosedPointTo_fromSpecStalk x)
    rw [← e]
    simp only [a, Category.assoc]
    rfl

end GlobalTheory.GeomTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenFrameChartVectorsCompactFlagSpaceAffi
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

section
open GlobalTheory.FlagMod GlobalTheory.Reg
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CompHS.exists_eigFrame_vecAt₀ : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(Y₀ TF.X Z, W)), (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z = spMap φ → ∀ (k : TF.X.F.J) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (x' : Sp Γ(Y₀ TF.X Z, W) ⟶ TF.Y.X) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x'), ∃ fr : GlobalTheory.ShFam.EigFrame TF.Y φ x', ∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt k _ hz hx τ j)).left := by
  intro E _ _ _ H Dw l Xo c TF Z W hW φ hφ k hz x' hx
  subst hx
  haveI := TF.X.proper
  haveI := TF.smooth
  haveI : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth Dw.dim TF.Y.s
  haveI : LocallyOfFiniteType TF.Y.s := inferInstance
  haveI : LocallyOfFiniteType (str₀ TF.X Z) := by unfold str₀ flagStr; infer_instance
  haveI : IsLocallyNoetherian (Y₀ TF.X Z) := LocallyOfFiniteType.isLocallyNoetherian (str₀ TF.X Z)
  obtain ⟨K, _, ρ, hρ, hK⟩ := GlobalTheory.T.affineOpen_ring_injects_to_ring_mapping_to_dense (Y₀ TF.X Z) (U₀ TF.X Z) (dense_U₀ TF.X Z) W hW
  letI : Algebra c.F K := (ρ.comp φ).toAlgebra
  have hz' : ⊤ ≤ (spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ⁻¹ᵁ TF.X.F.U k := FlagMod.le_preimage_comp _ hz
  have hr : Set.range ((spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π) ⊆ Set.range TF.Y.j := by
    rintro _ ⟨s, rfl⟩
    exact hK (Set.mem_univ s)
  let yK := IsOpenImmersion.lift TF.Y.j ((spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π) hr
  have hyK : yK ≫ TF.Y.j = (spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π := IsOpenImmersion.lift_fac _ _ _
  have hjs : TF.Y.j ≫ TF.Y.s = pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) := by
    have h1 : spMap (RingHom.id c.F) = 𝟙 _ := by
      unfold spMap; rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, TF.Y.jQ_over, h1, Category.comp_id]
  have hy : yK ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    rw [← hjs, ← Category.assoc, hyK]
    have h2 : spMap ρ ≫ spMap φ = spMap (algebraMap c.F K) := by
      unfold spMap; rw [← Spec.map_comp]; rfl
    rw [← h2, ← hφ]
    simp only [Category.assoc]
  have key : ∀ (x'' : Sp K ⟶ TF.Y.X) (hx : (spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π = x''),
      (∀ σ, initSpan K (TF.X.F.vecAt k _ hz' hx σ) (Dw.mult σ) = eigLie c x'' σ) →
      ∀ σ, initSpan K (TF.X.F.vecAt k _ hz' rfl σ) (Dw.mult σ) =
        eigLie c ((spMap ρ ≫ (hW.fromSpec ≫ inc₀ TF.X Z)) ≫ TF.X.π) σ := by
    rintro x'' rfl h
    exact h
  exact GlobalTheory.ChartEigFrame.exists_eigFrame_of_top ρ hρ φ rfl (hW.fromSpec ≫ inc₀ TF.X Z) k hz hz'
    (key _ hyK.symm fun σ => TF.X.top K yK hy _ hyK.symm k hz' σ)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerProjectionsExtendFromGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PowExtend

theorem isMonHom_of_components {𝒞 : Type*} [Category 𝒞] [CartesianMonoidalCategory 𝒞] {ι : Type}
    {A B C : 𝒞} [MonObj A] [MonObj B] [MonObj C] (p : ι → (B ⟶ C)) (hp : ∀ a, IsMonHom (p a))
    (hl : IsLimit (Fan.mk B p)) (e : A ⟶ B) (he : ∀ a, IsMonHom (e ≫ p a)) : IsMonHom e := by
  refine ⟨?_, ?_⟩
  · refine Fan.IsLimit.hom_ext hl _ _ fun a => ?_
    have := hp a
    have := he a
    change (_ ≫ e) ≫ p a = _ ≫ p a
    rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · refine Fan.IsLimit.hom_ext hl _ _ fun a => ?_
    have := hp a
    have := he a
    change (_ ≫ e) ≫ p a = (_ ≫ _) ≫ p a
    rw [Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
      tensorHom_comp_tensorHom]

theorem exists_iso_of_universal {𝒞 : Type*} [Category 𝒞] {ι : Type} {A B C : 𝒞} (p : ι → (B ⟶ C))
    (hl : IsLimit (Fan.mk B p)) (q : ι → (A ⟶ C))
    (hq : ∀ (T : 𝒞) (y : ι → (T ⟶ C)), ∃! x : T ⟶ A, ∀ a, x ≫ q a = y a) :
    ∃ e : A ≅ B, ∀ a, e.hom ≫ p a = q a := by
  have hA : IsLimit (Fan.mk A q) :=
    mkFanLimit _ (fun s => (hq s.pt s.proj).exists.choose)
      (fun s a => (hq s.pt s.proj).exists.choose_spec a)
      (fun s m hm => (hq s.pt s.proj).unique hm (hq s.pt s.proj).exists.choose_spec)
  exact ⟨hA.conePointUniqueUpToIso hl, fun a => hA.conePointUniqueUpToIso_hom_comp hl ⟨a⟩⟩

theorem universal_of_iso {𝒞 : Type*} [Category 𝒞] {ι : Type} {A B C : 𝒞} (p : ι → (B ⟶ C))
    (hl : IsLimit (Fan.mk B p)) (E : A ≅ B) (T : 𝒞) (y : ι → (T ⟶ C)) :
    ∃! x : T ⟶ A, ∀ a, x ≫ (E.hom ≫ p a) = y a := by
  refine ⟨hl.lift (Fan.mk T y) ≫ E.inv, fun a => ?_, fun x hx => ?_⟩
  · rw [Category.assoc, E.inv_hom_id_assoc]
    exact hl.fac (Fan.mk T y) ⟨a⟩
  · rw [Iso.eq_comp_inv]
    refine Fan.IsLimit.hom_ext hl _ _ fun a => ?_
    exact ((Category.assoc _ _ _).trans (hx a)).trans (hl.fac (Fan.mk T y) ⟨a⟩).symm

theorem exists_pow_projections : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G C : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj C] [IsCommMonObj C], IsSemiAbelian G → IsAbelianScheme C → ∀ pr' : Fin 8 → ((Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj C), (∀ a, IsMonHom (pr' a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ (Over.pullback (jK R)).obj C)), ∃! x : T' ⟶ (Over.pullback (jK R)).obj G, ∀ a, x ≫ pr' a = y a) → ∃ prO : Fin 8 → (G ⟶ C), (∀ a, IsMonHom (prO a)) ∧ (∀ a, (Over.pullback (jK R)).map (prO a) = pr' a) ∧ ∀ (T' : Over (Sp R)) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ G, ∀ a, x ≫ prO a = y a := by
  intro R _ _ _ _ G C _ _ _ _ hG hC pr' hm hu
  have hH : IsSemiAbelian (powObj C 8) :=
    GlobalTheory.SemiPow.isSemiAbelian_of_isPowGrp _ C (powObj C 8) 8 (powIsPowGrp C 8)
      (GlobalTheory.isSemiAbelian_of_isAbelianScheme C hC)
  let prK : Fin 8 → ((Over.pullback (jK R)).obj (powObj C 8) ⟶ (Over.pullback (jK R)).obj C) :=
    fun i => (Over.pullback (jK R)).map (powPr C i)
  have hlim : IsLimit (Fan.mk ((Over.pullback (jK R)).obj (powObj C 8)) prK) :=
    isLimitFanMkObjOfIsLimit (Over.pullback (jK R)) (fun _ : Fin 8 => C) (powPr C) (powIsLimit C 8)
  have hprKm : ∀ i, IsMonHom (prK i) := fun i =>
    inferInstanceAs (IsMonHom ((Over.pullback (jK R)).map (powPr C i)))
  obtain ⟨e, he⟩ := exists_iso_of_universal prK hlim pr' hu
  have hem : IsMonHom e.hom := isMonHom_of_components prK hprKm hlim e.hom fun a => by
    rw [he a]; exact hm a
  obtain ⟨E, ⟨hE, hEe⟩, -⟩ := @GlobalTheory.SemiAbExtDomain.existsUnique_iso_extension_generic R _ _ _ _
    (FractionRing R) _ _ _ G (powObj C 8) _ _ hG hH e hem
  refine ⟨fun a => E.hom ≫ powPr C a, fun a => inferInstance, fun a => ?_,
    universal_of_iso (powPr C) (powIsLimit C 8) E⟩
  rw [Functor.map_comp, ← he a]
  exact congrArg (· ≫ prK a) hEe

end GlobalTheory.PowExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndoImageTorsionPointUniformisedModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_endo_image_torsion_point_uniformised_model : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (f : ρ.P.A ⟶ ρ.P.A), IsMonHom f → ∀ (m : ℕ) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x ^ m = 1 → ∃ x₂ : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x₂.left ≫ u.φ = x.left ≫ u.φ ≫ f.left ∧ x₂ ^ m = 1 := by
  first | exact @GlobalTheory.EndoPt.exists_endo_point | exact GlobalTheory.EndoPt.exists_endo_point | (intros; apply GlobalTheory.EndoPt.exists_endo_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddings
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

namespace GlobalTheory.CMTypeEmb

theorem card_eq_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) : Fintype.card I = Module.finrank ℚ (FR E) := by
  have hc : Fintype.card I = Fintype.card (InfinitePlace E) :=
    Fintype.card_of_bijective (GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hφ)
  have hE : Fintype.card (InfinitePlace E) = Fintype.card (InfinitePlace (FR E)) :=
    Fintype.card_congr (IsCMField.equivInfinitePlace E)
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank (FR E)
  have hr : InfinitePlace.nrComplexPlaces (FR E) = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (FR E)
  have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := FR E)
  omega

theorem exists_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∃ e : I ≃ Emb (FR E), ∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ) := by
  intro E _ _ _ I _ φ hφ
  have hcard : Fintype.card I = Module.finrank ℚ (FR E) := card_eq_finrank hφ
  let e₀ : Fin (Module.finrank ℚ (FR E)) ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  obtain ⟨e, he⟩ := GlobalTheory.CMTypeRestrict.exists_equiv_realEmbeddings E I φ hφ e₀
  refine ⟨e₀.symm.trans e, fun i x ↦ ?_⟩
  have := he (e₀.symm i) x
  simp only [Equiv.apply_symm_apply] at this
  simp only [Equiv.trans_apply]
  exact this.symm

end GlobalTheory.CMTypeEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalTrivialisationCompMonHomStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_cubicalTrivialisation_comp_monHom : ∀ (S : Scheme.{0}) (G H H' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj H] [GrpObj H'] (P : GlobalTheory.UU.CP G) (i : H' ⟶ G) (e : H ⟶ H'), IsMonHom e → ∀ σ : GlobalTheory.UU.CubTriv P.c i, GlobalTheory.UU.CubTriv.Even (P := P) σ → ∃ σ₁ : GlobalTheory.UU.CubTriv P.c (e ≫ i), GlobalTheory.UU.CubTriv.Even (P := P) σ₁ := by
  first | exact @GlobalTheory.CubTrivComp.exists_even_comp | exact GlobalTheory.CubTrivComp.exists_even_comp | (intros; apply GlobalTheory.CubTrivComp.exists_even_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPointPolarisedFibreUniformisedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fieldPoint_polarised_fibre_uniformised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, IsProper (G.hom ∣_ W) → ∀ y : PrimeSpectrum R, y ∈ W → y.asIdeal ≠ ⊥ → ∃ (K₁ : Type) (_ : Field K₁) (z : Sp K₁ ⟶ Sp R), z (closedPoint K₁) = y ∧ IsProper (pullback.snd G.hom z) ∧ RelAmple ((Over.pullback z).obj G) (U.LG.L.pull (pullback.fst G.hom z)) ∧ KTriv ((Over.pullback z).obj G) (U.LG.L.pull (pullback.fst G.hom z)) := by
  first | exact @GlobalTheory.PolPoint.exists_field_point_polarised | exact GlobalTheory.PolPoint.exists_field_point_polarised | (intros; apply GlobalTheory.PolPoint.exists_field_point_polarised <;> assumption)
end

