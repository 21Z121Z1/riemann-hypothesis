import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwaySurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoFibreOfPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.NearFibreIso

open GlobalTheory.DenseFibreIso

variable {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R) (f : Y ⟶ X)

def Near (Q : MorphismProperty Scheme.{0}) (x : X) : Prop :=
  ∃ (T T' : Scheme.{0}) (g : T ⟶ X) (g' : T' ⟶ Y) (f' : T' ⟶ T),
    IsPullback f' g' g f ∧ IsOpenImmersion g ∧ x ∈ Set.range g ∧ Q f'

theorem Near.of_pullback {Q : MorphismProperty Scheme.{0}} {T T' : Scheme.{0}} {g : T ⟶ X}
    {g' : T' ⟶ Y} {f' : T' ⟶ T} (H : IsPullback f' g' g f) [IsOpenImmersion g] {y : T}
    (h : Near f' Q y) : Near f Q (g y) := by
  obtain ⟨T₀, T₀', g₀, g₀', f₀, H₀, hg₀, ⟨z, rfl⟩, hQ⟩ := h
  have := hg₀
  refine ⟨T₀, T₀', g₀ ≫ g, g₀' ≫ g', f₀, H₀.paste_vert H, inferInstance, ⟨z, ?_⟩, hQ⟩
  simp

theorem isIso_fibre_of_pullback {S : Scheme.{0}} (t : S ⟶ Sp R)
    [IsIso (pullback.snd f (pullback.fst s t))] {T T' : Scheme.{0}} {g : T ⟶ X} {g' : T' ⟶ Y}
    {f' : T' ⟶ T} (H : IsPullback f' g' g f) :
    IsIso (pullback.snd f' (pullback.fst (g ≫ s) t)) := by
  have H' : IsPullback (pullback.snd f' (pullback.fst (g ≫ s) t))
      (pullback.fst f' (pullback.fst (g ≫ s) t) ≫ g') (pullback.fst (g ≫ s) t ≫ g) f :=
    (IsPullback.of_hasPullback _ _).flip.paste_vert H
  refine DenseFibreIso.isIso_of_fibre s f t H' (pullback.snd _ _) ?_
  rw [Category.assoc, pullback.condition]

variable (K : Type) [Field K] [Algebra R K]

theorem near_isFinite [IsProper f]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) : Near f @IsFinite x := by
  have hsub : (f ⁻¹' {x}).Subsingleton := by
    let k : Sp K := IsLocalRing.closedPoint K
    have hk : s x = spMap (algebraMap R K) k := by
      apply PrimeSpectrum.ext
      rw [← hx, RingHom.ker_eq_comap_bot, ← Ideal.eq_bot_of_prime k.asIdeal]
      rfl
    obtain ⟨x', hx', -⟩ := Scheme.Pullback.exists_preimage_pullback x k hk
    intro y₁ hy₁ y₂ hy₂
    obtain ⟨z₁, hz₁, hz₁'⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := pullback.fst s (spMap (algebraMap R K))) y₁ x' (hy₁.trans hx'.symm)
    obtain ⟨z₂, hz₂, hz₂'⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := pullback.fst s (spMap (algebraMap R K))) y₂ x' (hy₂.trans hx'.symm)
    have hz : z₁ = z₂ :=
      (pullback.snd f (pullback.fst s (spMap (algebraMap R K)))).isOpenEmbedding.injective
        (hz₁'.trans hz₂'.symm)
    rw [← hz₁, ← hz₂, hz]
  obtain ⟨V, hxV, hV⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f x hsub.finite
  refine ⟨V, f ⁻¹ᵁ V, V.ι, (f ⁻¹ᵁ V).ι, f ∣_ V, isPullback_morphismRestrict f V, inferInstance, ?_, hV⟩
  simpa using hxV

theorem near_isClosedImmersion [hfin : IsFinite f]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f @IsClosedImmersion x := by
  refine DenseFibreIso.local_of_ring s f @IsClosedImmersion K ?_ x hx
  intro A B _ _ _ _ _ _ j j' _ H _ hbij m
  have hf : IsFinite (spMap (algebraMap A B)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite) H.flip hfin
  have : Module.Finite A B := RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hf)
  obtain ⟨a, ha, hsurj⟩ := DenseFibreIso.exists_away_surjective (A ⊗[R] K) hbij.2 m
  exact ⟨a, ha, IsClosedImmersion.spec_of_surjective _ hsurj⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem near_isIso [hcl : IsClosedImmersion f] [IsLocallyNoetherian X] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  refine DenseFibreIso.local_of_ring s f (MorphismProperty.isomorphisms _) K ?_ x hx
  intro A B _ _ _ _ _ _ j j' hj H hjs hbij m
  have : IsOpenImmersion j' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H hj
  have hci : IsClosedImmersion (spMap (algebraMap A B)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) H.flip hcl
  have hs : Function.Surjective (algebraMap A B) := by
    have h1 := (spMap (algebraMap A B)).app_surjective ⊤ (isAffineOpen_top _)
    have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A B))
    intro b
    obtain ⟨c, hc⟩ := h1 ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom c, ?_⟩
    have h3 := congr_arg (fun k => (ConcreteCategory.hom k) c) h2
    simp only [CategoryTheory.comp_apply, CommRingCat.hom_ofHom] at h3
    rw [← h3]
    change (Scheme.ΓSpecIso (CommRingCat.of B)).hom ((spMap (algebraMap A B)).app ⊤ c) = b
    rw [hc]
    simp
  have : IsLocallyNoetherian (Sp A) := isLocallyNoetherian_of_isOpenImmersion j
  have : IsNoetherian (Sp A) := {}
  have : IsNoetherianRing A := isNoetherian_Spec.mp this
  have hflat : Flat (spMap (algebraMap R B)) := by
    have e : spMap (algebraMap R B) = spMap (algebraMap A B) ≫ spMap (algebraMap R A) := by
      change Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    rw [e, ← hjs, reassoc_of% H.w]
    infer_instance
  have : Module.Flat R B := RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hflat)
  obtain ⟨a, ha, hb⟩ := DenseFibreIso.exists_away_bijective R K hs hbij.1 m
  exact ⟨a, ha, isIso_SpecMap_iff.mpr hb⟩

theorem near_isIso_of_isProper [IsProper f] [IsLocallyNoetherian X] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  obtain ⟨T, T', g, g', f', H, hg, ⟨y, rfl⟩, hQ⟩ := near_isFinite s f K x hx
  have := hg
  have : IsFinite f' := hQ
  have : IsIso (pullback.snd f' (pullback.fst (g ≫ s) (spMap (algebraMap R K)))) :=
    isIso_fibre_of_pullback s f _ H
  have hy : RingHom.ker (algebraMap R K) = ((g ≫ s) y).asIdeal := by simpa using hx
  obtain ⟨T₂, T₂', g₂, g₂', f₂, H₂, hg₂, ⟨y₂, rfl⟩, hQ₂⟩ := near_isClosedImmersion (g ≫ s) f' K y hy
  have := hg₂
  have : IsClosedImmersion f₂ := hQ₂
  have : IsIso (pullback.snd f₂ (pullback.fst (g₂ ≫ g ≫ s) (spMap (algebraMap R K)))) :=
    isIso_fibre_of_pullback (g ≫ s) f' _ H₂
  have : IsLocallyNoetherian T₂ := isLocallyNoetherian_of_isOpenImmersion (g₂ ≫ g)
  have : IsOpenImmersion g' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H hg
  have : IsOpenImmersion g₂' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H₂ hg₂
  have : Flat (f₂ ≫ g₂ ≫ g ≫ s) := by
    rw [reassoc_of% H₂.w, reassoc_of% H.w]
    infer_instance
  have hy₂ : RingHom.ker (algebraMap R K) = ((g₂ ≫ g ≫ s) y₂).asIdeal := by simpa using hy
  exact Near.of_pullback f H (Near.of_pullback f' H₂ (near_isIso (g₂ ≫ g ≫ s) f₂ K y₂ hy₂))

theorem isOpen_near (Q : MorphismProperty Scheme.{0}) : IsOpen {x : X | Near f Q x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨T, T', g, g', f', H, hg, hx, hQ⟩
  have := hg
  exact ⟨Set.range g, fun z hz => ⟨T, T', g, g', f', H, hg, hz, hQ⟩, g.isOpenEmbedding.isOpen_range, hx⟩

theorem isIso_of_near {S : Scheme.{0}} (t : S ⟶ X)
    (h : ∀ y : S, Near f (MorphismProperty.isomorphisms _) (t y)) : IsIso (pullback.snd f t) := by
  choose T T' g g' f' H hg hx hQ using h
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun y => t ⁻¹ᵁ (g y).opensRange) ?_ fun y => ?_
  · refine eq_top_iff.mpr fun z _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨z, ?_⟩
    simpa using hx z
  · have := hg y
    have : IsIso (f' y) := hQ y
    have hle : Set.range (Scheme.Opens.ι (t ⁻¹ᵁ (g y).opensRange) ≫ t) ⊆ Set.range (g y) := by
      rintro _ ⟨z, rfl⟩
      exact z.2
    have hu := IsOpenImmersion.lift_fac (g y) _ hle
    have big := (isPullback_morphismRestrict (pullback.snd f t) (t ⁻¹ᵁ (g y).opensRange)).paste_vert
      (IsPullback.of_hasPullback f t).flip
    rw [← hu] at big
    rw [MorphismProperty.isomorphisms.iff]
    exact (big.of_bot' (H y)).isIso_fst_of_isIso

theorem main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Y X : Scheme.{0}) (s : X ⟶ Sp R) (φ : Y ⟶ X) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → IsProper φ → Flat (φ ≫ s) → IsIso (pullback.snd φ (pullback.fst s (spMap x))) → ∃ f : R, x f ≠ 0 ∧ IsIso (pullback.snd φ (pullback.fst s (spMap (algebraMap R (Localization.Away f))))) := by
  intro R _ _ Y X s φ K _ x hs _ hφ hflat hiso
  let : Algebra R K := x.toAlgebra
  have : IsIso (pullback.snd φ (pullback.fst s (spMap (algebraMap R K)))) := hiso
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have hU : IsOpen {z : X | Near φ (MorphismProperty.isomorphisms _) z} := isOpen_near φ _
  have hZ : IsClosed (s '' {z : X | Near φ (MorphismProperty.isomorphisms _) z}ᶜ) :=
    s.isClosedMap _ hU.isClosed_compl
  let p : PrimeSpectrum R := ⟨RingHom.ker x, RingHom.ker_isPrime x⟩
  have hp : p ∉ s '' {z : X | Near φ (MorphismProperty.isomorphisms _) z}ᶜ := by
    rintro ⟨z, hz, hsz⟩
    refine hz (near_isIso_of_isProper s φ K z ?_)
    rw [hsz]
    rfl
  obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp hZ.isOpen_compl
  refine ⟨f, fun h0 => (PrimeSpectrum.mem_basicOpen _ _).mp hpf (RingHom.mem_ker.mpr h0), ?_⟩
  refine isIso_of_near φ _ fun y => ?_
  by_contra hy
  have hmem : s (pullback.fst s (spMap (algebraMap R (Localization.Away f))) y) ∈
      PrimeSpectrum.basicOpen f := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    refine (PrimeSpectrum.mem_basicOpen _ _).mpr fun hf => ?_
    have hf' : algebraMap R (Localization.Away f) f ∈
        (pullback.snd s (spMap (algebraMap R (Localization.Away f))) y).asIdeal := hf
    exact (pullback.snd s (spMap (algebraMap R (Localization.Away f))) y).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hf' (IsLocalization.Away.algebraMap_isUnit f))
  exact hsub hmem ⟨_, hy, rfl⟩

end GlobalTheory.NearFibreIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPrimitiveRootMapOfNatCastNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.IntegersAway

theorem isPrimitiveRoot_map_of_natCast_ne_zero {R K : Type} [CommRing R] [IsDomain R] [CharZero R] [Field K] {k : ℕ}
    (hk : 0 < k) {z : R} (hz : IsPrimitiveRoot z k) (β : R →+* K) (hβ : (k : K) ≠ 0) : IsPrimitiveRoot (β z) k := by
  have : NeZero (k : K) := ⟨hβ⟩
  have h : (Polynomial.cyclotomic k R).IsRoot z := hz.isRoot_cyclotomic hk
  rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic k β]
  exact h.map

theorem exists_tBase_of_numberField {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ) {k : ℕ} (hk : 0 < k)
    {z r : F} (hz : IsPrimitiveRoot z k) (hr : IsIntegral ℤ r) :
    ∃ (o : Type) (_ : CommRing o) (b : TBase o k) (em : o →+* ℂ) (ρ : o) (_ : Algebra o F), ArBase em ∧
      IsFractionRing o F ∧ (∀ x, φ (algebraMap o F x) = em x) ∧ algebraMap o F ρ = r ∧
      algebraMap o F (b.ζ : o) = z := by
  obtain ⟨em, hem, hcomp⟩ := exists_arBase_away φ hk.ne'
  have hn' : (k : 𝓞 F) ≠ 0 := by exact_mod_cast hk.ne'
  have hM : Submonoid.powers (k : 𝓞 F) ≤ nonZeroDivisors (𝓞 F) := powers_le_nonZeroDivisors_of_noZeroDivisors hn'
  let o := Localization.Away (k : 𝓞 F)
  have hu : IsUnit (algebraMap (𝓞 F) F (k : 𝓞 F)) := by simpa using hk.ne'
  let j : o →+* F := IsLocalization.Away.lift (k : 𝓞 F) hu
  have hj : ∀ x, j (algebraMap (𝓞 F) o x) = algebraMap (𝓞 F) F x := IsLocalization.Away.lift_eq _ hu
  let alg : Algebra o F := j.toAlgebra
  have : IsScalarTower (𝓞 F) o F := IsScalarTower.of_algebraMap_eq fun x => (hj x).symm
  let z₀ : 𝓞 F := ⟨z, hz.isIntegral hk⟩
  have hz₀ : IsPrimitiveRoot z₀ k :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 F) F) hz RingOfIntegers.coe_injective
  have hko : IsUnit (k : o) := by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := o) (k : 𝓞 F)
  have hzu : IsUnit (algebraMap (𝓞 F) o z₀) := (hz₀.isUnit hk.ne').map _
  refine ⟨o, inferInstance, ⟨hzu.unit, hko, fun K _ β => ?_⟩, em, algebraMap (𝓞 F) o ⟨r, hr⟩, alg, hem,
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (k : 𝓞 F)) o F, ?_, hj _, hj _⟩
  · refine isPrimitiveRoot_map_of_natCast_ne_zero hk hz₀ (β.comp (algebraMap (𝓞 F) o)) ?_
    simpa using (hko.map β).ne_zero
  · have : φ.comp j = em := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (k : 𝓞 F)) ?_
      rw [hcomp]
      ext x
      simp [hj]
    exact fun x => DFunLike.congr_fun this x

theorem exists_tBase_fractionRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ (o : Type) (_ : CommRing o) (b : TBase o l.A) (em : o →+* ℂ) (ρ : o) (_ : Algebra o (KA l)), ArBase em ∧ IsFractionRing o (KA l) ∧ (∀ x, ((algebraMap o (KA l) x : KA l) : ℂ) = em x) ∧ algebraMap o (KA l) ρ = (baseKA l).ρ ∧ algebraMap o (KA l) (b.ζ : o) = (baseKA l).ζ := by
  intro E _ _ _ H l
  have : FiniteDimensional ℚ (KA l) := by
    refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    rcases hx with rfl | rfl
    · refine IsIntegral.of_pow two_pos ?_
      rw [H.sqrt_neg_disc_sq]
      exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
    · refine IsIntegral.of_pow l.A_pos ?_
      rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
      exact isIntegral_one
  have : NumberField (KA l) := {}
  have hr : IsIntegral ℤ (baseKA l).ρ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [(baseKA l).ρ_sq]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := KA l) (x := (H.d : ℤ))).neg
  exact exists_tBase_of_numberField (KA l).val.toRingHom l.A_pos (baseKA l).ζ_prim hr

end GlobalTheory.ZM.IntegersAway
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelOnFactorOfEighthPowerAbelianScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem levelFactor_comp {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ}
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (c : Fin n → ℤ) (u : Fin m) : π u (∏ i, P i ^ c i) = L (bas c u) := by
  let φ : Λ →+ Additive H := AddMonoidHom.mk' (fun x => Additive.ofMul (L x)) hL
  have hφ : ∀ x, L x = Additive.toMul (φ x) := fun x => rfl
  have hc : bas c u = ∑ i, c i • bas (Pi.single i 1) u := by
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs : (Pi.single i (c i) : Fin n → ℤ) = c i • (Pi.single i 1 : Fin n → ℤ) := by
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [hs, map_zsmul, Pi.smul_apply]
  rw [map_prod, hc, hφ, map_sum, toMul_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow, hP, map_zsmul, toMul_zsmul]
  rfl

theorem levelFactor_torsion {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ} (u : Fin m)
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (k : ℕ) (ht : ∀ i, P i ^ k = 1) (x : Λ) : L x ^ k = 1 := by
  obtain ⟨c, hc⟩ : ∃ c, bas c = Pi.single u x := ⟨bas.symm (Pi.single u x), bas.apply_symm_apply _⟩
  have h1 := levelFactor_comp bas P π L hL hP c u
  rw [hc, Pi.single_eq_same] at h1
  have hk : ∀ i, (P i ^ c i) ^ k = 1 := fun i => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]
  rw [← h1, ← map_pow, ← Finset.prod_pow, Finset.prod_eq_one (fun i _ => hk i), map_one]

theorem levelFactor_bij {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ} (u : Fin m)
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (k : ℕ) (hk : 0 < k) (ht : ∀ i, P i ^ k = 1)
    (hπ : ∀ y : Fin m → H, ∃! x : G, ∀ u, π u x = y u)
    (hb : ∀ y : G, y ^ k = 1 → ∃! c : Fin n → ZMod k, (List.ofFn fun i => P i ^ (c i).val).prod = y) :
    (∀ x, L x = 1 ↔ ∃ y, x = k • y) ∧ ∀ y : H, y ^ k = 1 → ∃ x, L x = y := by
  have : NeZero k := ⟨hk.ne'⟩
  have hcomp := levelFactor_comp bas P π L hL hP
  have htor := levelFactor_torsion u bas P π L hL hP k ht
  have L0 : L 0 = 1 := mul_left_cancel (a := L 0) (by rw [← hL, add_zero, _root_.mul_one])
  have hsm : ∀ (j : ℕ) (x : Λ), L (j • x) = L x ^ j := by
    intro j x
    induction j with
    | zero => rw [zero_smul, L0, pow_zero]
    | succ j ih => rw [succ_nsmul, hL, ih, pow_succ]
  have hone : ∀ a : G, (∀ v, π v a = 1) → a = 1 := by
    intro a ha
    obtain ⟨x, -, hx⟩ := hπ (fun _ => 1)
    exact (hx a ha).trans (hx 1 (fun v => map_one _)).symm
  have hred : ∀ w : Fin n → ℤ,
      ∏ i, P i ^ w i = (List.ofFn fun i => P i ^ ((w i : ZMod k).val)).prod := by
    intro w
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [zpow_eq_zpow_emod (w i) (n := (k : ℤ)) (by rw [zpow_natCast]; exact ht i),
      ← ZMod.val_intCast, zpow_natCast]
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun y hy => ?_⟩
  · obtain ⟨w, hw⟩ : ∃ w, bas w = Pi.single u x := ⟨_, bas.apply_symm_apply _⟩
    have hg : ∏ i, P i ^ w i = 1 := hone _ fun v => by
      rw [hcomp, hw]
      by_cases hv : v = u
      · subst hv; rw [Pi.single_eq_same, hx]
      · rw [Pi.single_eq_of_ne hv, L0]
    obtain ⟨c0, -, huniq⟩ := hb 1 (one_pow _)
    have e1 := huniq (fun i => (w i : ZMod k)) ((hred w).symm.trans hg)
    have e2 := huniq 0 (by simp)
    have hdvd : ∀ i, (k : ℤ) ∣ w i := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun (e1.trans e2.symm) i)
    choose w' hw' using hdvd
    have hww : w = (k : ℤ) • w' := funext fun i => by rw [Pi.smul_apply, smul_eq_mul, hw' i]
    refine ⟨bas w' u, ?_⟩
    calc x = bas w u := by rw [hw, Pi.single_eq_same]
      _ = ((k : ℤ) • bas w') u := by rw [hww, map_zsmul]
      _ = k • bas w' u := by rw [Pi.smul_apply, natCast_zsmul]
  · rintro ⟨y, rfl⟩
    rw [hsm, htor]
  · obtain ⟨a, ha, -⟩ := hπ (Pi.mulSingle u y)
    have hak : a ^ k = 1 := hone _ fun v => by
      rw [map_pow, ha]
      by_cases hv : v = u
      · subst hv; rw [Pi.mulSingle_eq_same, hy]
      · rw [Pi.mulSingle_eq_of_ne hv, one_pow]
    obtain ⟨c, hc, -⟩ := hb a hak
    refine ⟨bas (fun i => ((c i).val : ℤ)) u, ?_⟩
    have hprod : ∏ i, P i ^ ((c i).val : ℤ) = a := by
      rw [← hc, List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => zpow_natCast _ _
    rw [← hcomp, hprod, ha, Pi.mulSingle_eq_same]

theorem level_on_factor_of_eighth_power : ∀ (h g : ℕ) (J : Type) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s) (A : Over S) [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (t.A ⟶ A)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)), 0 < k → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left) → (∀ x, lev x ^ k = 1) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ S), (∀ x, (toUnit (Over.mk p) ≫ lev x = 1 ↔ ∃ y, x = k • y)) ∧ ∀ y : Over.mk p ⟶ A, y ^ k = 1 → ∃ x, toUnit _ ≫ lev x = y := by
  intro h g J bas k o _ b S s t A _ _ pr lev hk hpr huniv hlev hpt
  have hcomp : ∀ i u, t.pt i ≫ pr u = lev (bas (Pi.single i 1) u) := fun i u =>
    Over.OverMorphism.ext (hpt i u)
  have hinj : ∀ (T : Over S) (x y : T ⟶ t.A), (∀ u, x ≫ pr u = y ≫ pr u) → x = y :=
    fun T x y hxy => (huniv T (fun u => y ≫ pr u)).unique hxy (fun u => rfl)
  let cg : ∀ T : Over S, CommGroup (T ⟶ t.A) := fun T =>
    { (inferInstance : Group (T ⟶ t.A)) with
      mul_comm := fun x y => hinj T _ _ fun u => by
        have := hpr u
        rw [MonObj.mul_comp, MonObj.mul_comp, _root_.mul_comm] }
  let π : ∀ T : Over S, Fin 8 → ((T ⟶ t.A) →* (T ⟶ A)) := fun T u =>
    MonoidHom.mk' (fun x => x ≫ pr u) (fun x y => by
      have := hpr u
      exact MonObj.mul_comp x y (pr u))
  refine ⟨?_, fun K _ _ p => ?_⟩
  · letI := cg (Out.baseOver S)
    exact levelFactor_torsion (G := Out.baseOver S ⟶ t.A) (H := Out.baseOver S ⟶ A)
      (0 : Fin 8) bas t.pt (π _) lev hlev hcomp k t.torsion
  let T := Over.mk p
  letI := cg T
  let q : T ⟶ Out.baseOver S := Over.homMk p (by simp [T])
  let ρ : (Out.baseOver S ⟶ t.A) →* (T ⟶ t.A) :=
    MonoidHom.mk' (fun x => q ≫ x) (fun x y => MonObj.comp_mul q x y)
  have hq : toUnit T = q := toUnit_unique _ _
  refine levelFactor_bij (G := T ⟶ t.A) (0 : Fin 8) bas (fun i => q ≫ t.pt i) (π T)
    (fun x => toUnit T ≫ lev x) (fun x y => by rw [hlev, MonObj.comp_mul]) (fun i u => ?_) k hk
    (fun i => by
      have h1 := map_pow ρ (t.pt i) k
      rw [t.torsion, map_one] at h1
      exact h1.symm)
    (fun y => huniv T y) (fun y hy => t.bij K p y hy)
  show (q ≫ t.pt i) ≫ pr u = toUnit T ≫ lev (bas (Pi.single i 1) u)
  rw [Category.assoc, hcomp, hq]

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SurjectiveAppTopPullbackSndOfApp
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

private theorem surjective_comp_isIso_of_surjective {A B C : CommRingCat} (a : A ⟶ B) (b : B ⟶ C) [IsIso b]
    (ha : Function.Surjective a.hom) : Function.Surjective (a ≫ b).hom := by
  intro y
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso b).2 y
  obtain ⟨w, rfl⟩ := ha z
  exact ⟨w, rfl⟩

theorem surjective_appTop_pullback_snd_of_app {X S : Scheme.{0}} (f : X ⟶ S) (V : S.Opens)
    (h : ∀ U : S.Opens, Function.Surjective (f.app U).hom) :
    Function.Surjective (pullback.snd f V.ι).appTop.hom := by
  have hr : Function.Surjective (f ∣_ V).appTop.hom := by
    rw [morphismRestrict_appTop]
    exact @surjective_comp_isIso_of_surjective _ _ _ _ _ (Functor.map_isIso _ _) (h _)
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f V, Scheme.Hom.comp_appTop]
  exact @surjective_comp_isIso_of_surjective _ _ _ _ _
    (inferInstanceAs (IsIso ((pullbackRestrictIsoRestrict f V).hom.app ⊤))) hr

theorem exists_gen_of_local_of_section : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (σ : S ⟶ X) (N : LB X), N.IsLB →
    σ ≫ f = 𝟙 S → (∀ U : S.Opens, Function.Surjective (f.app U).hom) →
    (∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : (N.pull (f ⁻¹ᵁ U).ι).Gen, t.IsGen) →
    (∃ t : (N.pull σ).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro X S f σ N hN hσ hf hl hg
  obtain ⟨c, hc⟩ := hg
  have hp : ∀ V : S.Opens, Function.Surjective (pullback.snd f V.ι).appTop.hom :=
    fun V => surjective_appTop_pullback_snd_of_app f V hf
  have e : σ ≫ f ≫ σ = σ := by rw [← Category.assoc, hσ, Category.id_comp]
  have h0 : ∀ (U : Type) [CommGroup U] (h : (S ⟶ X) → U),
      ∏ k, h (σ ≫ (![𝟙 X, f ≫ σ] : Fin 2 → (X ⟶ X)) k) ^ (![1, -1] : Fin 2 → ℤ) k = 1 := by
    intro U _ h
    simp [Fin.prod_univ_two, e]
  have hloc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      ∃ t : LB.Gen (LB.LinComb N (fun k => (f ⁻¹ᵁ U).ι ≫ (![𝟙 X, f ≫ σ] : Fin 2 → (X ⟶ X)) k)
        (![1, -1] : Fin 2 → ℤ)), t.IsGen := by
    intro s
    obtain ⟨U, hsU, t, ht⟩ := hl s
    refine ⟨U, hsU, ?_⟩
    let c₁ := LB.pullGen N (fun _ : PUnit => σ) (fun _ => 1) c ((f ⁻¹ᵁ U).ι ≫ f)
    have hc₁ : c₁.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ c hc _
    let c₂ := LB.invGen N _ _ c₁
    have hc₂ : c₂.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen N _ _ c₁ hc₁
    let m := LB.mulGen N (fun _ : PUnit => (f ⁻¹ᵁ U).ι) (fun _ => 1) _ _ t c₂
    have hm : m.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ t c₂ ht hc₂
    obtain ⟨g, hg, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN
      (φ' := fun k => (f ⁻¹ᵁ U).ι ≫ (![𝟙 X, f ≫ σ] : Fin 2 → (X ⟶ X)) k) (ε' := (![1, -1] : Fin 2 → ℤ))
      (by intro V _ h; simp [Fintype.prod_sum_type, Fin.prod_univ_two]) m hm
    exact ⟨g, hg⟩
  obtain ⟨u, hu⟩ := exists_gen_of_local_on_base hN (K := Fin 2) ![𝟙 X, f ≫ σ] ![1, -1] f σ hσ hp h0 hloc
  let c₃ := LB.pullGen N (fun _ : PUnit => σ) (fun _ => 1) c f
  have hc₃ : c₃.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ c hc f
  let m₂ := LB.mulGen N _ _ _ _ u c₃
  have hm₂ : m₂.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ u c₃ hu hc₃
  obtain ⟨g, hg, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN (φ' := fun _ : PUnit => 𝟙 X) (ε' := fun _ => 1)
    (by intro V _ h; simp [Fintype.prod_sum_type, Fin.prod_univ_two]) m₂ hm₂
  exact BoxTheta.exists_gen_of_section N (𝟙 X) (𝟙 X) (Category.id_comp _) g hg

end GlobalTheory
end
end

