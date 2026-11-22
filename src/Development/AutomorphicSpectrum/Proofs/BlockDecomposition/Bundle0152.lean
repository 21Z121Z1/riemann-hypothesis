import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0142
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivCyclotomicCharacter
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

theorem apply_eq_pow_cycMod_val {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω) {ζ : Ω} (hζ : ζ ^ (l ^ r) = 1) :
    σ ζ = ζ ^ ((cycMod F Ω l r σ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have key := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G F Ω) Ω σ) ζ hζ
  simpa [cycMod, cycZ] using key

theorem cycMod_intrinsic : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω), cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ l _ r σ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  have h1 := apply_eq_pow_cycMod_val (F := F) (Ω := Ω) l r σ hζ.pow_eq_one
  have h2 := apply_eq_pow_cycMod_val (F := F') (Ω := Ω') l r (Φ σ) (ζ := E ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hζ' : IsPrimitiveRoot (E ζ) (l ^ r) := hζ.map_of_injective E.injective
  rw [hΦ, h1, map_pow] at h2
  have hv := hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2
  apply Units.ext
  exact ZMod.val_injective _ hv.symm

end GlobalTheory.CompanionTheory.PTIso
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsDecomposition
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

private theorem valuation_lt_one_iff_mem_and_inv_not_mem {K : Type*} [Field K] (A : ValuationSubring K) (y : K) :
    A.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ A := by
  by_cases hy : y = 0
  · subst hy
    simp
  · have hp : 0 < A.valuation y := (Valuation.pos_iff _).2 hy
    rw [← A.valuation_le_one_iff, Valuation.map_inv, inv_le_one₀ hp, not_le]
    simp [hy]

theorem isPlaceOver_transfer_fieldIso :
    ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE eO eV hO hv A A' hA v
  have hlt : ∀ y : Ω, A'.valuation (E y) < 1 ↔ A.valuation y < 1 := by
    intro y
    rw [valuation_lt_one_iff_mem_and_inv_not_mem, valuation_lt_one_iff_mem_and_inv_not_mem, ← map_inv₀, hA, map_eq_zero_iff E E.injective]
  have hx : ∀ x : 𝓞 F, (A'.valuation (algebraMap F' Ω' ((eO x : 𝓞 F') : F')) < 1 ↔ eO x ∈ (eV v).asIdeal) ↔
      (A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ v.asIdeal) := by
    intro x
    rw [hO x, ← hE, hlt, ← hv]
  unfold Formalism.ConjugateSelfDual.IsPlaceOver
  constructor
  · intro h x'
    obtain ⟨x, rfl⟩ := eO.surjective x'
    exact (hx x).2 (h x)
  · intro h x
    exact (hx x).1 (h (eO x))

end GlobalTheory.CompanionTheory.PTIso
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsInertia
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

noncomputable section

namespace GlobalTheory.CompanionTheory.PTIso.InvTransport

theorem exists_invFam : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), (∀ σ : G F Ω, cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ) → ∀ inv : InvFam F Ω l r, ∃ inv' : InvFam F' Ω' l r, ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → (Function.Bijective (inv A) → Function.Bijective (inv' A')) ∧ (∀ (z : Z2 (muLoc F l r A)) (z' : Z2 (muLoc F' l r A')), (∀ (g h : Dec (F := F) A) (g' h' : Dec (F := F') A'), (g' : G F' Ω') = Φ g → (h' : G F' Ω') = Φ h → z'.1 (g', h') = z.1 (g, h)) → inv' A' (Submodule.Quotient.mk z') = inv A (Submodule.Quotient.mk z)) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ hDec l _ r hcyc inv
  have hcm : ∀ (A' : ValuationSubring Ω') (x : Ω), E x ∈ A' ↔ x ∈ A'.comap E.toRingHom :=
    fun A' x => Iff.rfl
  let eD : ∀ A' : ValuationSubring Ω',
      Dec (F := F) (A'.comap E.toRingHom) ≃ₜ* Dec (F := F') A' :=
    fun A' => subgroupIso Φ _ _ (hDec _ A' (hcm A'))
  have hc : ∀ (A' : ValuationSubring Ω') (h : Dec (F := F) (A'.comap E.toRingHom))
      (m : ZMod (l ^ r)),
      (muLoc F' l r A') (eD A' h) m = (muLoc F l r (A'.comap E.toRingHom)) h m := by
    intro A' h m
    have h1 : cycMod F' Ω' l r (Φ h.1) = cycMod F Ω l r h.1 := hcyc h.1
    show charRep ((cycMod F' Ω' l r).comp (Dec (F := F') A').subtype) (eD A' h) m =
      charRep ((cycMod F Ω l r).comp (Dec (F := F) (A'.comap E.toRingHom)).subtype) h m
    have h2 : ((cycMod F' Ω' l r).comp (Dec (F := F') A').subtype) (eD A' h) =
        ((cycMod F Ω l r).comp (Dec (F := F) (A'.comap E.toRingHom)).subtype) h := h1
    rw [charRep_apply, charRep_apply, h2]
  refine ⟨fun A' => inv (A'.comap E.toRingHom) ∘ₗ
    (ReciprocityTheory.Neutral.Bridge.equivH2OfIso (eD A') (muLoc F' l r A')
      (muLoc F l r (A'.comap E.toRingHom)) (hc A')).toLinearMap, ?_⟩
  intro A A' hA
  obtain rfl : A = A'.comap E.toRingHom := by
    ext x
    exact (hA x).symm.trans (hcm A' x)
  refine ⟨fun hb => hb.comp (LinearEquiv.bijective _), fun z z' hz => ?_⟩
  show inv (A'.comap E.toRingHom) (ReciprocityTheory.Neutral.Bridge.equivH2OfIso (eD A') (muLoc F' l r A')
      (muLoc F l r (A'.comap E.toRingHom)) (hc A') (Submodule.Quotient.mk z')) = _
  rw [ReciprocityTheory.Neutral.Bridge.equivH2OfIso_mk]
  congr 2
  apply Subtype.ext
  funext p
  exact hz p.1 p.2 (eD A' p.1) (eD A' p.2) rfl rfl

end GlobalTheory.CompanionTheory.PTIso.InvTransport
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivTransportsResidue
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

noncomputable section

namespace GlobalTheory.CompanionTheory.PTIso.Norm

theorem isNormalised_transfer : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ^ 2 ↔ eO x ∈ (eV v).asIdeal ^ 2) → (∀ v : HeightOneSpectrum (𝓞 F), normV (eV v) = normV v) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), (∀ σ : G F Ω, cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → (∀ σ : G F Ω, (σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') ∧ (σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') ∧ ∀ q : ℕ, IsFrob (F := F) A q σ ↔ IsFrob (F := F') A' q (Φ σ)) → ∀ (ζ : Ω) (v : HeightOneSpectrum (𝓞 F)) (iA : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)) (iA' : H2 (muLoc F' l r A') →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), (∀ (z : Z2 (muLoc F l r A)) (z' : Z2 (muLoc F' l r A')), (∀ (g h : Dec (F := F) A) (g' h' : Dec (F := F') A'), (g' : G F' Ω') = Φ g → (h' : G F' Ω') = Φ h → z'.1 (g', h') = z.1 (g, h)) → iA' (Submodule.Quotient.mk z') = iA (Submodule.Quotient.mk z)) → IsNormalised ζ A v iA → IsNormalised (E ζ) A' (eV v) iA' := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ eO eV heO hI hI2 hN l _ r hc A A' hA hD ζ v iA iA'
    hrel hn ϖ' y' κ' χ' z' h1 h2 h3 h4 h5 h6 h7 h8
  let eD : Dec (F := F) A ≃ₜ* Dec (F := F') A' :=
    subgroupIso Φ (Dec (F := F) A) (Dec (F := F') A') (fun a => (hD a).1)
  have hcoe : ∀ g : Dec (F := F) A, ((eD g : Dec (F := F') A') : G F' Ω') = Φ g := fun _ => rfl
  let zz : Z2 (muLoc F l r A) :=
    compatiblePairCocycles2 (muLoc F' l r A') (muLoc F l r A) (eD : Dec (F := F) A →* Dec (F := F') A')
      eD.continuous LinearMap.id continuous_id
      (fun g m => by
        show ((cycMod F' Ω' l r (Φ g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * m =
          ((cycMod F Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * m
        rw [hc]) z'
  have hEy : E (E.symm y') = y' := E.apply_symm_apply y'
  have hϖ : eO (eO.symm ϖ') = ϖ' := eO.apply_symm_apply ϖ'
  have key : iA (Submodule.Quotient.mk zz) = 1 := by
    refine hn (eO.symm ϖ') (E.symm y') (fun g => κ' (eD g)) (fun g => χ' (eD g)) zz
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hI, hϖ]; exact h1
    · rw [hI2, hϖ]; exact h2
    · apply E.injective
      rw [map_pow, hEy, h3, hE, ← heO, hϖ]
    · intro g
      apply E.injective
      have h := h4 (eD g)
      rw [← hΦ, hEy, ← hcoe, h, map_mul, map_pow, hEy]
    · intro g h
      show χ' (eD (g * h)) = χ' (eD g) + χ' (eD h)
      rw [map_mul, h5]
    · intro g hg
      exact h6 (eD g) ((hD (g : G F Ω)).2.1.1 hg)
    · intro g hg
      refine h7 (eD g) ?_
      rw [hN]
      exact ((hD (g : G F Ω)).2.2 _).1 hg
    · intro g h
      exact h8 (eD g) (eD h)
  rw [hrel zz z' ?_]
  · exact key
  · intro g h g' h' hg hh
    have e1 : g' = eD g := Subtype.ext hg
    have e2 : h' = eD h := Subtype.ext hh
    subst e1 e2
    rfl

end GlobalTheory.CompanionTheory.PTIso.Norm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingIsomorphismTransportsPlaces
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso.Places

variable {R S : Type} [CommRing R] [CommRing S]

theorem mem_iff_apply_mem_map (f : R ≃+* S) (I : Ideal R) (x : R) :
    x ∈ I ↔ f x ∈ I.map f := by
  rw [Ideal.mem_map_of_equiv]
  constructor
  · exact fun h => ⟨x, h, rfl⟩
  · rintro ⟨y, hy, e⟩
    rwa [← f.injective e]

variable [IsDedekindDomain R] [IsDedekindDomain S]

noncomputable def placeMap (f : R ≃+* S) (v : HeightOneSpectrum R) : HeightOneSpectrum S where
  asIdeal := v.asIdeal.map f
  isPrime := by
    haveI := v.isPrime
    exact Ideal.map_isPrime_of_equiv f
  ne_bot := by
    intro h
    apply v.ne_bot
    exact (Ideal.map_eq_bot_iff_of_injective f.injective).1 h

theorem placeMap_asIdeal (f : R ≃+* S) (v : HeightOneSpectrum R) :
    (placeMap f v).asIdeal = v.asIdeal.map f := rfl

theorem placeMap_symm_placeMap (f : R ≃+* S) (v : HeightOneSpectrum R) :
    placeMap f.symm (placeMap f v) = v := by
  apply HeightOneSpectrum.ext
  rw [placeMap_asIdeal, placeMap_asIdeal, Ideal.map_symm]
  ext x
  rw [Ideal.mem_comap]
  exact (mem_iff_apply_mem_map f _ x).symm

noncomputable def placeEquiv (f : R ≃+* S) : HeightOneSpectrum R ≃ HeightOneSpectrum S where
  toFun := placeMap f
  invFun := placeMap f.symm
  left_inv := placeMap_symm_placeMap f
  right_inv := placeMap_symm_placeMap f.symm

theorem exists_places_of_ringEquiv : ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] (e : F ≃+* F'), ∃ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ^ 2 ↔ eO x ∈ (eV v).asIdeal ^ 2) ∧ ∀ v : HeightOneSpectrum (𝓞 F), normV (eV v) = normV v := by
  intro F F' _ _ _ _ e
  refine ⟨RingOfIntegers.mapRingEquiv e, placeEquiv (RingOfIntegers.mapRingEquiv e), ?_, ?_, ?_, ?_⟩
  · intro x
    rw [RingOfIntegers.mapRingEquiv_apply]
  · intro v x
    exact mem_iff_apply_mem_map _ _ x
  · intro v x
    change x ∈ v.asIdeal ^ 2 ↔ _ ∈ (v.asIdeal.map (RingOfIntegers.mapRingEquiv e)) ^ 2
    rw [← Ideal.map_pow]
    exact mem_iff_apply_mem_map _ _ x
  · intro v
    exact (Nat.card_congr (Ideal.quotientEquiv v.asIdeal _ (RingOfIntegers.mapRingEquiv e) rfl).toEquiv).symm

end GlobalTheory.CompanionTheory.PTIso.Places
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCoboundaryDegreeZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem Sh_dn_zero {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (v : Cn (box F) 0) :
    Sh F 0 (dn (box F) 0 v) = prA F (dl 0) (S0 F 0 v) - prA F (dl 1) (S0 F 0 v) := by
  have e0 : bv F ((sI (0 : Fin 1)).comp (dl 0)) ((Fin.predAboveOrderHom (0 : Fin 1)).comp (dl 0)) v =
      bv F ((dl (0 : Fin 2)).comp (cst 0 0)) OrderHom.id v :=
    bv_congr (fun i ↦ by
      fin_cases i
      rfl) (fun i ↦ Subsingleton.elim (α := Fin 1) _ _) v
  have e1 : bv F ((sI (0 : Fin 1)).comp (dl 1)) ((Fin.predAboveOrderHom (0 : Fin 1)).comp (dl 1)) v =
      bv F ((dl (1 : Fin 2)).comp (cst 0 0)) OrderHom.id v :=
    bv_congr (fun i ↦ by
      fin_cases i
      rfl) (fun i ↦ Subsingleton.elim (α := Fin 1) _ _) v
  have hS : Sh F 0 = (bv F (sI (0 : Fin 1)) (Fin.predAboveOrderHom (0 : Fin 1))).toLinearMap :=
    (Fin.sum_univ_one (M := Cn (box F) 1 →ₗ[R] Bi F 1 0)
      fun i : Fin 1 ↦ ((-1 : R) ^ (i : ℕ)) • (bv F (sI i) (Fin.predAboveOrderHom i)).toLinearMap).trans (by simp)
  have hd : dn (box F) 0 v = pr (box F) (dl 0) v - pr (box F) (dl 1) v := by
    rw [dn_eq]
    refine (Fin.sum_univ_two (M := Cn (box F) 1)
      fun i : Fin 2 ↦ ((-1 : R) ^ (i : ℕ)) • pr (box F) (dl i) v).trans ?_
    simp [sub_eq_add_neg]
  simp only [S0, prA_bv]
  rw [← e0, ← e1, hS, hd, AlgHom.toLinearMap_apply, map_sub, bv_pr, bv_pr]

end GlobalTheory.CompanionTheory.HopfC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCoboundaryFormula
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.Prism

theorem prism_sum {R G : Type} [CommRing R] [AddCommGroup G] [Module R G] (N : ℕ) (a b : ℕ → ℕ → G)
    (h1 : ∀ k j, k < N → j ≤ k → a (k + 1) j = b k j)
    (h2 : ∀ k j, k < N → k < j → j < N + 1 → a k (j + 1) = b k j)
    (h3 : ∀ k, k < N → a k (k + 1) = a (k + 1) (k + 1)) :
    ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 2), ((-1 : R) ^ (i + j)) • a i j =
      a 0 0 - a N (N + 1) - ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (N + 1), ((-1 : R) ^ (k + j)) • b k j := by
  have row : ∀ i, i ≤ N → ∑ j ∈ Finset.range (N + 2), ((-1 : R) ^ (i + j)) • a i j =
      ∑ j ∈ Finset.range i, ((-1 : R) ^ (i + j)) • a i j + (a i i - a i (i + 1)) +
        ∑ j ∈ Finset.Ico (i + 1) (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) := by
    intro i hi
    have e1 := Finset.sum_range_add_sum_Ico (fun j ↦ ((-1 : R) ^ (i + j)) • a i j) (show i ≤ N + 2 by omega)
    have e2 : ∑ j ∈ Finset.Ico i (N + 2), ((-1 : R) ^ (i + j)) • a i j =
        ((-1 : R) ^ (i + i)) • a i i + ∑ j ∈ Finset.Ico i (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_Ico_add' (fun j ↦ ((-1 : R) ^ (i + j)) • a i j) i (N + 1) 1]
    have e3 : ∑ j ∈ Finset.Ico i (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) =
        ((-1 : R) ^ (i + (i + 1))) • a i (i + 1) +
          ∑ j ∈ Finset.Ico (i + 1) (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) :=
      Finset.sum_eq_sum_Ico_succ_bot (by omega) _
    have s1 : ((-1 : R) ^ (i + i)) = 1 := Even.neg_one_pow ⟨i, rfl⟩
    have s2 : ((-1 : R) ^ (i + (i + 1))) = -1 := by rw [← add_assoc, pow_succ, s1]; simp
    rw [← e1, e2, e3, s1, s2, one_smul, neg_smul, one_smul]
    abel
  rw [Finset.sum_congr rfl (fun i hi ↦ row i (by have := Finset.mem_range.1 hi; omega))]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have tL : ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range i, ((-1 : R) ^ (i + j)) • a i j =
      - ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), ((-1 : R) ^ (k + j)) • b k j := by
    rw [Finset.sum_range_succ', Finset.range_zero, Finset.sum_empty, add_zero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [h1 k j (Finset.mem_range.1 hk) (by have := Finset.mem_range.1 hj; omega), ← neg_smul]
    congr 1
    ring
  have tR : ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.Ico (i + 1) (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) =
      - ∑ k ∈ Finset.range N, ∑ j ∈ Finset.Ico (k + 1) (N + 1), ((-1 : R) ^ (k + j)) • b k j := by
    rw [Finset.sum_range_succ, Finset.Ico_self, Finset.sum_empty, add_zero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have := Finset.mem_Ico.1 hj
    rw [h2 k j (Finset.mem_range.1 hk) (by omega) (by omega), ← neg_smul]
    congr 1
    ring
  have tD : ∑ i ∈ Finset.range (N + 1), (a i i - a i (i + 1)) = a 0 0 - a N (N + 1) := by
    rw [Finset.sum_range_succ, Finset.sum_congr rfl (fun k hk ↦ by rw [h3 k (Finset.mem_range.1 hk)]),
      Finset.sum_range_sub' (fun i ↦ a i i)]
    abel
  have tS : ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (N + 1), ((-1 : R) ^ (k + j)) • b k j =
      ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), ((-1 : R) ^ (k + j)) • b k j +
        ∑ k ∈ Finset.range N, ∑ j ∈ Finset.Ico (k + 1) (N + 1), ((-1 : R) ^ (k + j)) • b k j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have := Finset.mem_range.1 hk
    exact (Finset.sum_range_add_sum_Ico _ (by omega)).symm
  rw [tL, tR, tD, tS]
  abel

section

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem val_sI {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 1 + 1)) :
    ((sI i t : Fin (1 + 1)) : ℕ) = if i.1 < t.1 then 1 else 0 := by
  show (((if i.castSucc < t then 1 else 0 : Fin (1 + 1))) : ℕ) = _
  by_cases h : i.1 < t.1
  · rw [if_pos (show i.castSucc < t from h), if_pos h]; rfl
  · rw [if_neg (show ¬ i.castSucc < t from h), if_neg h]; rfl

theorem val_pa {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 1 + 1)) :
    ((Fin.predAboveOrderHom i t : Fin (n + 1)) : ℕ) = if i.1 < t.1 then t.1 - 1 else t.1 := by
  show ((Fin.predAbove i t : Fin (n + 1)) : ℕ) = _
  rw [Fin.predAbove]
  by_cases h : i.1 < t.1
  · rw [dif_pos (show i.castSucc < t from h), if_pos h]; simp
  · rw [dif_neg (show ¬ i.castSucc < t from h), if_neg h]; simp

def aT {n : ℕ} (w : Cn (box F) (n + 1)) (i j : ℕ) : Bi F 1 (n + 1) :=
  if h : i < n + 2 ∧ j < n + 3 then
    bv F ((sI (⟨i, h.1⟩ : Fin (n + 1 + 1))).comp (dl (⟨j, h.2⟩ : Fin (n + 1 + 1 + 1))))
      ((Fin.predAboveOrderHom (⟨i, h.1⟩ : Fin (n + 1 + 1))).comp (dl (⟨j, h.2⟩ : Fin (n + 1 + 1 + 1)))) w
  else 0

def bT {n : ℕ} (w : Cn (box F) (n + 1)) (k j : ℕ) : Bi F 1 (n + 1) :=
  if h : k < n + 1 ∧ j < n + 2 then
    bv F (sI (⟨k, h.1⟩ : Fin (n + 1)))
      ((dl (⟨j, h.2⟩ : Fin (n + 1 + 1))).comp (Fin.predAboveOrderHom (⟨k, h.1⟩ : Fin (n + 1)))) w
  else 0

variable {F}

theorem prism_term_lower_index {n : ℕ} (w : Cn (box F) (n + 1)) (k j : ℕ) (hk : k < n + 1) (hj : j ≤ k) :
    aT F w (k + 1) j = bT F w k j := by
  rw [aT, bT, dif_pos (by omega), dif_pos (by omega)]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl]
    grind

theorem prism_term_upper_index {n : ℕ} (w : Cn (box F) (n + 1)) (k j : ℕ) (hk : k < n + 1) (hkj : k < j) (hj : j < n + 2) :
    aT F w k (j + 1) = bT F w k j := by
  rw [aT, bT, dif_pos (by omega), dif_pos (by omega)]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl]
    grind

theorem prism_term_diagonal_equality {n : ℕ} (w : Cn (box F) (n + 1)) (k : ℕ) (hk : k < n + 1) :
    aT F w k (k + 1) = aT F w (k + 1) (k + 1) := by
  rw [aT, aT, dif_pos (by omega), dif_pos (by omega)]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl]
    grind

theorem aT_first {n : ℕ} (w : Cn (box F) (n + 1)) : aT F w 0 0 = prA F (dl 0) (S0 F (n + 1) w) := by
  rw [aT, dif_pos (by omega), S0, prA_bv]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl, cst_apply, Fin.val_zero]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl, Fin.val_zero, OrderHom.id_coe, id_eq]
    grind

theorem aT_last {n : ℕ} (w : Cn (box F) (n + 1)) :
    aT F w (n + 1) (n + 2) = prA F (dl 1) (S0 F (n + 1) w) := by
  rw [aT, dif_pos (by omega), S0, prA_bv]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl, cst_apply, Fin.val_zero, Fin.val_one]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl, OrderHom.id_coe, id_eq]
    grind

theorem Sh_dn_expand {n : ℕ} (w : Cn (box F) (n + 1)) :
    Sh F (n + 1) (dn (box F) (n + 1) w) =
      ∑ i ∈ Finset.range (n + 1 + 1), ∑ j ∈ Finset.range (n + 1 + 2), ((-1 : R) ^ (i + j)) • aT F w i j := by
  rw [dn_eq (n + 1)]
  simp only [Finset.sum_range, Sh, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_sum,
    map_smul, bv_pr, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [aT, dif_pos ⟨i.2, j.2⟩, pow_add, mul_comm]

theorem prB_Sh_expand {n : ℕ} (w : Cn (box F) (n + 1)) :
    ∑ j : Fin (n + 1 + 1), ((-1 : R) ^ (j : ℕ)) • prB F (dl j) (Sh F n w) =
      ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1 + 1), ((-1 : R) ^ (k + j)) • bT F w k j := by
  simp only [Finset.sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Sh, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_sum, map_smul, prB_bv]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [bT, dif_pos ⟨k.2, j.2⟩, smul_smul, pow_add, mul_comm]

theorem shuffle_coboundary_prism_identity {n : ℕ} (w : Cn (box F) (n + 1)) :
    Sh F (n + 1) (dn (box F) (n + 1) w) = prA F (dl 0) (S0 F (n + 1) w) - prA F (dl 1) (S0 F (n + 1) w) -
      ∑ j : Fin (n + 1 + 1), ((-1 : R) ^ (j : ℕ)) • prB F (dl j) (Sh F n w) := by
  rw [Sh_dn_expand, prB_Sh_expand, ← aT_first, ← aT_last]
  exact prism_sum (n + 1) (aT F w) (bT F w) (fun k j hk hj ↦ prism_term_lower_index w k j hk hj)
    (fun k j hk hkj hj ↦ prism_term_upper_index w k j hk hkj hj) (fun k hk ↦ prism_term_diagonal_equality w k hk)

end

theorem Sh_dn : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (w : Cn (box F) (n + 1)), Sh F (n + 1) (dn (box F) (n + 1) w) = prA F (dl 0) (S0 F (n + 1) w) - prA F (dl 1) (S0 F (n + 1) w) - ∑ j : Fin (n + 1 + 1), ((-1 : R) ^ (j : ℕ)) • prB F (dl j) (Sh F n w) :=
  fun _ _ w ↦ shuffle_coboundary_prism_identity w

end GlobalTheory.CompanionTheory.HopfC.Prism
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCup1DegreeZeroFormula
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem shuffle_cup1_degree_zero {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (u : Cn (box F) 1) (w : Cn (box F) 0) :
    Sh F 0 (cup1 (box F) 0 u w) = bv F OrderHom.id (cst 1 0) u * bv F (cst 0 1) OrderHom.id w := by
  have hsum : GlobalTheory.CompanionTheory.HopfC.Sh F 0 = AlgHom.toLinearMap
      (GlobalTheory.CompanionTheory.HopfC.bv F (N := 0 + 1) (p := 1) (q := 0)
        (GlobalTheory.CompanionTheory.HopfC.sI 0) (Fin.predAboveOrderHom 0)) := by
    rw [GlobalTheory.CompanionTheory.HopfC.Sh]
    first
    | (rw [Fin.sum_univ_one]; simp)
    | simp
    | (ext; simp)
  rw [hsum, AlgHom.toLinearMap_apply, GlobalTheory.CompanionTheory.HopfC.cup1_apply, map_mul,
    GlobalTheory.CompanionTheory.HopfC.bv_pr, GlobalTheory.CompanionTheory.HopfC.bv_pr]
  congr 1
  all_goals
    first
    | rfl
    | (refine GlobalTheory.CompanionTheory.HopfC.bv_congr (fun i => ?_) (fun i => ?_) _ <;>
        fin_cases i <;> first | rfl | decide | exact Subsingleton.elim (α := Fin 1) _ _)

end GlobalTheory.CompanionTheory.HopfC
end
end

