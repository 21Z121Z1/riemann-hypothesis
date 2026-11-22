import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0002
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.GlobalFields.LocalFieldAtPlace
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0448
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0455
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0441
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import GroundTheory.AutomorphicForms.HarishChandraCentre.VermaCoordEqZeroOfMemNPlusU
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0452
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0440
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0442
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0450
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupUniformizer
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

namespace GlobalTheory.CompanionTheory.KummerCup

noncomputable def muEquiv {Ω : Type} [Field Ω] {n : ℕ} [NeZero n] (ζ : Ωˣ) (hζ : IsPrimitiveRoot ζ n) :
    ZMod n ≃+ Additive (rootsOfUnity n Ω) :=
  let ζ' : rootsOfUnity n Ω := ⟨ζ, (mem_rootsOfUnity _ _).2 hζ.pow_eq_one⟩
  have h1 : ζ' ^ n = 1 := Subtype.ext hζ.pow_eq_one
  let f : ZMod n →+ Additive (rootsOfUnity n Ω) :=
    { toFun := fun m => Additive.ofMul (ζ' ^ m.val)
      map_zero' := by simp
      map_add' := fun a b => by
        rw [ZMod.val_add, ← pow_eq_pow_mod _ h1, pow_add, ofMul_mul] }
  AddEquiv.ofBijective f (by
    have hinj : Function.Injective f := by
      intro a b hab
      have h2 : ζ ^ a.val = ζ ^ b.val := by
        have := congrArg (fun w => ((Additive.toMul w : rootsOfUnity n Ω) : Ωˣ)) hab
        simpa [f, ζ'] using this
      have h3 := hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h2
      exact ZMod.val_injective n h3
    refine ⟨hinj, fun w => ?_⟩
    have hζ' : IsPrimitiveRoot (ζ : Ω) n := IsPrimitiveRoot.coe_units_iff.2 hζ
    have hw : (((Additive.toMul w : rootsOfUnity n Ω) : Ωˣ) : Ω) ^ n = 1 := by
      have := (mem_rootsOfUnity _ _).1 (Additive.toMul w).2
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    obtain ⟨i, hi, hie⟩ := hζ'.eq_pow_of_pow_eq_one hw
    refine ⟨(i : ZMod n), ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    change (((ζ' ^ ((i : ZMod n)).val : rootsOfUnity n Ω) : Ωˣ) : Ω) = _
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi, ← hie]
    simp [ζ'])

theorem muEquiv_apply {Ω : Type} [Field Ω] {n : ℕ} [NeZero n] (ζ : Ωˣ) (hζ : IsPrimitiveRoot ζ n) (m : ZMod n) :
    (((Additive.toMul (muEquiv ζ hζ m) : rootsOfUnity n Ω) : Ωˣ)) = ζ ^ m.val := by
  simp [muEquiv]

attribute [local instance 2000] Rep.hV2

theorem cochainOf_cyclesMap {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B : Rep.{0} k G} [IsDiscreteRep A] [IsDiscreteRep B] (φ : A ⟶ B) (x : cocycles A 2) (s : Fin 2 → G) :
    cochainOf B (cocycleι B 2 ((HomologicalComplex.cyclesMap (cochainsMap φ) 2).hom x)) s =
      φ.hom (cochainOf A (cocycleι A 2 x) s) := by
  have e := congrArg (fun ψ => cochainOf B (ψ.hom x)) (HomologicalComplex.cyclesMap_i (cochainsMap φ) 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
  change cochainOf B (((cochainsComplex B).iCycles 2).hom _) s = _
  rw [e, cochainOf_cochainsMap_f]
  rfl

theorem inv_class (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [ValuativeRel Ω] [TopologicalSpace Ω]
    [IsValuativeTopology Ω] [ValuativeExtension K Ω] (n : ℕ) [NeZero n]
    (ζ y : Ωˣ) (a : Kˣ) (hζ : IsPrimitiveRoot ζ n)
    (ha : ord (a : K) = 1) (hy : (y : Ω) ^ n = algebraMap K Ω a)
    (κ χ : Gal(Ω/K) → ZMod n)
    (hκ : ∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ g).val * y)
    (hadd : ∀ g h, χ (g * h) = χ g + χ h) (hcont : Continuous χ)
    (hF : ∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1)
    (x : cocycles (galRootsOfUnity.{0} K Ω n) 2)
    (hx : ∀ s : Fin 2 → Gal(Ω/K), cochainOf _ (cocycleι _ 2 x) s = muEquiv ζ hζ (κ (s 0) * χ (s 1))) :
    brauerInv K Ω ((cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom (cohomologyπ _ 2 x)) = - zmodToQZ n 1 := by
  have hJx := ConcreteCategory.congr_hom (cohomologyπ_comp_cohomologyMap (rootsOfUnityToUnits K Ω n) 2) x
  have hJx' : (cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom (cohomologyπ _ 2 x) =
      cohomologyπ _ 2 ((HomologicalComplex.cyclesMap (cochainsMap (rootsOfUnityToUnits K Ω n)) 2).hom x) := hJx
  rw [hJx']
  refine GlobalTheory.T.kummer_character_tame_formula K Ω n ζ y a hζ.pow_eq_one ha hy κ χ hκ hadd hcont hF _ fun s => ?_
  rw [cochainOf_cyclesMap, hx, rootsOfUnityToUnits_hom_apply, muEquiv_apply]

theorem generates_of_inv {n : ℕ} [NeZero n] {H : Type} [AddCommGroup H] [Module (ZMod n) H] (T : H →+ QZ)
    (hT : Function.Injective T) (w : H) (h : T w = - zmodToQZ n 1) :
    Submodule.span (ZMod n) {w} = ⊤ := by
  have hTn : ∀ x, n • T x = 0 := by
    intro x
    rw [← map_nsmul]
    have : n • x = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
    rw [this, map_zero]
  rw [Submodule.eq_top_iff']
  intro x
  obtain ⟨b, hb⟩ := exists_zmodToQZ_eq (hTn x)
  have hx : x = (-b) • w := by
    apply hT
    rw [← hb]
    have : (-b) • w = ((-b).val) • w := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_zmod_val]
    rw [this, map_nsmul, h, ← map_neg, ← map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    simp
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem mu_equivariant (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (n : ℕ) [NeZero n]
    (c : Gal(Ω/K) →* (ZMod n)ˣ) (ζ : Ωˣ) (hζ : IsPrimitiveRoot ζ n)
    (hc : ∀ g : Gal(Ω/K), g (ζ : Ω) = (ζ : Ω) ^ ((c g : (ZMod n)ˣ) : ZMod n).val)
    (g : Gal(Ω/K)) (m : ZMod n) : muEquiv ζ hζ (charRep c g m) =
      (galRootsOfUnity.{0} K Ω n).ρ g (muEquiv ζ hζ m) := by
  rw [galRootsOfUnity_ρ_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change (((Additive.toMul (muEquiv ζ hζ (charRep c g m)) : rootsOfUnity n Ω) : Ωˣ) : Ω) =
    g (((Additive.toMul (muEquiv ζ hζ m) : rootsOfUnity n Ω) : Ωˣ) : Ω)
  rw [muEquiv_apply, muEquiv_apply, charRep_apply, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    map_pow, hc, ← pow_mul, ZMod.val_mul]
  have h1 : (ζ : Ω) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  rw [← pow_eq_pow_mod _ h1]

theorem core (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [ValuativeRel Ω] [TopologicalSpace Ω]
    [IsValuativeTopology Ω] [ValuativeExtension K Ω] (n : ℕ) [NeZero n] (hn : (n : K) ≠ 0)
    (c : Gal(Ω/K) →* (ZMod n)ˣ) (ζ y : Ωˣ) (a : Kˣ) (hζ : IsPrimitiveRoot ζ n)
    (hc : ∀ g : Gal(Ω/K), g (ζ : Ω) = (ζ : Ω) ^ ((c g : (ZMod n)ˣ) : ZMod n).val)
    (ha : ord (a : K) = 1) (hy : (y : Ω) ^ n = algebraMap K Ω a)
    (κ χ : Gal(Ω/K) → ZMod n)
    (hκ : ∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ g).val * y)
    (hadd : ∀ g h, χ (g * h) = χ g + χ h)
    (hF : ∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1)
    (z : Z2 (charRep c)) (hz : ∀ g h, z.1 (g, h) = κ g * χ h) :
    Submodule.span (ZMod n) {(Submodule.Quotient.mk z : H2 (charRep c))} = ⊤ := by
  have hcont := GlobalTheory.T.unramified_character_continuous K Ω n χ hadd hF
  have he := mu_equivariant K Ω n c ζ hζ hc
  obtain ⟨e2, hex, he2⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 Gal(Ω/K) (ZMod n) (ZMod n) (charRep c)
    (galRootsOfUnity.{0} K Ω n) (muEquiv ζ hζ) he
  have hJ : Function.Injective (cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom :=
    cohomologyMap_f_injective_of_subsingleton (kummerSequence_shortExact (K := K) (L := Ω) n hn) 1
      subsingleton_cohomology_one_galUnits
  let T : H2 (charRep c) →+ QZ := ((brauerInv K Ω).comp
    (cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom.toAddMonoidHom).comp e2.toAddMonoidHom
  have hTinj : Function.Injective T :=
    (brauerInv_bijective K Ω).1.comp (hJ.comp e2.injective)
  have hT1 : T (Submodule.Quotient.mk z) = - zmodToQZ n 1 := by
    obtain ⟨x, hx⟩ := hex z
    change brauerInv K Ω ((cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom (e2 (Submodule.Quotient.mk z))) = _
    rw [he2 z x hx]
    exact inv_class K Ω n ζ y a hζ ha hy κ χ hκ hadd hcont hF x fun s => by rw [hx, hz]
  exact generates_of_inv T hTinj _ hT1

theorem core_dec (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (n : ℕ) [NeZero n] (hn : (n : K) ≠ 0)
    (D : Type) [Group D] [TopologicalSpace D] (ε : Gal(Ω/K) ≃ₜ* D)
    (c : D →* (ZMod n)ˣ) (ζ y : Ωˣ) (a : Kˣ) (hζ : IsPrimitiveRoot ζ n)
    (hc : ∀ g : Gal(Ω/K), g (ζ : Ω) = (ζ : Ω) ^ ((c (ε g) : (ZMod n)ˣ) : ZMod n).val)
    (ha : ord (a : K) = 1) (hy : (y : Ω) ^ n = algebraMap K Ω a)
    (κ χ : D → ZMod n)
    (hκ : ∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ (ε g)).val * y)
    (hadd : ∀ g h, χ (g * h) = χ g + χ h)
    (hF : ∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ (ε g) = 1)
    (z : Z2 (charRep c)) (hz : ∀ g h, z.1 (g, h) = κ g * χ h) :
    Submodule.span (ZMod n) {(Submodule.Quotient.mk z : H2 (charRep c))} = ⊤ := by
  letI := algebraicValuativeRel K Ω
  letI := algebraicTopology K Ω
  haveI := algebraicValuativeRel_valuativeExtension K Ω
  haveI := algebraicTopology_isValuativeTopology K Ω
  let c' : Gal(Ω/K) →* (ZMod n)ˣ := c.comp (ε : Gal(Ω/K) →* D)
  let T := ReciprocityTheory.Neutral.Bridge.equivH2OfIso ε (charRep c) (charRep c') (fun _ _ => rfl)
  let z' : Z2 (charRep c') := ReciprocityTheory.Gal.compatiblePairCocycles2 (charRep c) (charRep c')
    (ε : Gal(Ω/K) →* D) (ReciprocityTheory.Neutral.Bridge.continuous_coe_iso ε) LinearMap.id continuous_id (fun _ _ => rfl) z
  have hspan := core K Ω n hn c' ζ y a hζ hc ha hy (fun g => κ (ε g)) (fun g => χ (ε g)) hκ
    (fun g h => by rw [map_mul, hadd]) hF z' (fun g h => hz _ _)
  rw [Submodule.eq_top_iff']
  intro x
  have hx : T x ∈ Submodule.span (ZMod n) {(Submodule.Quotient.mk z' : H2 (charRep c'))} := by
    rw [hspan]; trivial
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hx
  have : x = b • (Submodule.Quotient.mk z : H2 (charRep c)) := by
    apply T.injective
    rw [← hb, map_smul, show T (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' from
      ReciprocityTheory.Neutral.Bridge.equivH2OfIso_mk ε _ _ _ z]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem cyc_apply (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] [CharZero Ω] (l : ℕ)
    [Fact l.Prime] (r : ℕ) (ζ : Ω) (hζ : ζ ^ (l ^ r) = 1) (σ : G F Ω) :
    σ ζ = ζ ^ ((cycMod F Ω l r σ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
  haveI : ∀ i, NeZero (l ^ i) := fun i => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  exact cyclotomicCharacter.spec (L := Ω) l (σ : Ω ≃+* Ω) ζ hζ

theorem span_class_eq_top : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) → (∀ g h, z.1 (g, h) = κ g * χ h) → Submodule.span (ZMod (l ^ r)) {(Submodule.Quotient.mk z : H2 (muLoc F l r A))} = ⊤ := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8
  have hl0 : l ^ r ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ r) := ⟨hl0⟩
  obtain ⟨ι, e, hec, hes, hl⟩ := GlobalTheory.CompanionTheory.DecGal.exists_algHom_mulEquiv_dec F Ω A v hA
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  haveI : IsSepClosure (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) :=
    ⟨inferInstance, inferInstance⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hϖ0 : (ϖ : F) ≠ 0 := by
    intro h
    have : ϖ = 0 := by exact_mod_cast h
    exact h2 (this ▸ Ideal.zero_mem _)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hl0] at h3
    exact hϖ0 ((map_eq_zero_iff _ (algebraMap F Ω).injective).1 h3.symm)
  have hιζ : IsPrimitiveRoot (ι ζ) (l ^ r) := hζ.map_of_injective ι.injective
  have hιy : ι y ≠ 0 := (map_ne_zero_iff _ ι.injective).2 hy0
  have ha0 : algebraMap F (v.adicCompletion F) (ϖ : F) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap F (v.adicCompletion F)).injective).2 hϖ0
  refine core_dec (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) (l ^ r)
    (Nat.cast_ne_zero.2 hl0) (Dec (F := F) A) { e with continuous_toFun := hec, continuous_invFun := hes }
    ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) (Units.mk0 (ι ζ) (hιζ.ne_zero hl0)) (Units.mk0 (ι y) hιy)
    (Units.mk0 _ ha0) (IsPrimitiveRoot.coe_units_iff.1 hιζ) ?_ (GlobalTheory.T.uniformizer_order_eq_one F v ϖ h1 h2) ?_ κ χ ?_ h5 ?_ z h8
  · intro g
    change g (ι ζ) = (ι ζ) ^ _
    rw [← hl, cyc_apply F Ω l r ζ hζ.pow_eq_one, map_pow]
    rfl
  · change (ι y) ^ (l ^ r) = _
    rw [← map_pow, h3, ι.commutes]
    exact IsScalarTower.algebraMap_apply F _ _ _
  · intro g
    change g (ι y) = (ι ζ) ^ _ * ι y
    rw [← hl]
    refine (congrArg ι (h4 (e g))).trans ?_
    rw [map_mul, map_pow]
    rfl
  · intro g hg
    exact h7 _ (GlobalTheory.T.decomposition_group_local_galois F Ω A v hA ι _ g (e g).2 (hl g) hg)

end GlobalTheory.CompanionTheory.KummerCup
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LoweringWordsSpan
section
set_option maxSynthPendingDepth 1

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

theorem exists_exp {μ : Fin n → ℤ} {x : U n} (h : x ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n))
    (hx : x ∉ vermaIdeal (rhoVec n)) : ∃ m : Fin n × Fin n →₀ ℕ, LowExp m ∧ wt m = μ := by
  by_contra hne
  have hbot : lowSpanW μ = ⊥ := by
    refine Submodule.span_eq_bot.2 ?_
    rintro _ ⟨m, hm, hw, rfl⟩
    exact absurd ⟨m, hm, hw⟩ hne
  rw [hbot, bot_sup_eq] at h
  exact hx h

theorem lowExp_wt_zero {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) (h : wt m = 0) : m = 0 := by
  refine GlobalTheory.T.eq_zero_of_low_exponent_casimir m hm (fun i j hij => ⟨1, by simp [h]⟩) ?_
  simp [h]

theorem mem_of_adW_zero {x : U n} (h : x ∈ lowSpanW (0 : Fin n → ℤ) ⊔ vermaIdeal (rhoVec n)) :
    ∃ c : ℂ, x - c • 1 ∈ vermaIdeal (rhoVec n) := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 h
  clear h
  have : ∃ c : ℂ, y = c • 1 := by
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, hw0, rfl⟩ := hx
      exact ⟨1, by rw [lowExp_wt_zero hm hw0]; simp⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨c + d, by rw [add_smul]⟩
    | smul r x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨r * c, by rw [mul_smul]⟩
  obtain ⟨c, rfl⟩ := this
  exact ⟨c, by simpa using hw⟩

theorem mem_Jp_of_adW {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (ht0 : t ≠ 0)
    (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0) :
    ∀ (N : ℕ) (μ : Fin n → ℤ) (x : U n), -ht μ < N → IsAdW μ x → φ x t = 0 → x ∈ Jp n := by
  intro N
  induction N with
  | zero =>
    intro μ x hN hx h0
    by_contra hJ
    obtain ⟨m, hm, rfl⟩ := exists_exp (GlobalTheory.T.weight_vector_mem_low_span_sup_verma μ x hx) fun h => hJ (vermaIdeal_le_Jp h)
    have := ht_wt_nonpos hm
    push_cast at hN
    omega
  | succ N ih =>
    intro μ x hN hx h0
    by_contra hJ
    obtain ⟨m, hm, rfl⟩ := exists_exp (GlobalTheory.T.weight_vector_mem_low_span_sup_verma μ x hx) fun h => hJ (vermaIdeal_le_Jp h)
    have hup : ∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n := by
      intro a ha
      refine ih _ _ ?_ (hx.e_mul a) (by simp [h0])
      rw [ht_add_rootAt, ht_rootAt]
      have h1 : (a.1 : ℕ) < a.2 := ha
      push_cast at hN
      omega
    have hm0 : m = 0 := GlobalTheory.T.eq_zero_of_low_exponent_casimir m hm
      (fun i j hij => GlobalTheory.T.nat_of_simple_lowering_nilpotent (wt m) x i j hx hup hJ hij (GlobalTheory.T.simple_lowering_pow_mem_ideal i j x hij))
      (GlobalTheory.T.casimir_eq_of_singular_weight_vector (wt m) x hx hup hJ)
    subst hm0
    have hw0 : wt (0 : Fin n × Fin n →₀ ℕ) = 0 := by ext k; simp [wt]
    rw [hw0] at hx
    obtain ⟨c, hc⟩ := mem_of_adW_zero (GlobalTheory.T.weight_vector_mem_low_span_sup_verma 0 x hx)
    have h1 := act_eq_zero_of_mem φ t hd hu hc
    rw [map_sub, LinearMap.sub_apply, h0, zero_sub, map_smul, map_one] at h1
    have hc0 : c = 0 := by
      by_contra hne
      simp [hne, ht0] at h1
    rw [hc0, zero_smul, sub_zero] at hc
    exact hJ (vermaIdeal_le_Jp hc)

theorem word_mem_lowSpan {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, p.2 < p.1) :
    word l ∈ lowSpan n := by
  refine (Submodule.span_le.2 ?_) (word_mem_canonSpan closed_lower l hl)
  rintro _ ⟨m, hm, -, -, rfl⟩
  exact Submodule.subset_span ⟨m, hm, rfl⟩

theorem rho_cast (a : Fin n) : ((rhoV n a : ℝ) : ℂ) = rhoVec n a := by
  simp [rhoV, rhoVec]

theorem act_eq_zero_of_sqSpan {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    {F : Fin n → Fin n → Module.End ℂ Z} (φ : U n →ₐ[ℂ] Module.End ℂ Z)
    (hφ : ∀ i j, φ (e (i, j)) = F i j) (z : Z)
    (hz : ∀ i j : Fin n, (j : ℕ) = i + 1 → ((F j i) ^ 2) z = 0) {x : U n}
    (hx : x ∈ sqSpan n) : φ x z = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, i, j, hij, rfl⟩ := hx
    simp only [map_mul, map_pow, hφ, Module.End.mul_apply]
    rw [hz i j hij, map_zero]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => simp [hx]

theorem pres_rho : ∀ {n : ℕ} {A Z : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup Z] [Module ℂ Z]
    (G : Fin n → Fin n → Module.End ℂ A) (F : Fin n → Fin n → Module.End ℂ Z),
    Formalism.REAL.GlRel G → Formalism.REAL.GlRel F → ∀ t : A, t ≠ 0 →
    (∀ a, G a a t = ((rhoV n a : ℝ) : ℂ) • t) → (∀ a b, a < b → G a b t = 0) →
    ∀ z : Z, (∀ i j : Fin n, (j : ℕ) = i + 1 → ((F j i) ^ 2) z = 0) →
    ∀ (s : Finset (List (Fin n × Fin n))) (coef : List (Fin n × Fin n) → ℂ), (∀ l ∈ s, ∀ p ∈ l, p.2 < p.1) →
    ∑ l ∈ s, coef l • (l.map fun p => G p.1 p.2).prod t = 0 →
    ∑ l ∈ s, coef l • (l.map fun p => F p.1 p.2).prod z = 0 := by
  intro n A Z _ _ _ _ G F hG hF t ht0 hd hu z hz s coef hs hsum
  obtain ⟨φ, hφ⟩ := exists_act G hG
  obtain ⟨ψ, hψ⟩ := exists_act F hF
  have hd' : ∀ k, φ (e (k, k)) t = rhoVec n k • t := fun k => by
    rw [hφ, hd, rho_cast]
  have hu' : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0 := fun a ha => by
    rw [show e a = e (a.1, a.2) from rfl, hφ]; exact hu _ _ ha
  set Y : U n := ∑ l ∈ s, coef l • word l with hY
  have hYlow : Y ∈ lowSpan n :=
    Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (word_mem_lowSpan (hs l hl))
  have hYt : φ Y t = 0 := by
    rw [hY, map_sum, LinearMap.sum_apply, ← hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, LinearMap.smul_apply, act_word φ hφ]
  have hYJ : Y ∈ Jp n := by
    refine (Submodule.span_le.2 ?_) (GlobalTheory.T.annihilator_spanned_by_weight_vectors φ t hd' Y hYt)
    rintro y ⟨μ, hy, h0⟩
    exact mem_Jp_of_adW φ t ht0 hd' hu' (-ht μ + 1).toNat μ y (by omega) hy h0
  have hYs := GlobalTheory.T.low_span_inf_ideal_le_square_span Y hYlow hYJ
  have h := act_eq_zero_of_sqSpan ψ hψ z hz hYs
  rw [hY, map_sum, LinearMap.sum_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, LinearMap.smul_apply, act_word ψ hψ]

end GlobalTheory.CompanionTheory.PresRho
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRatCentTwConj
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (quotIntegral IsQuotNormaliser twConj twConj_mul_left mem_twCent)

namespace GlobalTheory.CompanionTheory.OrbInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thetaA_ratGL (g : GL (Fin n) E) : thetaA E n (ratGL E n g) = ratGL E n (thetaE E n g) := by
  have h : ∀ g : GL (Fin n) E, (ratGL E n g).val = g.val.map (algebraMap E (Ad E)) := fun _ => rfl
  apply Units.ext
  rw [thetaR_val, ← map_inv, h, h, thetaR_val]
  ext i j
  exact conjAd_algebraMap _

theorem twConj_ratGL (g d : GL (Fin n) E) (x : GA E n) :
    twConj (thetaA E n) x (ratGL E n (twConj (thetaE E n) g d)) =
      twConj (thetaA E n) (ratGL E n g * x) (ratGL E n d) := by
  simp only [twConj, map_mul, map_inv, thetaA_ratGL]
  group

theorem mem_ratCent_twConj (g d : GL (Fin n) E) (x : GA E n) :
    x ∈ ratCent (twConj (thetaE E n) g d) ↔ ratGL E n g * x * (ratGL E n g)⁻¹ ∈ ratCent d := by
  simp only [ratCent, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' := (mem_twCent _ _ _).1 hc
    simp only [twConj] at hc'
    refine ⟨g * c * g⁻¹, (mem_twCent _ _ _).2 ?_, by simp only [map_mul, map_inv]⟩
    simp only [map_mul, map_inv]
    calc (g * c * g⁻¹)⁻¹ * d * (thetaE E n g * thetaE E n c * (thetaE E n g)⁻¹)
        = g * (c⁻¹ * (g⁻¹ * d * thetaE E n g) * thetaE E n c) * (thetaE E n g)⁻¹ := by group
      _ = g * (g⁻¹ * d * thetaE E n g) * (thetaE E n g)⁻¹ := by rw [hc']
      _ = d := by group
  · rintro ⟨c, hc, h⟩
    have hc' := (mem_twCent _ _ _).1 hc
    refine ⟨g⁻¹ * c * g, (mem_twCent _ _ _).2 ?_, ?_⟩
    · simp only [twConj, map_mul, map_inv]
      calc (g⁻¹ * c * g)⁻¹ * (g⁻¹ * d * thetaE E n g) *
            ((thetaE E n g)⁻¹ * thetaE E n c * thetaE E n g)
          = g⁻¹ * (c⁻¹ * d * thetaE E n c) * thetaE E n g := by group
        _ = g⁻¹ * d * thetaE E n g := by rw [hc']
    · simp only [map_mul, map_inv, h]
      group

theorem twConj_ratCent (d : GL (Fin n) E) {h : GA E n} (hh : h ∈ ratCent d) (x : GA E n) :
    twConj (thetaA E n) (h * x) (ratGL E n d) = twConj (thetaA E n) x (ratGL E n d) := by
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hh
  have hc' := (mem_twCent _ _ _).1 hc
  refine twConj_mul_left _ _ ((mem_twCent _ _ _).2 ?_) x
  rw [thetaA_ratGL, ← map_inv, ← map_mul, ← map_mul, hc']

theorem countable_ratCent [Countable (GL (Fin n) E)] (d : GL (Fin n) E) :
    (ratCent d : Set (GA E n)).Countable :=
  (Set.countable_range (ratGL E n)).mono (by
    rintro _ ⟨c, -, rfl⟩
    exact ⟨c, rfl⟩)

theorem orbInvOf : OrbInvOf := by
  intro hQ hT E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ φ d₁ g₁ d₂ g₂ hc
  obtain ⟨⟨lc₁, sc₁, t₁⟩, -, -, cn₁, -, -⟩ := hT E a
  obtain ⟨⟨lc₂, sc₂, t₂⟩, -, -, cn₂, -, -⟩ := hT E b
  have hcnt : (((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b)) :
      Set (GA E a × GA E b)).Countable := by
    rw [Subgroup.coe_prod]
    exact (countable_ratCent d₁).prod (countable_ratCent d₂)
  have : Countable ((ratCent d₁).prod (ratCent d₂) : Subgroup (GA E a × GA E b)) := hcnt.to_subtype
  set F : GA E a × GA E b → ℂ := fun x =>
    φ (twConj (thetaA E a) x.1 (ratGL E a d₁), twConj (thetaA E b) x.2 (ratGL E b d₂)) with hF
  have key := hQ (GA E a × GA E b) (μ₁.prod μ₂) ((ratCent d₁).prod (ratCent d₂))
    ((ratCent (twConj (thetaE E a) g₁ d₁)).prod (ratCent (twConj (thetaE E b) g₂ d₂))) F
    (ratGL E a g₁, ratGL E b g₂) hc.measurable
    (fun h hh x => by
      simp only [hF, Prod.fst_mul, Prod.snd_mul]
      rw [twConj_ratCent d₁ hh.1, twConj_ratCent d₂ hh.2])
    (fun x => by
      simp only [Subgroup.mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv,
        mem_ratCent_twConj])
  simp only [hF, Prod.fst_mul, Prod.snd_mul] at key
  simp only [orbTerm2, twConj_ratGL]
  exact key

end GlobalTheory.CompanionTheory.OrbInv

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicUnipotentLeParabolicStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_unipotent_le_parabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), MirUin k (m + j) ≤ MirabolicParabolic k m j := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.mirUin_le_HGP | exact GlobalTheory.CompanionTheory.LeibPhi.mirUin_le_HGP | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.mirUin_le_HGP <;> assumption)
end

