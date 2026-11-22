import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0303
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalInvariants
import ReciprocityTheory.GaloisValuations.GlobalE
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0253
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0249
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0203
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0252
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0038
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0096
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0198
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupKummer
section
set_option maxSynthPendingDepth 1

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open ValuativeRel

namespace GlobalTheory.CompanionTheory.KapChi

theorem pow_val_add {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {ζ : Ω} (hζ : ζ ^ N = 1) (a b : ZMod N) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) N, pow_add, pow_mul, hζ, one_pow, one_mul]

def addHom {D : Type} [Group D] {N : ℕ} (χ : D → ZMod N) (h : ∀ g k, χ (g * k) = χ g + χ k) :
    D →* Multiplicative (ZMod N) :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (χ g)) (fun g k => by rw [h]; rfl)

theorem chi_decomp {D : Type} [Group D] {N : ℕ} (χ : D → ZMod N) (h : ∀ g k, χ (g * k) = χ g + χ k)
    (φ t i : D) (a : ℕ) (hφ : χ φ = 1) (hi : χ i = 0) : χ (φ ^ a * t ^ N * i) = a := by
  have hp : ∀ (x : D) (n : ℕ), χ (x ^ n) = n * χ x := fun x n => by
    have := map_pow (addHom χ h) x n
    have e : Multiplicative.toAdd (addHom χ h (x ^ n)) = χ (x ^ n) := rfl
    rw [← e, this, toAdd_pow]
    simp [addHom]
  rw [h, h, hi, hp, hp, hφ]
  simp

section Dec

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} {N : ℕ}

theorem chi_unique (hA : IsPlaceOver A v) (hN : 0 < N) {χ χ' : Dec (F := F) A → ZMod N}
    (ha : ∀ g h, χ (g * h) = χ g + χ h)
    (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0)
    (hF : ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1)
    (ha' : ∀ g h, χ' (g * h) = χ' g + χ' h)
    (hI' : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ' g = 0)
    (hF' : ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ' g = 1) :
    χ = χ' := by
  obtain ⟨φ₁, hφ₁⟩ := exists_isFrob hA
  let φ : Dec (F := F) A := ⟨φ₁, hφ₁.1⟩
  funext g
  obtain ⟨a, -, t, i, hi, rfl⟩ := GlobalTheory.T.decomposition_group_frobenius_factor F Ω A v hA φ hφ₁ N hN g
  rw [chi_decomp χ ha φ t i a (hF φ hφ₁) (hI i hi), chi_decomp χ' ha' φ t i a (hF' φ hφ₁) (hI' i hi)]

theorem chi_eq_zero_of_fix (hA : IsPlaceOver A v) (hN : 0 < N) {χ : Dec (F := F) A → ZMod N}
    (ha : ∀ g h, χ (g * h) = χ g + χ h)
    (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0)
    (hF : ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1)
    {ξ : Ω} (hξ : IsPrimitiveRoot ξ (normV v ^ N - 1)) (g : Dec (F := F) A)
    (hg : (g : G F Ω) ξ = ξ) : χ g = 0 := by
  obtain ⟨φ₁, hφ₁⟩ := exists_isFrob hA
  let φ : Dec (F := F) A := ⟨φ₁, hφ₁.1⟩
  obtain ⟨a, haN, t, i, hi, rfl⟩ := GlobalTheory.T.decomposition_group_frobenius_factor F Ω A v hA φ hφ₁ N hN g
  have h0 := GlobalTheory.T.frobenius_power_fixes_root_unique F Ω A v hA φ hφ₁ N hN ξ hξ a t i haN hi hg
  rw [chi_decomp χ ha φ t i a (hF φ hφ₁) (hI i hi), h0, Nat.cast_zero]

end Dec

section Core

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem apply_eq_pow_cycMod (l : ℕ) [Fact l.Prime] (r : ℕ) (g : G F Ω) {ζ : Ω} (hζ : ζ ^ l ^ r = 1) :
    g ζ = ζ ^ ((cycMod F Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ

theorem exists_cochain_cup (l : ℕ) [Fact l.Prime] (r : ℕ) (hr : 0 < r) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (l ^ r)) {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A v) {ϖ ϖ' : 𝓞 F} (h1 : ϖ ∈ v.asIdeal) (h2 : ϖ ∉ v.asIdeal ^ 2)
    (h1' : ϖ' ∈ v.asIdeal) (h2' : ϖ' ∉ v.asIdeal ^ 2) {t : Ω}
    (ht : t ^ l ^ r * algebraMap F Ω (ϖ : F) = algebraMap F Ω (ϖ' : F))
    {κt χ : Dec (F := F) A → ZMod (l ^ r)}
    (hκ : ∀ g : Dec (F := F) A, (g : G F Ω) t = ζ ^ (κt g).val * t)
    (ha : ∀ g h, χ (g * h) = χ g + χ h)
    (hI : ∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0)
    (hF : ∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) :
    ∃ c : Dec (F := F) A → ZMod (l ^ r), Continuous c ∧ ∀ g h : Dec (F := F) A,
      ((cycMod F Ω l r (g : G F Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * c h - c (g * h) + c g =
        κt g * χ h := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hN : 0 < l ^ r := pow_pos hl r
  have : NeZero (l ^ r) := ⟨hN.ne'⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ι, hι⟩ := GlobalTheory.LocDict.exists_isLocEmb F Ω A v hA
  obtain ⟨θ, hθ, hθ', hlift⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc F Ω A v hA ι hι
  have hlift' : ∀ (σ : GlobalTheory.LocDict.GalLoc v) (x : Ω), σ (ι x) = ι ((θ.symm σ : G F Ω) x) := fun σ x => by
    have := hlift (θ.symm σ) x
    rwa [MulEquiv.apply_symm_apply] at this

  have hq : 1 < normV v := ReciprocityTheory.Gal.one_lt_normV v
  obtain ⟨n, hn⟩ : ∃ n, n = normV v ^ l ^ r - 1 := ⟨_, rfl⟩
  have hn0 : n ≠ 0 := by
    have := one_lt_pow₀ hq hN.ne'
    omega
  have : NeZero n := ⟨hn0⟩
  have : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn0⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  rw [hn] at hξ
  have hξv : IsPrimitiveRoot (ι ξ) (Nat.card 𝓀[v.adicCompletion F] ^ l ^ r - 1) := by
    rw [GlobalTheory.T.residue_field_card_eq_norm F v]
    exact hξ.map_of_injective ι.toRingHom.injective
  let ψ : GlobalTheory.LocDict.GalLoc v →* Multiplicative (ZMod (l ^ r)) :=
    (addHom χ ha).comp θ.symm.toMonoidHom
  have hfix : ∀ σ : GlobalTheory.LocDict.GalLoc v, σ (ι ξ) = ι ξ → ψ σ = 1 := fun σ hσ => by
    rw [hlift'] at hσ
    have e := chi_eq_zero_of_fix hA hN ha hI hF hξ (θ.symm σ) (ι.toRingHom.injective hσ)
    show Multiplicative.ofAdd (χ (θ.symm σ)) = 1
    rw [e]
    rfl
  have ho : IsOpen (ψ.ker : Set (GlobalTheory.LocDict.GalLoc v)) := by
    have : FiniteDimensional (v.adicCompletion F) (IntermediateField.adjoin (v.adicCompletion F) {ι ξ}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin (v.adicCompletion F) {ι ξ}).fixingSubgroup)
      (fun σ hσ => hfix σ ?_) (IntermediateField.fixingSubgroup_isOpen _)
    exact hσ ⟨ι ξ, IntermediateField.mem_adjoin_simple_self _ _⟩

  have hϖ0 : algebraMap F (v.adicCompletion F) (ϖ : F) ≠ 0 := by
    intro h
    have h0 : (ϖ : F) = 0 := (map_eq_zero _).1 h
    have h0' : ϖ = 0 := by exact_mod_cast h0
    exact h2 (h0' ▸ Ideal.zero_mem _)
  have hϖ0' : algebraMap F (v.adicCompletion F) (ϖ' : F) ≠ 0 := by
    intro h
    have h0 : (ϖ' : F) = 0 := (map_eq_zero _).1 h
    have h0' : ϖ' = 0 := by exact_mod_cast h0
    exact h2' (h0' ▸ Ideal.zero_mem _)
  let U : (v.adicCompletion F)ˣ := Units.mk0
    (algebraMap F (v.adicCompletion F) (ϖ' : F) / algebraMap F (v.adicCompletion F) (ϖ : F))
    (div_ne_zero hϖ0' hϖ0)
  have hU : (U : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (ϖ : F) =
      algebraMap F (v.adicCompletion F) (ϖ' : F) := div_mul_cancel₀ _ hϖ0
  have hord := GlobalTheory.T.uniformizer_ratio_valuation_zero F v ϖ ϖ' h1 h2 h1' h2' U hU
  have hnorm := GlobalTheory.T.norm_from_kummer_unramified_unit (K := v.adicCompletion F) (Ω := GlobalTheory.LocDict.Kbar v) (l ^ r) hN.ne' (ι ξ) hξv ψ ho hfix U hord
  have hcomm : ∀ x : F, ι (algebraMap F Ω x) =
      algebraMap (v.adicCompletion F) (GlobalTheory.LocDict.Kbar v) (algebraMap F (v.adicCompletion F) x) := fun x => by
    rw [ι.commutes, ← IsScalarTower.algebraMap_apply]
  have hT : ι t ^ l ^ r = algebraMap (v.adicCompletion F) (GlobalTheory.LocDict.Kbar v) (U : v.adicCompletion F) := by
    have e := congrArg ι ht
    rw [map_mul, map_pow, hcomm, hcomm, ← hU, map_mul] at e
    exact mul_right_cancel₀ ((map_ne_zero _).2 hϖ0) e
  have hc0 : ∀ σ : GlobalTheory.LocDict.GalLoc v, σ (ι ζ) = ι ζ ^
      ((cycMod F Ω l r (θ.symm σ : G F Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := fun σ => by
    rw [hlift', apply_eq_pow_cycMod l r _ hζ.pow_eq_one, map_pow]
  have hκ' : ∀ σ : GlobalTheory.LocDict.GalLoc v, σ (ι t) = ι ζ ^ (κt (θ.symm σ)).val * ι t := fun σ => by
    rw [hlift', hκ, map_mul, map_pow]
  obtain ⟨c, hc, hc2⟩ := GlobalTheory.T.kummer_cocycle_norm_criterion (K := v.adicCompletion F) (Ω := GlobalTheory.LocDict.Kbar v) (l ^ r) hN (ι ζ)
    (hζ.map_of_injective ι.toRingHom.injective) _ hc0 ψ ho U hnorm (ι t) (fun σ => κt (θ.symm σ)) hT hκ'
  refine ⟨fun g => c (θ g), hc.continuous.comp hθ, fun g h => ?_⟩
  have e := hc2 (θ g) (θ h)
  have hψ : Multiplicative.toAdd (ψ (θ h)) = χ h := by
    show χ (θ.symm (θ h)) = χ h
    rw [MulEquiv.symm_apply_apply]
  simp only [MulEquiv.symm_apply_apply, ← map_mul] at e
  rw [hψ] at e
  exact e

end Core

theorem cup_class_eq : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) → (∀ g h, z.1 (g, h) = κ g * χ h) → ∀ (ϖ' : 𝓞 F) (y' : Ω) (κ' χ' : Dec (F := F) A → ZMod (l ^ r)) (z' : Z2 (muLoc F l r A)), ϖ' ∈ v.asIdeal → ϖ' ∉ v.asIdeal ^ 2 → y' ^ (l ^ r) = algebraMap F Ω (ϖ' : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y' = ζ ^ (κ' g).val * y') → (∀ g h, χ' (g * h) = χ' g + χ' h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ' g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ' g = 1) → (∀ g h, z'.1 (g, h) = κ' g * χ' h) → (Submodule.Quotient.mk z : H2 (muLoc F l r A)) = Submodule.Quotient.mk z' := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ A v hA ϖ y κ χ z h1 h2 hy hκ hχa hχI hχF hz ϖ' y' κ' χ' z' h1' h2' hy'
    hκ' hχa' hχI' hχF' hz'
  have hN : 0 < l ^ r := pow_pos (Fact.out : l.Prime).pos r
  have : NeZero (l ^ r) := ⟨hN.ne'⟩
  obtain rfl : χ = χ' := chi_unique hA hN hχa hχI hχF hχa' hχI' hχF'
  have hϖ0 : algebraMap F Ω (ϖ : F) ≠ 0 := by
    intro h
    have h0 : (ϖ : F) = 0 := (map_eq_zero _).1 h
    have h0' : ϖ = 0 := by exact_mod_cast h0
    exact h2 (h0' ▸ Ideal.zero_mem _)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hy
    exact hϖ0 hy.symm
  have ht : (y' / y) ^ l ^ r * algebraMap F Ω (ϖ : F) = algebraMap F Ω (ϖ' : F) := by
    rw [div_pow, hy, hy', div_mul_cancel₀ _ hϖ0]
  have hκt : ∀ g : Dec (F := F) A, (g : G F Ω) (y' / y) = ζ ^ (κ' g - κ g).val * (y' / y) := fun g => by
    have e := pow_val_add hζ.pow_eq_one (κ' g - κ g) (κ g)
    rw [sub_add_cancel] at e
    have hgy : ζ ^ (κ g).val ≠ 0 := pow_ne_zero _ (hζ.ne_zero hN.ne')
    rw [map_div₀, hκ, hκ', e]
    field_simp
  obtain ⟨c, hc, hc2⟩ := exists_cochain_cup l r hr hζ hA h1 h2 h1' h2' ht hκt hχa hχI hχF
  refine ((Submodule.Quotient.eq _).2 ?_).symm
  refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c, hc, funext fun p => ?_⟩
  obtain ⟨g, h⟩ := p
  have e := hc2 g h
  rw [sub_mul] at e
  show _ = z'.1 (g, h) - z.1 (g, h)
  rw [hz, hz', ← e]
  rfl

end GlobalTheory.CompanionTheory.KapChi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableLocalZeroCount
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.FSCrofton.Chart

theorem measurableSet_of_isSigmaCompact {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {A : Set X} (hA : IsSigmaCompact A) :
    MeasurableSet A := by
  obtain ⟨K, hK, rfl⟩ := hA
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

variable {Y : Var ℂ} {L : LB Y.X}

noncomputable def chartVal {n : ℕ} (b : Fin n → L.Sec) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim)
    (i : L.ι) (j : Fin n) (v : ReciprocityTheory.L2DbarEstimates.V Y.dim) : ℂ :=
  secVal Y.str (RingHom.id ℂ) (b j) i (c.e.symm v)

theorem encard_eq_zeroCnt {n : ℕ} (b : Fin n → L.Sec) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim)
    (i : L.ι) (A : Set (CxPts Y.str (RingHom.id ℂ))) (hAc : A ⊆ c.e.source)
    (hAi : A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i)) (C : Fin Y.dim → Fin n → ℂ) :
    (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι),
        y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞) =
      zeroCnt Y.dim (c.e '' A) (chartVal b c i) C := by
  have hinj : Set.InjOn c.e {y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι),
        y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0} :=
    c.e.injOn.mono fun y hy => hAc hy.1
  have himg : c.e '' {y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι),
        y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') →
        ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0} =
      {z ∈ c.e '' A | ∀ k, ∑ j, C k j * chartVal b c i j z = 0} := by
    ext v
    constructor
    · rintro ⟨y, ⟨hyA, hy⟩, rfl⟩
      refine ⟨⟨y, hyA, rfl⟩, fun k => ?_⟩
      simpa only [chartVal, c.e.left_inv (hAc hyA)] using hy k i (hAi hyA)
    · rintro ⟨⟨y, hyA, rfl⟩, hy⟩
      refine ⟨y, ⟨hyA, fun k i' hi' => ?_⟩, rfl⟩
      have h0 : ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0 := by
        simpa only [chartVal, c.e.left_inv (hAc hyA)] using hy k
      have e : ∀ j, secVal Y.str (RingHom.id ℂ) (b j) i' y =
          gv Y.str (RingHom.id ℂ) L i' i y * secVal Y.str (RingHom.id ℂ) (b j) i y :=
        fun j => (secVal_mem (b j)).1 i' i y hi' (hAi hyA)
      simp only [e]
      calc ∑ j, C k j * (gv Y.str (RingHom.id ℂ) L i' i y * secVal Y.str (RingHom.id ℂ) (b j) i y)
          = gv Y.str (RingHom.id ℂ) L i' i y *
              ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [h0, mul_zero]
  rw [zeroCnt, ← himg, hinj.encard_image]

theorem fsBasis_φ_chart (hL : L.IsLB) {n : ℕ} (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤)
    (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι) (v : ReciprocityTheory.L2DbarEstimates.V Y.dim) :
    (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).φ i (c.e.symm v) =
      Real.log (∑ j, ‖chartVal b c i j v‖ ^ 2) := by
  rw [Weight.fsBasis_φ]
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rfl

theorem chernPart_eq_lintegral (hL : L.IsLB) {n : ℕ} (b : Fin n → L.Sec)
    (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι)
    (A : Set (CxPts Y.str (RingHom.id ℂ))) (hAm : MeasurableSet A) (hAc : A ⊆ c.e.source)
    (hAi : A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i)) (hBm : MeasurableSet (c.e '' A)) :
    (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernPart Y.dim 1 A =
      ∫⁻ z in c.e '' A, ENNReal.ofReal ((Y.dim.factorial : ℝ) / Real.pi ^ Y.dim *
        (ReciprocityTheory.L2DbarEstimates.cHess Y.dim
          (fun v => ((Real.log (∑ j, ‖chartVal b c i j v‖ ^ 2) : ℝ) : ℂ)) z).det.re) := by
  haveI := CxPts.secondCountableTopology_of_isProjOver (σ := RingHom.id ℂ) Y.isProjOver
  have hC := Weight.isCInf_fsBasis (p := Y.str) (σ := RingHom.id ℂ) hL b hb 1 (by simp)
  rw [Weight.chernPart_apply hC 1 c hAm hAc]
  refine setLIntegral_congr_fun hBm fun v hv => ?_
  obtain ⟨y, hy, rfl⟩ := hv
  have hys := c.e.left_inv (hAc hy)
  simp only [hys]
  rw [c.chernDens_eq hC (hAc hy) (hAi hy), AlgChart.hess]
  simp only [fsBasis_φ_chart hL b hb c i, Units.val_one, Int.cast_one, one_mul]

end GlobalTheory.CompanionTheory.FSCrofton.Chart

open GlobalTheory.CompanionTheory.FSCrofton.Chart in

theorem GlobalTheory.CompanionTheory.FSCrofton.crofton_chart : ∀ (Y : Var ℂ) (L : LB Y.X) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤) (c : AlgChart Y.str (RingHom.id ℂ) Y.dim) (i : L.ι) (j₀ : Fin n) (A : Set (CxPts Y.str (RingHom.id ℂ))), A ⊆ c.e.source → A ⊆ ptsIn Y.str (RingHom.id ℂ) (L.U i) → (∀ y ∈ A, secVal Y.str (RingHom.id ℂ) (b j₀) i y ≠ 0) → IsSigmaCompact A → Measurable (fun C : Fin Y.dim → Fin n → ℂ => (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞)) ∧ ∫⁻ C : Fin Y.dim → Fin n → ℂ, gW Y.dim (Fin n) C * (({y : CxPts Y.str (RingHom.id ℂ) | y ∈ A ∧ ∀ (k : Fin Y.dim) (i' : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i') → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i' y = 0}.encard : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal (Real.pi ^ (Y.dim * n)) * (Weight.fsBasis Y.str (RingHom.id ℂ) hL b hb 1 (by simp)).chernPart Y.dim 1 A := by
  intro Y L hL n b hb c i j₀ A hAc hAi hA0 hAs
  have hAm : MeasurableSet A := measurableSet_of_isSigmaCompact hAs
  have hBs : IsSigmaCompact (c.e '' A) :=
    hAs.image_of_continuousOn (c.e.continuousOn.mono hAc)
  have hBm : MeasurableSet (c.e '' A) := measurableSet_of_isSigmaCompact hBs
  have hcnt := encard_eq_zeroCnt b c i A hAc hAi

  set W : Y.X.Opens := L.U i ⊓ nonzeroLocus (b j₀) with hW
  set U : Set (ReciprocityTheory.L2DbarEstimates.V Y.dim) := c.e.target ∩ c.e.symm ⁻¹' ptsIn Y.str (RingHom.id ℂ) W
    with hU
  have hUo : IsOpen U := ChartGlue.isOpen_over c.e (isOpen_ptsIn W)
  have hUi : ∀ v ∈ U, c.e.symm v ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) := fun v hv =>
    (mem_ptsIn_inf.1 hv.2).1
  have hd : ∀ j, DifferentiableOn ℂ (chartVal b c i j) U := fun j =>
    (c.holo (L.U i) ((b j).f i)).mono fun v hv => ⟨hv.1, hUi v hv⟩
  have h0 : ∀ z ∈ U, chartVal b c i j₀ z ≠ 0 := fun z hz =>
    (secVal_ne_zero_iff (b j₀) (hUi z hz)).2 (mem_ptsIn_inf.1 hz.2).2
  have hBU : c.e '' A ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨c.e.map_source (hAc hy), ?_⟩
    change c.e.symm (c.e y) ∈ ptsIn Y.str (RingHom.id ℂ) W
    rw [c.e.left_inv (hAc hy)]
    exact mem_ptsIn_inf.2 ⟨hAi hy, (secVal_ne_zero_iff (b j₀) (hAi hy)).1 (hA0 y hy)⟩
  refine ⟨?_, ?_⟩
  · simp only [hcnt]
    exact GlobalTheory.T.measurable_zero_count Y.dim (Fin n) U (c.e '' A) (chartVal b c i)
      (fun j => (hd j).continuousOn) hBU hBs
  · simp only [hcnt]
    have key := GlobalTheory.T.random_section_zero_count Y.dim (Fin n) j₀ U (c.e '' A) (chartVal b c i) hUo hd h0 hBU hBs
    rw [key, Fintype.card_fin, chernPart_eq_lintegral hL b hb c i A hAm hAc hAi hBm]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulInvMemQOfRowQEq
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZPhiPhi

section Alg

variable {k : Type} [Field k]

theorem mul_inv_mem_Q_of_rowQ_eq (n : ℕ) (a b : Mir k (n + 1)) (h : rowQ k n a = rowQ k n b) :
    a * b⁻¹ ∈ Q k n := by
  show GlobalTheory.BZMir.mirabolicProjection k (n + 1) (a * b⁻¹) ∈ GlobalTheory.BZMir.Mir k n
  have hab : Matrix.vecMul (GlobalTheory.BZMir.eLast k n)
      (↑(GlobalTheory.BZMir.mirabolicProjection k (n + 1) a) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      Matrix.vecMul (GlobalTheory.BZMir.eLast k n)
      (↑(GlobalTheory.BZMir.mirabolicProjection k (n + 1) b) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    rw [GlobalTheory.BZMir.vecMul_eLast, GlobalTheory.BZMir.vecMul_eLast]
    funext j
    exact congrFun h j
  rw [GlobalTheory.BZMir.mem_Mir_iff, ← GlobalTheory.BZMir.vecMul_eLast k n
    (↑(GlobalTheory.BZMir.mirabolicProjection k (n + 1) (a * b⁻¹)) : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
    map_mul, map_inv, Units.val_mul, ← Matrix.vecMul_vecMul, hab, Matrix.vecMul_vecMul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

def rowMat (n : ℕ) (r : Fin (n + 1) → k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k :=
  (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) k).updateRow (Fin.castSucc (Fin.last n))
    (Fin.lastCases (motive := fun _ => k) 0 r)

theorem rowMat_single (n : ℕ) : rowMat n (Pi.single (Fin.last n) (1 : k)) = 1 := by
  ext i j
  rw [GlobalTheory.CompanionTheory.BZPhiPhi.rowMat, Matrix.updateRow_apply]
  split_ifs with hi
  · subst hi
    induction j using Fin.lastCases with
    | last => simp [Matrix.one_apply, Fin.castSucc_ne_last]
    | cast j =>
      by_cases hj : j = Fin.last n
      · subst hj
        simp [Matrix.one_apply]
      · simp [Matrix.one_apply, Pi.single_apply, hj, Ne.symm hj]
  · rfl

def rowEl (n : ℕ) (r : Fin (n + 1) → k) (h : (rowMat n r).det ≠ 0) : Mir k (n + 1) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (rowMat n r) h, by
    rw [mem_Mir_iff]
    show rowMat n r (Fin.last (n + 1)) = eLast k (n + 1)
    rw [rowMat, updateRow_ne (Fin.castSucc_ne_last _).symm]
    funext j
    simp [eLast, one_apply, Pi.single_apply, eq_comm]⟩

theorem rowEl_val (n : ℕ) (r : Fin (n + 1) → k) (h : (rowMat n r).det ≠ 0) :
    (((rowEl n r h : Mir k (n + 1)) : GL (Fin (n + 2)) k) : Matrix (Fin (n + 2)) (Fin (n + 2)) k) = rowMat n r := rfl

theorem rowQ_rowEl (n : ℕ) (r : Fin (n + 1) → k) (h : (rowMat n r).det ≠ 0) :
    rowQ k n (rowEl n r h) = r := by
  funext j
  show GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r (Fin.castSucc (Fin.last n)) (Fin.castSucc j) = r j
  rw [GlobalTheory.CompanionTheory.BZPhiPhi.rowMat, Matrix.updateRow_self, Fin.lastCases_castSucc]

end Alg

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_rowMat (n : ℕ) : Continuous (rowMat (k := k) n) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [GlobalTheory.CompanionTheory.BZPhiPhi.rowMat]
  by_cases hi : i = Fin.castSucc (Fin.last n)
  · subst hi
    simp only [Matrix.updateRow_self]
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_last]
      exact continuous_const
    | cast j =>
      simp only [Fin.lastCases_castSucc]
      exact continuous_apply j
  · simp only [Matrix.updateRow_ne hi]
    exact continuous_const

theorem continuous_rowEl (n : ℕ) :
    Continuous fun r : {r : Fin (n + 1) → k // (rowMat n r).det ≠ 0} => rowEl n r.1 r.2 := by
  have hM : Continuous fun r : {r : Fin (n + 1) → k // (GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r).det ≠ 0} =>
      GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r.1 :=
    (GlobalTheory.CompanionTheory.BZPhiPhi.continuous_rowMat n).comp continuous_subtype_val
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  refine ⟨hM, ?_⟩
  simp only [Function.comp_apply, Matrix.coe_units_inv]
  show Continuous fun r : {r : Fin (n + 1) → k // (GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r).det ≠ 0} =>
    (GlobalTheory.CompanionTheory.BZPhiPhi.rowMat n r.1)⁻¹
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hM.matrix_det.inv₀ fun r => r.2).smul hM.matrix_adjugate

end Top

end GlobalTheory.CompanionTheory.BZPhiPhi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialSubrepresentation
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.DegPrinSeries

theorem nontrivial_subrepresentation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → Nontrivial (Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))) := by
  intro k _ _ _ _ a b χ₁ χ₂ hχ₁ hχ₂
  have hdetChar : ∀ (m : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ →
      GlobalTheory.PRep.IsSmooth (GlobalTheory.SmGL.detRep (Fin m) χ) := by
    intro m χ hχ
    have hc : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin m) k → kˣ) := by
      rw [Units.continuous_iff]
      constructor
      · have hval : (Units.val ∘ (Matrix.GeneralLinearGroup.det : GL (Fin m) k → kˣ)) =
            fun g : GL (Fin m) k => Matrix.det (g : Matrix (Fin m) (Fin m) k) := by
          funext g
          exact Matrix.GeneralLinearGroup.val_det_apply g
        rw [hval]
        exact Units.continuous_val.matrix_det
      · have hinv : (fun g : GL (Fin m) k => ((Matrix.GeneralLinearGroup.det g)⁻¹ : kˣ).val) =
            fun g => Matrix.det ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) := by
          funext g
          rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
        rw [hinv]
        exact Units.continuous_coe_inv.matrix_det
    unfold GlobalTheory.SmGL.detRep
    rw [GlobalTheory.SmGL.isSmooth_ofChar_iff]
    unfold GlobalTheory.SmGL.IsSmoothChar at hχ ⊢
    exact hc.isOpen_preimage _ hχ
  have hsmooth := GlobalTheory.SmGL.isSmooth_comp
    (GlobalTheory.SmGL.isSmooth_extTensor (hdetChar a χ₁ hχ₁) (hdetChar b χ₂ hχ₂))
    (GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm.toMonoidHom
    (by exact (continuous_apply Bool.false).prodMk (continuous_apply Bool.true))
  have hu : ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) ≠ 0 := by
    intro h0
    have := congrArg (TensorProduct.lid ℂ ℂ) h0
    simp at this
  obtain ⟨f, hf1, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one
    (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : a + b = a + b))) _
    hsmooth ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))
  refine ⟨⟨⟨⊥, fun g ⦃v⦄ hv => ?_⟩, ⟨⊤, fun _ ⦃_⦄ _ => Submodule.mem_top⟩, fun hEq => ?_⟩⟩
  · rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  · have hsub := congrArg Subrepresentation.toSubmodule hEq
    have hf : f = 0 := (Submodule.mem_bot ℂ).1 (Submodule.eq_top_iff'.1 hsub f)
    rw [hf] at hf1
    apply hu
    rw [← hf1]
    first
    | rfl
    | simp

end GlobalTheory.CompanionTheory.DegPrinSeries
end
end

