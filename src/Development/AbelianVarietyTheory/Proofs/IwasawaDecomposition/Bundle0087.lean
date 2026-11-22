import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0083
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import ReciprocityTheory.GaloisValuations.Global
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaTameCharPrimitiveRootOfUniformizerR
section
open NumberField IsDedekindDomain

namespace GlobalTheory.TameRootSurj

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem irreducible_X_pow_sub_C {E : Type} [Field E] [NumberField E]
    (P : HeightOneSpectrum (𝓞 E)) {L : ℕ} (hL : 0 < L) {ϖ : 𝓞 E}
    (hmem : ϖ ∈ P.asIdeal) (hnot : ϖ ∉ P.asIdeal ^ 2) :
    Irreducible (X ^ L - C (ϖ : E)) := by
  have hmon : (X ^ L - C ϖ : (𝓞 E)[X]).Monic := monic_X_pow_sub_C ϖ hL.ne'
  have hdeg : (X ^ L - C ϖ : (𝓞 E)[X]).natDegree = L := natDegree_X_pow_sub_C
  have hEis : (X ^ L - C ϖ : (𝓞 E)[X]).IsEisensteinAt P.asIdeal := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmon.leadingCoeff]; exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    · intro m hm
      rw [hdeg] at hm
      rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hm.ne]
      by_cases h0 : m = 0
      · subst h0; simpa using P.asIdeal.neg_mem_iff.2 hmem
      · simp [h0]
    · rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hL.ne, if_pos rfl, zero_sub]
      rwa [Ideal.neg_mem_iff]
  have hirr : Irreducible (X ^ L - C ϖ : (𝓞 E)[X]) :=
    hEis.irreducible P.isPrime hmon.isPrimitive (by rw [hdeg]; exact hL)
  have hmap : (X ^ L - C ϖ : (𝓞 E)[X]).map (algebraMap (𝓞 E) E) = X ^ L - C (ϖ : E) := by
    simp [Polynomial.map_sub]
  rw [← hmap]; exact (hmon.irreducible_iff_irreducible_map_fraction_map (K := E)).1 hirr

theorem main : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ) (ϖ : 𝓞 E) (π : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    π ^ L = algebraMap E Ω (ϖ : E) → ∃ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, IsPrimitiveRoot (σ π / π) L := by
  intro E Ω _ _ _ _ _ P A L ϖ π hA hL h1 h2 hπ
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hL0 : L ≠ 0 := by rintro rfl; exact hL (by simp)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hL0, eq_comm, map_eq_zero] at hπ
    exact hϖ0 (by simpa using hπ)
  rcases Nat.lt_or_ge L 2 with hL2 | hL2
  · have hL1 : L = 1 := by omega
    subst hL1
    refine ⟨1, one_mem _, ?_⟩
    rw [AlgEquiv.one_apply, div_self hπ0]
    exact IsPrimitiveRoot.one
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : NeZero ((L : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hL0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω L
  have hirr := irreducible_X_pow_sub_C P (Nat.pos_of_ne_zero hL0) h1 h2
  have hmon : (X ^ L - C (ϖ : E)).Monic := monic_X_pow_sub_C _ hL0
  have hr1 : aeval π (X ^ L - C (ϖ : E)) = 0 := by simp [hπ]
  have hr2 : aeval (ζ * π) (X ^ L - C (ϖ : E)) = 0 := by simp [mul_pow, hζ.pow_eq_one, hπ]
  have hm1 := minpoly.eq_of_irreducible_of_monic hirr hr1 hmon
  have hm2 := minpoly.eq_of_irreducible_of_monic hirr hr2 hmon
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  obtain ⟨g, hg⟩ : ∃ g : Ω ≃ₐ[E] Ω, g π = ζ * π := by
    obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := E) (E := Ω)).1 (hm2.symm.trans hm1)
    exact ⟨g, hg⟩
  obtain ⟨-, hx2⟩ := GlobalTheory.InertiaMovesRoot.cong_on_adjoin hA hL2 h1 h2 hπ
  letI : TopologicalSpace (IntCl E Ω) := ⊥
  haveI : DiscreteTopology (IntCl E Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl E Ω
  let H := MulAction.stabilizer (Ω ≃ₐ[E] Ω) π
  have hH : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) :=
    H.isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral (K := E) π)
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  obtain ⟨k, hk, k', hk', hc⟩ := GlobalTheory.InertiaMovesRoot.exists_cong_of_cong_on_fixed (R := 𝓞 E) H
    (primeBelow (F := E) A) g (fun b hb => by
      refine hx2 g b ?_ (valuation_le_one_intCl A b)
      rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin E {π}),
        IntermediateField.mem_fixedField_iff]
      intro f hf
      exact congrArg Subtype.val (hb f (hf ⟨π, IntermediateField.mem_adjoin_simple_self E π⟩)))
  refine ⟨k' * g * k, GlobalTheory.InertiaMovesRoot.mem_Ine_of_cong hc, ?_⟩
  have e1 : k π = π := hk
  have e2 : k' π = π := hk'
  have e3 : (k' * g * k) π / π = k' ζ := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, e1, hg, map_mul, e2, mul_div_cancel_right₀ _ hπ0]
  rw [e3]
  exact hζ.map_of_injective k'.injective

end GlobalTheory.TameRootSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModulusBbDisjoint
section
namespace GlobalTheory.Mem

theorem exc_dvd_prod_range {g e l r : ℕ} (hg : 1 ≤ g) (h1 : 1 ≤ e) (hr : e ≤ r) (h : Formalism.CyclotomicNorms.Exc g e l) :
    l ∣ ∏ i ∈ Finset.range r, (g ^ (i + 1) - 1) := by
  have hv : padicValNat l (g ^ e - 1) ≠ 0 := by
    intro h0
    have h2 := h.2
    rw [h0, mul_zero, pow_zero] at h2
    have := Nat.one_le_pow e g hg
    omega
  have h3 : g ^ e - 1 ∣ ∏ i ∈ Finset.range r, (g ^ (i + 1) - 1) := by
    have := Finset.dvd_prod_of_mem (fun i => g ^ (i + 1) - 1) (Finset.mem_range.2 (show e - 1 < r by omega))
    rwa [Nat.sub_add_cancel h1] at this
  exact ((dvd_pow_self l hv).trans pow_padicValNat_dvd).trans h3

theorem not_exc_of_cong_sq {M l g e c k : ℕ} (hl : l.Prime) (hM : l ^ k ∣ M) (hM0 : 0 < M)
    (hg : g = 1 + 2 * M + M ^ 2 * c) (hbig : M ^ 8 ≤ g) (h1 : 1 ≤ e) (hk : 2 * e < l ^ k) :
    ¬ Formalism.CyclotomicNorms.Exc g e l := by
  rintro ⟨-, hlt⟩
  have : Fact l.Prime := ⟨hl⟩
  set x : ℕ := M * (2 + M * c) with hx
  have hgx : g = x + 1 := by rw [hg, hx]; ring
  set S : ℕ := ∑ i ∈ Finset.range e, (x + 1) ^ i with hS
  have hgeo : S * x + 1 = g ^ e := by rw [hgx]; exact geom_sum_mul_add x e
  have hSe : S * (2 + M * c) ≡ 2 * e [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [hS, hx]
    push_cast
    simp [mul_comm]
  have hnd : ¬ l ^ k ∣ S * (2 + M * c) := by
    intro hd
    have := Nat.le_of_dvd (by omega) ((hSe.dvd_iff hM).1 hd)
    omega
  have hS0 : S * (2 + M * c) ≠ 0 := by rintro h; exact hnd (h ▸ dvd_zero _)
  have hvS : padicValNat l (S * (2 + M * c)) ≤ k := by
    by_contra hc
    exact hnd ((pow_dvd_pow l (by omega)).trans pow_padicValNat_dvd)
  have hval : padicValNat l (g ^ e - 1) = padicValNat l (S * (2 + M * c)) + padicValNat l M := by
    have : S * x = S * (2 + M * c) * M := by rw [hx]; ring
    rw [← hgeo, Nat.add_sub_cancel, this, padicValNat.mul hS0 hM0.ne']
  have hle : l ^ (4 * padicValNat l (g ^ e - 1)) ≤ M ^ 8 := by
    have a1 : l ^ padicValNat l M ≤ M := Nat.le_of_dvd hM0 pow_padicValNat_dvd
    have a2 : l ^ k ≤ M := Nat.le_of_dvd hM0 hM
    calc l ^ (4 * padicValNat l (g ^ e - 1)) ≤ l ^ (k * 4 + padicValNat l M * 4) :=
          Nat.pow_le_pow_right hl.pos (by rw [hval]; omega)
      _ = (l ^ k) ^ 4 * (l ^ padicValNat l M) ^ 4 := by rw [pow_add, ← pow_mul, ← pow_mul]
      _ ≤ M ^ 4 * M ^ 4 := Nat.mul_le_mul (Nat.pow_le_pow_left a2 4) (Nat.pow_le_pow_left a1 4)
      _ = M ^ 8 := by ring
  have hge : g ≤ g ^ e := Nat.le_self_pow (by omega) g
  omega

theorem exists_modulus_bb_disjoint : ∀ (r g0 m : ℕ), g0.Prime → m ≠ 0 → ∃ M N : ℕ, M ≠ 0 ∧ m ∣ M ∧
    ∀ g1 : ℕ, g1.Prime → N < g1 → g1 ≡ (1 + M) ^ 2 [MOD M ^ 2] →
      Disjoint (Formalism.CyclotomicNorms.BB r g0) (Formalism.CyclotomicNorms.BB r g1) := by
  intro r g0 m hg0 hm
  set P : ℕ := g0 * ∏ i ∈ Finset.range r, (g0 ^ (i + 1) - 1) with hP
  have hP0 : 0 < P := by
    refine Nat.mul_pos hg0.pos (Finset.prod_pos fun i _ => ?_)
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.succ_ne_zero i) hg0.one_lt)
  set M : ℕ := (m * P) ^ (2 * r + 1) with hM
  have hmP : 0 < m * P := Nat.mul_pos (Nat.pos_of_ne_zero hm) hP0
  have hM0 : 0 < M := pow_pos hmP _
  have hmM : m ∣ M := (Dvd.intro P rfl).trans (dvd_pow_self _ (by omega))
  refine ⟨M, M ^ 8 + 1 + 2 * M + P, hM0.ne', hmM, fun g1 _ hgt hmod => ?_⟩
  have hmod' : 1 + 2 * M ≡ g1 [MOD M ^ 2] := by
    refine Nat.ModEq.trans ?_ hmod.symm
    have : (1 + M) ^ 2 = 1 + 2 * M + M ^ 2 := by ring
    rw [this]
    exact (Nat.add_modEq_right).symm
  obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' (show 1 + 2 * M ≤ g1 by omega)).1 hmod'
  have hg1 : g1 = 1 + 2 * M + M ^ 2 * c := by omega
  have hbig : M ^ 8 ≤ g1 := by omega
  rw [Set.disjoint_left]
  intro l hl0 hl1
  have hlP : l.Prime ∧ l ∣ P := by
    rcases hl0 with h | ⟨e, h1, h9, h⟩
    · rw [Set.mem_singleton_iff.1 h]; exact ⟨hg0, Dvd.intro _ rfl⟩
    · exact ⟨h.1, (exc_dvd_prod_range hg0.pos h1 h9 h).trans (Dvd.intro_left _ rfl)⟩
  rcases hl1 with h | ⟨e, h1, h9, h⟩
  · have := Nat.le_of_dvd hP0 hlP.2
    rw [Set.mem_singleton_iff.1 h] at this
    omega
  · have hk : 2 * r + 1 < l ^ (2 * r + 1) := Nat.lt_pow_self hlP.1.one_lt
    exact not_exc_of_cong_sq hlP.1 (pow_dvd_pow_of_dvd (hlP.2.trans (Dvd.intro_left _ rfl)) (2 * r + 1)) hM0 hg1
      hbig h1 (by omega) h

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormPrime
section
namespace GlobalTheory.Mem.LevelPrime

section Quadratic

open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder

theorem norm_nonneg_of_imag_quadratic (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (x : 𝓞 K) : 0 ≤ Algebra.norm ℤ x := by
  classical
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hne : ComplexEmbedding.conjugate φ ≠ φ := by
    intro h
    exact IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 h)
  have hcard : Fintype.card (K →+* ℂ) = 2 := by rw [Embeddings.card, h2]
  have huniv : (Finset.univ : Finset (K →+* ℂ)) = {ComplexEmbedding.conjugate φ, φ} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, hcard]
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ (x : K)
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f (x : K)) (fun σ => σ (x : K))
    (fun _ => by simp [RingHom.equivRatAlgHom_apply]), huniv, Finset.prod_pair hne,
    ComplexEmbedding.conjugate_coe_eq, mul_comm, Complex.mul_conj, ← Algebra.coe_norm_int] at h1
  have h3 : ((Algebra.norm ℤ x : ℤ) : ℝ) = Complex.normSq (φ x) := by
    apply Complex.ofReal_injective
    rw [← h1]; simp
  have h4 : (0 : ℝ) ≤ ((Algebra.norm ℤ x : ℤ) : ℝ) := h3 ▸ Complex.normSq_nonneg _
  exact_mod_cast h4

theorem exists_prime_norm_of_two_le (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (M : ℕ) (hM : 2 ≤ M) (a : 𝓞 K) (ha : IsCoprime a (M : 𝓞 K)) (N : ℕ) :
    ∃ (π : 𝓞 K) (p : ℕ), p.Prime ∧ N < p ∧ Algebra.norm ℤ π = p ∧ π - a ∈ Ideal.span {(M : 𝓞 K)} := by
  obtain ⟨D⟩ := nonempty_rayData_of_ne_zero K M (by omega)
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hu : IsUnit ((M : ℕ) : 𝓞 K) := isCoprime_zero_left.1 ha
    have h1 := hu.map (Algebra.norm ℤ)
    have h3 : Algebra.norm ℤ ((M : ℕ) : 𝓞 K) = (M : ℤ) ^ 2 := by
      have := Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 K) (M : ℤ)
      rw [RingOfIntegers.rank, h2] at this
      simpa using this
    rw [h3, isUnit_pow_iff two_ne_zero, Int.isUnit_iff] at h1
    omega
  have hac : IsCoprime (Ideal.span {a}) (Ideal.span {(M : 𝓞 K)}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).2 ha
  obtain ⟨v, hc, hp, hN⟩ := GlobalTheory.Mem.RayPrimes.exists_prime_in_class K h2 M hM D (D.cls (Ideal.span {a})) N
  obtain ⟨x, y, hx0, hy0, hx, hy, hxy⟩ := (D.cls_eq _ _ v.2 hac v.1.ne_bot
    (by simpa using ha0)).1 hc
  rw [Ideal.span_singleton_mul_span_singleton] at hxy
  have hdvd : x ∣ y * a := by
    rw [← Ideal.mem_span_singleton]
    have : y * a ∈ Ideal.span {x} * v.1.asIdeal := by
      rw [hxy]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left this
  obtain ⟨π, hπ⟩ := hdvd
  have hv : v.1.asIdeal = Ideal.span {π} := by
    rw [hπ, ← Ideal.span_singleton_mul_span_singleton] at hxy
    exact mul_left_cancel₀ (by simpa using hx0) hxy
  refine ⟨π, Ideal.absNorm v.1.asIdeal, hp, hN, ?_, ?_⟩
  · rw [hv, Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg (norm_nonneg_of_imag_quadratic K h2 π)]
  · have : π - a = (y - 1) * a - (x - 1) * π := by linear_combination -hπ
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hy) (Ideal.mul_mem_right _ _ hx)

theorem exists_prime_norm : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), M ≠ 0 → ∀ (a : 𝓞 K), IsCoprime a (M : 𝓞 K) → ∀ N : ℕ, ∃ (π : 𝓞 K) (p : ℕ), p.Prime ∧ N < p ∧ Algebra.norm ℤ π = p ∧ π - a ∈ Ideal.span {(M : 𝓞 K)} := by
  intro K _ _ _ h2 M hM a ha N
  rcases Nat.lt_or_ge M 2 with h | h
  · obtain rfl : M = 1 := by omega
    obtain ⟨π, p, hp, hN, hn, -⟩ := exists_prime_norm_of_two_le K h2 2 le_rfl 1 isCoprime_one_left N
    exact ⟨π, p, hp, hN, hn, by simp⟩
  · exact exists_prime_norm_of_two_le K h2 M h a ha N

end Quadratic

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

theorem norm_eq_mul_conj {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (x : K) :
    ((Algebra.norm ℚ x : ℚ) : ℂ) = φ x * starRingEnd ℂ (φ x) := by
  classical
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have hne : φ.toRatAlgHom ≠ (ComplexEmbedding.conjugate φ).toRatAlgHom := by
    intro he
    have hc := IsTotallyComplex.isComplex (InfinitePlace.mk φ)
    apply InfinitePlace.isComplex_mk_iff.mp hc
    rw [ComplexEmbedding.isReal_iff]
    ext y
    exact (congrArg (fun f : K →ₐ[ℚ] ℂ => f y) he).symm
  have hu : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) =
      {φ.toRatAlgHom, (ComplexEmbedding.conjugate φ).toRatAlgHom} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, AlgHom.card, h2]
  rw [hu, Finset.prod_pair hne] at h
  exact h

variable {R : Ranks}

theorem sqrtMinusD_mem (H : Host R) : H.sqrtMinusD ∈ H.K :=
  IntermediateField.mem_adjoin_simple_self ℚ _

theorem finrank_K (H : Host R) : Module.finrank ℚ H.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos H.sqrtMinusD_sq

theorem isTotallyComplex_K (H : Host R) : IsTotallyComplex H.K := by
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  set b : H.K := ⟨H.sqrtMinusD, sqrtMinusD_mem H⟩
  have hb : b ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simpa [b] using H.sqrtMinusD_sq
  have h1 := congrArg (InfinitePlace.embedding_of_isReal hw) hb
  rw [map_pow, map_neg, map_natCast] at h1
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hw b)]

theorem norm_K (H : Host R) (x : H.K) :
    (x : H.E) * H.conj (x : H.E) = ((Algebra.norm ℚ x : ℚ) : H.E) := by
  have := isTotallyComplex_K H
  apply H.φ₀.injective
  have h1 : H.φ₀ (H.conj (x : H.E)) = starRingEnd ℂ (H.φ₀ (x : H.E)) :=
    Formalism.HC.HostAx.conjE_apply H.toHostAx _ _
  rw [map_mul, h1, map_ratCast,
    norm_eq_mul_conj (finrank_K H) (H.φ₀.comp (algebraMap H.K H.E)) x]
  rfl

theorem dvd_of_eq_mul_integral {E : Type} [Field E] [NumberField E] {M : ℕ} (hM : M ≠ 0) {n : ℤ} {y : E}
    (hy : IsIntegral ℤ y) (h : (n : E) = M * y) : (M : ℤ) ∣ n := by
  have hM' : (M : E) ≠ 0 := by exact_mod_cast hM
  have hM'' : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  have e : y = algebraMap ℚ E ((n : ℚ) / M) := by
    rw [map_div₀, map_intCast, map_natCast, h]; field_simp
  rw [e, isIntegral_algebraMap_iff (algebraMap ℚ E).injective] at hy
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp hy
  refine ⟨k, ?_⟩
  have : (n : ℚ) = M * k := by
    have hk' : (k : ℚ) = n / M := by simpa using hk
    rw [hk']; field_simp
  exact_mod_cast this

theorem exists_norm_prime : ∀ (R : Ranks) (H : Host R) (M a N : ℕ), M ≠ 0 → Nat.Coprime a M →
    ∃ (π : 𝓞 H.E) (p : ℕ), p.Prime ∧ N < p ∧ (π : H.E) ∈ H.K ∧
      (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧ π - (a : 𝓞 H.E) ∈ Ideal.span {(M : 𝓞 H.E)} ∧
      p ≡ a ^ 2 [MOD M] := by
  intro R H M a N hM haM
  have := isTotallyComplex_K H
  obtain ⟨π, p, hp, hN, hn, hc⟩ := exists_prime_norm H.K (finrank_K H) M hM (a : 𝓞 H.K)
    (Nat.Coprime.cast haM) N
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hc
  have hπ : ((algebraMap (𝓞 H.K) (𝓞 H.E) π : 𝓞 H.E) : H.E) = ((π : H.K) : H.E) := rfl
  have hnorm : ((π : H.K) : H.E) * H.conj ((π : H.K) : H.E) = (p : H.E) := by
    rw [norm_K, ← Algebra.coe_norm_int, hn]
    simp
  have hx' : algebraMap (𝓞 H.K) (𝓞 H.E) x * (M : 𝓞 H.E) =
      algebraMap (𝓞 H.K) (𝓞 H.E) π - (a : 𝓞 H.E) := by
    have := congrArg (algebraMap (𝓞 H.K) (𝓞 H.E)) hx
    rwa [map_mul, map_sub, map_natCast, map_natCast] at this
  refine ⟨algebraMap (𝓞 H.K) (𝓞 H.E) π, p, hp, hN, ?_, ?_, Ideal.mem_span_singleton'.mpr ⟨_, hx'⟩, ?_⟩
  · rw [hπ]; exact (π : H.K).2
  · rw [hπ]; exact hnorm
  · set y : 𝓞 H.E := algebraMap (𝓞 H.K) (𝓞 H.E) x
    have hy : IsIntegral ℤ (y : H.E) := y.isIntegral_coe
    have hcy : IsIntegral ℤ (H.conj (y : H.E)) := hy.map (H.conj.toAlgHom.restrictScalars ℤ)
    have e : ((π : H.K) : H.E) = a + M * (y : H.E) := by
      have := congrArg (algebraMap (𝓞 H.E) H.E) hx'
      rw [map_mul, map_sub, map_natCast, map_natCast] at this
      rw [← hπ]
      linear_combination -this
    rw [e, map_add, map_mul, map_natCast, map_natCast] at hnorm
    have hd : (M : ℤ) ∣ (p : ℤ) - (a : ℤ) ^ 2 := by
      apply dvd_of_eq_mul_integral (E := H.E) hM
        (y := a * (y : H.E) + a * H.conj (y : H.E) + M * ((y : H.E) * H.conj (y : H.E)))
      · have ha : IsIntegral ℤ (a : H.E) := by
          simpa using (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := (a : ℤ)))
        have hMi : IsIntegral ℤ (M : H.E) := by
          simpa using (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := (M : ℤ)))
        exact ((ha.mul hy).add (ha.mul hcy)).add (hMi.mul (hy.mul hcy))
      · push_cast
        linear_combination -hnorm
    apply Nat.ModEq.symm
    rw [Nat.modEq_iff_dvd]
    exact_mod_cast hd

end GlobalTheory.Mem.LevelPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityCongrUnitAtPlace
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem exists_root_congr_unit : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)),
    IsPlaceOver A P → ∀ u : 𝓞 E, u ∉ P.asIdeal →
      ∃ ζ : Ω, ζ ^ (normV P - 1) = 1 ∧ A.valuation (ζ - algebraMap E Ω (u : E)) < 1 := by
  intro E Ω _ _ _ _ _ A P hA u hu
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI hfin : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  letI : Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _
  haveI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field _
  set q := normV P with hq
  have hqc : q = Fintype.card (𝓞 E ⧸ P.asIdeal) := by
    rw [hq, normV, Nat.card_eq_fintype_card]
  have hq1 : 1 < q := by rw [hqc]; exact Fintype.one_lt_card
  set n := q - 1 with hn
  have hn0 : 0 < n := by omega

  have hmem : u ^ n - 1 ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
    have h0 : (Ideal.Quotient.mk P.asIdeal u) ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have := FiniteField.pow_card_sub_one_eq_one _ h0
    rwa [← hqc] at this
  have hlt : A.valuation (algebraMap E Ω ((u ^ n - 1 : 𝓞 E) : E)) < 1 := (hA _).mpr hmem
  set a : Ω := algebraMap E Ω (u : E) with ha
  have hcast : algebraMap E Ω ((u ^ n - 1 : 𝓞 E) : E) = a ^ n - 1 := by
    simp [ha]
  rw [hcast] at hlt

  set p : Polynomial Ω := Polynomial.X ^ n - Polynomial.C 1 with hp
  have hmon : p.Monic := Polynomial.monic_X_pow_sub_C 1 hn0.ne'
  have hprod := (IsAlgClosed.splits p).eq_prod_roots_of_monic hmon
  have heval : a ^ n - 1 = (p.roots.map (fun ζ => a - ζ)).prod := by
    have := congrArg (Polynomial.eval a) hprod
    rw [Polynomial.eval_multiset_prod, Multiset.map_map] at this
    simp only [hp, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, Function.comp_def] at this
    rw [this]
  by_contra hcon
  push_neg at hcon
  have hall : ∀ ζ ∈ p.roots, 1 ≤ A.valuation (a - ζ) := by
    intro ζ hζ
    have hroot : ζ ^ n = 1 := by
      have := (Polynomial.mem_roots hmon.ne_zero).mp hζ
      simpa [hp, sub_eq_zero] using this
    rw [Valuation.map_sub_swap]
    exact hcon ζ hroot
  have : 1 ≤ A.valuation (a ^ n - 1) := by
    rw [heval, map_multiset_prod, Multiset.map_map]
    have key : ∀ s : Multiset Ω, (∀ ζ ∈ s, 1 ≤ A.valuation (a - ζ)) →
        1 ≤ (s.map (A.valuation ∘ fun ζ => a - ζ)).prod := by
      intro s
      induction s using Multiset.induction_on with
      | empty => intro _; simp
      | cons b s ih =>
        intro h
        rw [Multiset.map_cons, Multiset.prod_cons]
        exact one_le_mul (h b (Multiset.mem_cons_self b s))
          (ih fun ζ hζ => h ζ (Multiset.mem_cons_of_mem hζ))
    exact key _ hall
  exact absurd hlt (not_lt.mpr this)

end GlobalTheory.TameTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasSignatureDiagonalSgn
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

theorem hasSignature_diagonal_sgn (N : ℕ) (neg : Fin N → Bool) :
    Formalism.UG.HasSignature (Matrix.diagonal fun i : Fin N => (Examples₂.sgn (neg i) : ℂ))
      (Finset.univ.filter fun i => neg i = false).card
      (Finset.univ.filter fun i => neg i = true).card := by
  classical
  let e1 : {i // neg i = false} ≃ Fin (Finset.univ.filter fun i => neg i = false).card :=
    Fintype.equivFinOfCardEq (Fintype.card_subtype _)
  let e2 : {i // ¬ neg i = false} ≃ Fin (Finset.univ.filter fun i => neg i = true).card :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_subtype]; simp)
  let f : Fin (Finset.univ.filter fun i => neg i = false).card ⊕
      Fin (Finset.univ.filter fun i => neg i = true).card ≃ Fin N :=
    (Equiv.sumCongr e1.symm e2.symm).trans (Equiv.sumCompl fun i => neg i = false)
  have h1 : ∀ i, neg (f (Sum.inl i)) = false := fun i => (e1.symm i).2
  have h2 : ∀ i, neg (f (Sum.inr i)) = true := fun i => by
    have h : ¬ neg (f (Sum.inr i)) = false := (e2.symm i).2
    simpa using h
  refine ⟨f.symm, 1, ?_⟩
  simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, h1, h2, Examples₂.sgn]
  split_ifs <;> simp

theorem stdSpace_sigOK_count (E : Type) [Field E] [NumberField E] [StarRing E]
    (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) (neg : Fin N → Bool) :
    (Formalism.BasicNotions.Examples₂.stdSpace hstar N neg (Finset.univ.filter fun i => neg i = false).card
      (Finset.univ.filter fun i => neg i = true).card).SigOK := by
  intro τ
  have hg : (Formalism.BasicNotions.Examples₂.stdSpace hstar N neg (Finset.univ.filter fun i => neg i = false).card
      (Finset.univ.filter fun i => neg i = true).card).gram.map τ =
      Matrix.diagonal fun i : Fin N => (Examples₂.sgn (neg i) : ℂ) := by
    ext i j
    rw [Matrix.map_apply]
    refine (congrArg τ (Examples₂.stdSpace_gram_apply hstar N neg _ _ i j)).trans ?_
    change τ (if i = j then (Examples₂.sgn (neg i) : E) else 0) =
      if i = j then (Examples₂.sgn (neg i) : ℂ) else 0
    by_cases h : i = j <;> simp [h, Examples₂.map_sgn]
  rw [hg]
  exact hasSignature_diagonal_sgn N neg

end GlobalTheory
end

