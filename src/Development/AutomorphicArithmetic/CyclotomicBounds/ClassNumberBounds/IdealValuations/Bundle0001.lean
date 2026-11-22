import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.ResidueUnit
import Mathlib

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.ConjCount
section
open NumberField NumberField.IsCMField NumberField.Units IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.IdealValuations

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

private theorem count_coe_map_conj (v : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) :
    FractionalIdeal.count K v
        ((J.map (ringOfIntegersComplexConj K).toRingEquiv : Ideal (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.count K (conjPrime v) (J : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  set c := (ringOfIntegersComplexConj K).toRingEquiv with hc
  rcases eq_or_ne J 0 with rfl | hJ
  · simp [FractionalIdeal.count_zero]
  have hJ' : J.map c ≠ 0 := by
    intro h
    exact hJ ((Ideal.map_eq_bot_iff_of_injective c.injective).mp h)
  rw [FractionalIdeal.count_coe K v hJ', FractionalIdeal.count_coe K _ hJ]
  congr 1
  refine eq_of_forall_le_iff fun n => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ') v.associates_irreducible,
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ)
      (conjPrime v).associates_irreducible,
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
    Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
  have h1 : (conjPrime v).asIdeal = v.asIdeal.comap c := rfl
  rw [h1, ← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]

private theorem count_spanSingleton_conj_int (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (complexConj K (a : K))) =
      FractionalIdeal.count K (conjPrime v) (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)) := by
  have h := count_coe_map_conj v (Ideal.span {a})
  rw [Ideal.map_span, Set.image_singleton, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.coeIdeal_span_singleton] at h
  exact h

theorem count_spanSingleton_conj (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (complexConj K x)) =
      FractionalIdeal.count K (conjPrime v) (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [FractionalIdeal.count_zero]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have ha0 : algebraMap (𝓞 K) K a ≠ 0 := fun h => hx (by simp [h])
  have hb0 : algebraMap (𝓞 K) K b ≠ 0 := fun h => hx (by simp [h])
  have key : ∀ (w : HeightOneSpectrum (𝓞 K)) (y z : K), y ≠ 0 → z ≠ 0 →
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ (y / z)) =
        FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ y) -
        FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ z) := by
    intro w y z hy hz
    rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul K w (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero hz)),
      ← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, sub_eq_add_neg]
  rw [map_div₀, key _ _ _ (by simpa using ha0) (by simpa using hb0), key _ _ _ ha0 hb0]
  congr 1
  · exact count_spanSingleton_conj_int v a
  · exact count_spanSingleton_conj_int v b

theorem count_fromBase (v : HeightOneSpectrum (𝓞 K)) {b : IdealGroup K} (hb : b ∈ fromBase K) :
    FractionalIdeal.count K v (b : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.count K (conjPrime v) (b : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨I, hI⟩ := hb
  obtain ⟨d, J, hd, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul
    (I : FractionalIdeal (𝓞 (maximalRealSubfield K))⁰ (maximalRealSubfield K))
  have hbI : (b : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.extendedHom K (𝓞 K)
      (I : FractionalIdeal (𝓞 (maximalRealSubfield K))⁰ (maximalRealSubfield K)) := by
    rw [← hI]; rfl
  have hd1 : (FractionalIdeal.spanSingleton (𝓞 (maximalRealSubfield K))⁰
      (algebraMap _ (maximalRealSubfield K) d)⁻¹) =
      ((Ideal.span {d} : Ideal (𝓞 (maximalRealSubfield K))) :
        FractionalIdeal (𝓞 (maximalRealSubfield K))⁰ (maximalRealSubfield K))⁻¹ := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_inv]
  have key : ∀ A : Ideal (𝓞 (maximalRealSubfield K)),
      FractionalIdeal.count K v ((A.map (algebraMap _ (𝓞 K)) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.count K (conjPrime v) ((A.map (algebraMap _ (𝓞 K)) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K) := by
    intro A
    rw [← count_coe_map_conj]
    congr 2
    have : ((ringOfIntegersComplexConj K).toRingEquiv : 𝓞 K →+* 𝓞 K).comp
        (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) = algebraMap _ _ := by
      ext1 x
      exact (ringOfIntegersComplexConj K).commutes x
    conv_lhs => rw [← this, ← Ideal.map_map]
    rfl
  rw [hIJ, hd1, map_mul, map_inv₀, FractionalIdeal.extendedHom_coeIdeal_eq_map,
    FractionalIdeal.extendedHom_coeIdeal_eq_map] at hbI
  have hb0 := b.ne_zero
  rw [hbI] at hb0 ⊢
  rw [FractionalIdeal.count_mul K _ (left_ne_zero_of_mul hb0) (right_ne_zero_of_mul hb0),
    FractionalIdeal.count_mul K _ (left_ne_zero_of_mul hb0) (right_ne_zero_of_mul hb0),
    FractionalIdeal.count_inv, FractionalIdeal.count_inv, key, key]

end KStar.IdealValuations
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.Residue
section
open NumberField NumberField.IsCMField NumberField.Units IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.IdealValuations

variable {K : Type*} [Field K] [NumberField K]

private theorem residueHom_algebraMap (P : Ideal (𝓞 K)) [P.IsMaximal] (a : 𝓞 K) :
    residueHom P (algebraMap (𝓞 K) (locAt P) a) = Ideal.Quotient.mk P a := by
  unfold residueHom
  exact IsLocalization.lift_eq _ a

theorem isResidue_iff (P : Ideal (𝓞 K)) [P.IsMaximal] (x : K) (r : 𝓞 K ⧸ P) :
    IsResidue P x r ↔ ∃ y : locAt P, (y : K) = x ∧ residueHom P y = r := by
  constructor
  · rintro ⟨a, b, hb, h1, h2⟩
    have hb0 : (b : K) ≠ 0 := by
      intro h
      have : b = 0 := by exact_mod_cast h
      exact hb (this ▸ P.zero_mem)
    have hx : x ∈ locAt P := ⟨a, b, hb, by
      have : x = (a : K) * (b : K)⁻¹ := by rw [← h1]; field_simp
      exact this⟩
    refine ⟨⟨x, hx⟩, rfl, ?_⟩
    have e : (⟨x, hx⟩ : locAt P) * algebraMap (𝓞 K) (locAt P) b
        = algebraMap (𝓞 K) (locAt P) a := Subtype.ext h1
    have e2 := congrArg (residueHom P) e
    rw [map_mul, residueHom_algebraMap, residueHom_algebraMap, ← h2] at e2
    have hb' : Ideal.Quotient.mk P b ≠ 0 := fun h => hb (Ideal.Quotient.eq_zero_iff_mem.mp h)
    exact mul_right_cancel₀ hb' e2
  · rintro ⟨y, rfl, rfl⟩
    obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj P.primeCompl y
    refine ⟨a, b, b.2, congrArg Subtype.val e, ?_⟩
    have e2 := congrArg (residueHom P) e
    rwa [map_mul, residueHom_algebraMap, residueHom_algebraMap] at e2

private theorem valuation_eq_exp_count_int (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0) :
    v.valuation K (a : K) = WithZero.exp (-FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K))) := by
  have h1 : v.valuation K (a : K) = v.intValuation a := v.valuation_of_algebraMap a
  have h2 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)
      = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.coeIdeal_span_singleton a).symm
  rw [h1, h2, v.intValuation_if_neg ha, FractionalIdeal.count_coe K v (by simpa using ha)]

private theorem valuation_eq_exp_count (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hx
    simp [← e]
  have e' : x * (b : K) = (a : K) := by
    rw [← e]; exact div_mul_cancel₀ _ hbK
  have h1 := valuation_eq_exp_count_int v a ha0
  have h2 := valuation_eq_exp_count_int v b hb0
  rw [← e', map_mul, h2, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hbK), neg_add, WithZero.exp_add] at h1
  exact mul_right_cancel₀ WithZero.exp_ne_zero h1

private theorem mem_locAt_iff (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ locAt v.asIdeal ↔ v.valuation K x ≤ 1 := by
  have h : x ∈ locAt v.asIdeal ↔ x ∈ v.valuationSubringAtPrime K := Iff.rfl
  rw [h, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.mem_valuationSubring_iff]

theorem exists_unit_locAt_iff (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    (∃ u : (locAt v.asIdeal)ˣ, ((u : locAt v.asIdeal) : K) = (x : K)) ↔
      FractionalIdeal.count K v
        ((toPrincipalIdeal (𝓞 K) K x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  have key : v.valuation K (x : K) = 1 ↔ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0 := by
    rw [valuation_eq_exp_count v _ x.ne_zero, ← WithZero.exp_zero, WithZero.exp_inj, neg_eq_zero]
  rw [coe_toPrincipalIdeal, ← key]
  constructor
  · rintro ⟨u, hu⟩
    have h1 := (mem_locAt_iff v _).mp (u : locAt v.asIdeal).2
    have h2 := (mem_locAt_iff v _).mp ((u⁻¹ : (locAt v.asIdeal)ˣ) : locAt v.asIdeal).2
    have h3 : ((u : locAt v.asIdeal) : K) * (((u⁻¹ : (locAt v.asIdeal)ˣ) : locAt v.asIdeal) : K)
        = 1 := congrArg Subtype.val u.mul_inv
    have h4 := congrArg (v.valuation K) h3
    rw [map_mul, map_one] at h4
    rw [← hu]
    exact eq_one_of_one_le_mul_left h1 h2 h4.ge
  · intro h
    have h1 : (x : K) ∈ locAt v.asIdeal := (mem_locAt_iff v _).mpr h.le
    have h2 : (x : K)⁻¹ ∈ locAt v.asIdeal := (mem_locAt_iff v _).mpr (by rw [map_inv₀, h]; simp)
    exact ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ x.ne_zero),
      Subtype.ext (inv_mul_cancel₀ x.ne_zero)⟩, rfl⟩

end KStar.IdealValuations
end

