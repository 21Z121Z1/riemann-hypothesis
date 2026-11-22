import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.RecordEigenInputs
import GroundTheory.HeightsAndTheta.Heights.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PNormCountBound
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem exists_prime_natCast_mem {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ P → ∃ p : ℕ, p.Prime ∧ (p : R) ∈ P := by
  intro n
  induction n using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    exact absurd ((Ideal.eq_top_iff_one P).mpr (by simpa using h)) hP.ne_top
  | prime_mul p a hp ih =>
    intro hpa h
    rw [Nat.cast_mul] at h
    rcases hP.mem_or_mem h with h | h
    · exact ⟨p, hp, h⟩
    · exact ih (right_ne_zero_of_mul hpa) h

theorem exists_prime_mem_heightOneSpectrum {L : Type} [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 L)) : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 L) ∈ v.asIdeal := by
  have := v.isPrime
  refine exists_prime_natCast_mem v.asIdeal (Ideal.absNorm v.asIdeal) ?_ (Ideal.absNorm_mem _)
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

theorem log_absNorm_heightOneSpectrum_nonneg {L : Type} [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 L)) : 0 ≤ Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  apply Real.log_nonneg
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h

theorem log_absNorm_eq_sum {L : Type} [Field L] [NumberField L] {I : FractionalIdeal (𝓞 L)⁰ L}
    (hI : I ≠ 0) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (hT : ∀ v, FractionalIdeal.count L v I ≠ 0 → v ∈ T) :
    Real.log (FractionalIdeal.absNorm I : ℝ) =
      ∑ v ∈ T, (FractionalIdeal.count L v I : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := L) hI
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) ?_] at hfac
  · have h1 : (FractionalIdeal.absNorm I : ℝ) =
        ∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ) ^ (FractionalIdeal.count L v I) := by
      conv_lhs => rw [← hfac]
      rw [map_prod, Rat.cast_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast]
    rw [h1, Real.log_prod]
    · exact Finset.sum_congr rfl fun v _ => Real.log_zpow _ _
    · intro v _
      apply zpow_ne_zero
      rw [Ne, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    apply hT v
    intro h0
    apply hv
    rw [h0, zpow_zero]

theorem log_absNorm_primeFrac (L : Type) [Field L] [NumberField L] (q : ℕ) :
    Real.log (FractionalIdeal.absNorm (primeFrac L q) : ℝ) = Module.finrank ℚ L * Real.log q := by
  rw [primeFrac, FractionalIdeal.coeIdeal_absNorm, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  push_cast
  rw [Real.log_pow]

theorem NormCountBound.full : NormCountBound.Statement := by
  intro L _ _ 𝔠 𝔇 S a b h𝔠 h𝔇 ha hb hloc
  classical
  have fin : ∀ J : FractionalIdeal (𝓞 L)⁰ L,
      {v : HeightOneSpectrum (𝓞 L) | FractionalIdeal.count L v J ≠ 0}.Finite :=
    fun J => Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors J)
  let P := S.filter Nat.Prime
  let T : Finset (HeightOneSpectrum (𝓞 L)) := (fin 𝔠).toFinset ∪ (fin (𝔇 : FractionalIdeal (𝓞 L)⁰ L)).toFinset ∪
    P.biUnion (fun q => (fin (primeFrac L q)).toFinset)
  have h𝔠T : ∀ v, FractionalIdeal.count L v 𝔠 ≠ 0 → v ∈ T := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_union_left _ ((fin 𝔠).mem_toFinset.mpr hv))
  have h𝔇T : ∀ v, FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) ≠ 0 → v ∈ T := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_union_right _ ((fin _).mem_toFinset.mpr hv))
  have hqT : ∀ q ∈ P, ∀ v, FractionalIdeal.count L v (primeFrac L q) ≠ 0 → v ∈ T := fun q hq v hv =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q, hq, (fin _).mem_toFinset.mpr hv⟩)
  have h𝔠eq := log_absNorm_eq_sum h𝔠 T h𝔠T
  have h𝔇eq := log_absNorm_eq_sum (I := (𝔇 : FractionalIdeal (𝓞 L)⁰ L))
    (by rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact h𝔇) T h𝔇T
  rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] at h𝔇eq
  have hqeq : ∀ q ∈ P, ∑ v ∈ T, (FractionalIdeal.count L v (primeFrac L q) : ℝ) *
      Real.log (Ideal.absNorm v.asIdeal : ℝ) = Module.finrank ℚ L * Real.log q := fun q hq => by
    rw [← log_absNorm_eq_sum (primeFrac_ne_zero L (Finset.mem_filter.mp hq).2) T (hqT q hq),
      log_absNorm_primeFrac]
  have hterm : ∀ q ∈ P, ∀ v : HeightOneSpectrum (𝓞 L),
      0 ≤ a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) := fun q hq v => by
    apply div_nonneg (mul_nonneg ha (by exact_mod_cast FractionalIdeal.count_coe_nonneg L v _))
    have : (1 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_filter.mp hq).2.one_lt.le
    linarith
  have hv : ∀ v : HeightOneSpectrum (𝓞 L), |(FractionalIdeal.count L v 𝔠 : ℝ)| ≤
      ∑ q ∈ P, a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) +
        b * (FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ) := fun v => by
    obtain ⟨p, hp, hpv⟩ := exists_prime_mem_heightOneSpectrum v
    have h1 := hloc p hp v hpv
    have h2 : (if p ∈ S then a * (FractionalIdeal.count L v (primeFrac L p) : ℝ) / ((p : ℝ) - 1) else 0) ≤
        ∑ q ∈ P, a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) := by
      split_ifs with hpS
      · exact Finset.single_le_sum (f := fun q => a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) /
          ((q : ℝ) - 1)) (fun q hq => hterm q hq v) (Finset.mem_filter.mpr ⟨hpS, hp⟩)
      · exact Finset.sum_nonneg fun q hq => hterm q hq v
    linarith
  have hS : ∑ q ∈ P, Real.log q / ((q : ℝ) - 1) ≤ ∑ q ∈ S, Real.log q / ((q : ℝ) - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro q _ _
    rcases q with _ | q
    · simp
    · have : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 q
      exact div_nonneg (Real.log_nonneg this) (by linarith)
  have hfin : (0 : ℝ) ≤ Module.finrank ℚ L := Nat.cast_nonneg _
  calc |Real.log (FractionalIdeal.absNorm 𝔠 : ℝ)|
      = |∑ v ∈ T, (FractionalIdeal.count L v 𝔠 : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)| := by
        rw [h𝔠eq]
    _ ≤ ∑ v ∈ T, |(FractionalIdeal.count L v 𝔠 : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ v ∈ T, |(FractionalIdeal.count L v 𝔠 : ℝ)| * Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
        Finset.sum_congr rfl fun v _ => by
          rw [abs_mul, abs_of_nonneg (log_absNorm_heightOneSpectrum_nonneg v)]
    _ ≤ ∑ v ∈ T, (∑ q ∈ P, a * (FractionalIdeal.count L v (primeFrac L q) : ℝ) / ((q : ℝ) - 1) +
          b * (FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ)) *
          Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
        Finset.sum_le_sum fun v _ =>
          mul_le_mul_of_nonneg_right (hv v) (log_absNorm_heightOneSpectrum_nonneg v)
    _ = ∑ q ∈ P, a / ((q : ℝ) - 1) * ∑ v ∈ T, (FractionalIdeal.count L v (primeFrac L q) : ℝ) *
          Real.log (Ideal.absNorm v.asIdeal : ℝ) +
        b * ∑ v ∈ T, (FractionalIdeal.count L v (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ) *
          Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
        simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        · exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun v _ => by ring
        · exact Finset.sum_congr rfl fun v _ => by ring
    _ = Module.finrank ℚ L * (a * ∑ q ∈ P, Real.log q / ((q : ℝ) - 1)) +
        b * Real.log (Ideal.absNorm 𝔇 : ℝ) := by
        rw [h𝔇eq, Finset.sum_congr rfl fun q hq => by rw [hqeq q hq]]
        congr 1
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by ring
    _ ≤ Module.finrank ℚ L * (a * ∑ q ∈ S, Real.log q / ((q : ℝ) - 1)) +
        b * Real.log (Ideal.absNorm 𝔇 : ℝ) := by
        gcongr

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PPrimeLogSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open Finset

namespace PrimeLogSum

theorem term_le {p : ℕ} (hp : 2 ≤ p) :
    Real.log p / ((p : ℝ) - 1) ≤ 2 * (Real.log p / p) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  calc Real.log p / ((p : ℝ) - 1) ≤ Real.log p / ((p : ℝ) / 2) :=
        div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by positivity) (by linarith)
    _ = 2 * (Real.log p / p) := by ring

theorem block_le (k : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ Nat.log 2 p = k) :
    ∑ p ∈ S, Real.log p / p ≤ 2 * Real.log 4 := by
  have h1 : ∑ p ∈ S, Real.log p / p ≤ ∑ p ∈ S, Real.log p / (2 : ℝ) ^ k := by
    apply sum_le_sum
    intro p hp
    obtain ⟨hpp, hk⟩ := hS p hp
    apply div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (by positivity)
    have := Nat.pow_log_le_self 2 hpp.ne_zero
    rw [hk] at this
    exact_mod_cast this
  have h2 : ∑ p ∈ S, Real.log p ≤ Chebyshev.theta ((2 ^ (k + 1) : ℕ) : ℝ) := by
    rw [Chebyshev.theta, Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpp, hk⟩ := hS p hp
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
      rw [hk] at this
      simp only [mem_filter, mem_Ioc]
      exact ⟨⟨hpp.pos, this.le⟩, hpp⟩
    · intro p _ _
      exact Real.log_natCast_nonneg p
  have h3 := Chebyshev.theta_le_log4_mul_x (x := ((2 ^ (k + 1) : ℕ) : ℝ)) (by positivity)
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  calc ∑ p ∈ S, Real.log p / p ≤ ∑ p ∈ S, Real.log p / (2 : ℝ) ^ k := h1
    _ = (∑ p ∈ S, Real.log p) / (2 : ℝ) ^ k := by rw [sum_div]
    _ ≤ Chebyshev.theta ((2 ^ (k + 1) : ℕ) : ℝ) / (2 : ℝ) ^ k := by gcongr
    _ ≤ Real.log 4 * ((2 ^ (k + 1) : ℕ) : ℝ) / (2 : ℝ) ^ k := by gcongr
    _ = 2 * Real.log 4 := by
      push_cast
      rw [pow_succ]
      field_simp

theorem natLog_mul_log_two_le {N : ℕ} (hN : N ≠ 0) :
    (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
  have h := Nat.pow_log_le_self 2 hN
  have h' : (2 : ℝ) ^ Nat.log 2 N ≤ N := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rwa [Real.log_pow] at this

theorem small_le {N : ℕ} (hN : 2 ≤ N) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N) :
    ∑ p ∈ S, Real.log p / p ≤ 8 * Real.log N := by
  have hmap : ∀ p ∈ S, Nat.log 2 p ∈ range (Nat.log 2 N + 1) := by
    intro p hp
    simp only [mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right (hS p hp).2)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hblocks : ∑ k ∈ range (Nat.log 2 N + 1), ∑ p ∈ S with Nat.log 2 p = k, Real.log p / p
      ≤ ∑ k ∈ range (Nat.log 2 N + 1), 2 * Real.log 4 := by
    apply sum_le_sum
    intro k _
    apply block_le k
    intro p hp
    simp only [mem_filter] at hp
    exact ⟨(hS p hp.1).1, hp.2⟩
  have hcount : ∑ k ∈ range (Nat.log 2 N + 1), 2 * Real.log 4
      = 2 * Real.log 4 * ((Nat.log 2 N : ℝ) + 1) := by
    simp [sum_const, card_range]
    ring
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN'
  have hnl := natLog_mul_log_two_le (N := N) (by omega)
  have hl2pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc _ ≤ _ := hblocks
    _ = 2 * Real.log 4 * ((Nat.log 2 N : ℝ) + 1) := hcount
    _ = 4 * ((Nat.log 2 N : ℝ) * Real.log 2 + Real.log 2) := by rw [hlog4]; ring
    _ ≤ 4 * (Real.log N + Real.log N) := by gcongr
    _ ≤ 8 * Real.log N := by linarith

theorem large_le {B : ℕ} (hB : 2 ≤ B) (S : Finset ℕ) (hS : ∀ p ∈ S, B < p) (hcard : S.card ≤ B) :
    ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 4 * Real.log B := by
  have hB' : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have he : Real.exp 1 ≤ (B : ℝ) + 1 := by
    have := Real.exp_one_lt_d9
    linarith
  have hterm : ∀ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1)) := by
    intro p hp
    have hBp : B + 1 ≤ p := hS p hp
    have hBp' : (B : ℝ) + 1 ≤ p := by exact_mod_cast hBp
    refine (term_le (by omega)).trans ?_
    have := Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he)
      (Set.mem_Ici.mpr (he.trans hBp')) hBp'
    simp only at this
    linarith
  have hsum := sum_le_sum hterm
  rw [sum_const, nsmul_eq_mul] at hsum
  have hcard' : (S.card : ℝ) ≤ B := by exact_mod_cast hcard
  have hlogpos : 0 ≤ Real.log ((B : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hq : 0 ≤ 2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1)) := by positivity
  have h1 : (S.card : ℝ) * (2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1)))
      ≤ 2 * Real.log ((B : ℝ) + 1) := by
    calc (S.card : ℝ) * (2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1)))
        ≤ ((B : ℝ) + 1) * (2 * (Real.log ((B : ℝ) + 1) / ((B : ℝ) + 1))) := by
          gcongr
          linarith
      _ = 2 * Real.log ((B : ℝ) + 1) := by field_simp
  have h2 : Real.log ((B : ℝ) + 1) ≤ 2 * Real.log B := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < (B : ℝ) + 1)
      (show (B : ℝ) + 1 ≤ (B : ℝ) ^ 2 by nlinarith)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  linarith

theorem full : Statement := by
  refine ⟨20, fun B hB P hP hcard => ?_⟩
  rw [← sum_filter_add_sum_filter_not P (fun p => p ≤ B)]
  have hsmall : ∑ p ∈ P with p ≤ B, Real.log p / ((p : ℝ) - 1) ≤ 16 * Real.log B := by
    calc ∑ p ∈ P with p ≤ B, Real.log p / ((p : ℝ) - 1)
        ≤ ∑ p ∈ P with p ≤ B, 2 * (Real.log p / p) := by
          apply sum_le_sum
          intro p hp
          simp only [mem_filter] at hp
          exact term_le (hP p hp.1).two_le
      _ = 2 * ∑ p ∈ P with p ≤ B, Real.log p / p := by rw [mul_sum]
      _ ≤ 2 * (8 * Real.log B) := by
          gcongr
          apply small_le hB
          intro p hp
          simp only [mem_filter] at hp
          exact ⟨hP p hp.1, hp.2⟩
      _ = 16 * Real.log B := by ring
  have hlarge : ∑ p ∈ P with ¬ p ≤ B, Real.log p / ((p : ℝ) - 1) ≤ 4 * Real.log B := by
    apply large_le hB
    · intro p hp
      simp only [mem_filter] at hp
      omega
    · exact (card_filter_le _ _).trans hcard
  linarith

end PrimeLogSum

end GroundTheory.Heights₂.Heights.NineStatements
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PowLeSqrtDetGram
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MeasureTheory Module

theorem pow_le_sqrt_det_gram {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {m : ℕ} (b : Fin m → V) (hb : LinearIndependent ℝ b) {lam : ℝ} (hlam : 0 ≤ lam)
    (hmin : ∀ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) :
    (lam / Real.sqrt m) ^ m ≤ Real.sqrt (Matrix.gram ℝ b).det := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  set W := Submodule.span ℝ (Set.range b)
  let B : Basis (Fin m) ℝ W := Basis.span hb
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  let _ : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have hBW : ∀ i, ((B i : W) : V) = b i := fun i => congrArg Subtype.val (Basis.span_apply hb i)
  have hfin : finrank ℝ W = m := by rw [finrank_eq_card_basis B, Fintype.card_fin]
  let Λ : Submodule ℤ W := Submodule.span ℤ (Set.range B)
  have hcov : ZLattice.covolume Λ = Real.sqrt (Matrix.gram ℝ b).det := by
    rw [GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram Λ (B.restrictScalars ℤ)]
    congr 2
    ext i j
    simp only [Matrix.gram, Matrix.of_apply]
    rw [Basis.restrictScalars_apply, Basis.restrictScalars_apply]
    exact congrArg₂ (inner ℝ) (hBW i) (hBW j)
  have hF := ZSpan.isAddFundamentalDomain' B (volume : Measure W)
  have hFvol : volume (ZSpan.fundamentalDomain B) =
      ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ b).det) := by
    rw [← hcov, ZLattice.covolume_eq_measure_fundamentalDomain Λ volume
      (ZSpan.isAddFundamentalDomain B volume), measureReal_def, ENNReal.ofReal_toReal]
    exact (ZSpan.fundamentalDomain_isBounded B).measure_lt_top.ne
  let o : OrthonormalBasis (Fin m) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr hfin)
  set r := lam / Real.sqrt m with hr
  let f : W →ₗ[ℝ] (Fin m → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).toLinearMap ∘ₗ o.repr.toLinearEquiv.toLinearMap
  have hf : ∀ x, f x = WithLp.ofLp (o.repr x) := fun x => rfl
  let s : Set W := f ⁻¹' Set.univ.pi fun _ => Set.Ioo (-r) r
  have hs_symm : ∀ x ∈ s, -x ∈ s := by
    intro x hx i _
    have := hx i (Set.mem_univ i)
    simp only [map_neg, Pi.neg_apply, Set.mem_Ioo] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have hs_conv : Convex ℝ s :=
    (convex_pi fun i _ => convex_Ioo (-r) r).linear_preimage f
  have hs_vol : volume s = ENNReal.ofReal (2 * r) ^ m := by
    have h1 : s = o.repr ⁻¹' (WithLp.ofLp ⁻¹' Set.univ.pi fun _ => Set.Ioo (-r) r) := rfl
    rw [h1, (o.measurePreserving_repr).measure_preimage
      (((MeasurableSet.univ_pi fun _ => measurableSet_Ioo).preimage
        (PiLp.volume_preserving_ofLp (Fin m)).measurable).nullMeasurableSet),
      (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage
        (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet,
      Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    ring
  have hs_lat : ∀ x : W, x ∈ Λ → x ∈ s → x = 0 := by
    intro x hxΛ hxs
    by_contra hx0
    have hxV : (x : V) ∈ Submodule.span ℤ (Set.range b) := by
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxΛ
      refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, ?_⟩
      rw [← hc, Submodule.coe_sum]
      simp [hBW]
    have hxV0 : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hr0 : 0 < r := by
      have := hxs ⟨0, hm⟩ (Set.mem_univ _)
      exact neg_lt_self_iff.1 (this.1.trans this.2)
    have hnorm : ‖(x : V)‖ < lam := by
      have hxn : ‖(x : V)‖ = ‖o.repr x‖ := by
        rw [LinearIsometryEquiv.norm_map]
        rfl
      rw [hxn, EuclideanSpace.norm_eq]
      have hsum : ∑ i, ‖(o.repr x) i‖ ^ 2 < ∑ _i : Fin m, r ^ 2 := by
        have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
        refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_
        have := hxs i (Set.mem_univ i)
        rw [hf] at this
        rw [Real.norm_eq_abs, sq_abs]
        exact sq_lt_sq' this.1 this.2
      have hlam_eq : lam = Real.sqrt (∑ _i : Fin m, r ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq hr0.le, hr,
          mul_div_cancel₀ _ (Real.sqrt_pos.2 (by exact_mod_cast hm)).ne']
      rw [hlam_eq]
      exact Real.sqrt_lt_sqrt (Finset.sum_nonneg fun i _ => by positivity) hsum
    exact absurd (hmin _ hxV hxV0) (not_le.2 hnorm)
  by_contra hlt
  push Not at hlt
  have hr_nonneg : 0 ≤ r := div_nonneg hlam (Real.sqrt_nonneg _)
  have hreal : Real.sqrt (Matrix.gram ℝ b).det * 2 ^ m < (2 * r) ^ m := by
    rw [mul_pow, mul_comm]
    exact mul_lt_mul_of_pos_left hlt (by positivity)
  have h2 : (2 : ENNReal) ^ m = ENNReal.ofReal ((2 : ℝ) ^ m) := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    simp
  have hbig : volume (ZSpan.fundamentalDomain B) * 2 ^ finrank ℝ W < volume s := by
    rw [hFvol, hs_vol, hfin, h2, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (by positivity)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hreal
  have : Countable (Submodule.span ℤ (Set.range B)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range B)))
  obtain ⟨x, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hF hs_symm hs_conv hbig
  exact hx0 (Subtype.ext (hs_lat _ x.2 hxs))

end GroundTheory.Heights₂.Heights.NineStatements
end
end

