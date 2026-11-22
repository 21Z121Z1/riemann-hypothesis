import Mathlib
import Formalism.MirabolicMackeyTheory.Bundle0001
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0007
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0003
import Formalism.LogFactorialIndices.SignedSubspaceIndex.Bundle0001

-- bundled from Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.AbsorbLocalConditions
section
open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem errGood_nonneg (Y X2 A1 A2 kw T : ℝ) (th add : ℕ → ℝ) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hkw : 0 ≤ kw) (hT : 0 ≤ T) (hth : ∀ p, 0 ≤ th p) (hadd : ∀ p, 0 ≤ add p) (p : ℕ) :
    0 ≤ errGood Y X2 A1 A2 kw T th add p := by
  have hp : (0:ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have e1 : 0 ≤ A1 / (p : ℝ) := div_nonneg hA1 hp
  have e2 : 0 ≤ kw * th p := mul_nonneg hkw (hth p)
  have e3 : 0 ≤ T * add p := mul_nonneg hT (hadd p)
  have e4 : 0 ≤ A2 / (p : ℝ) ^ 2 := div_nonneg hA2 (by positivity)
  unfold errGood
  split_ifs <;> linarith

theorem onSum_of (hP : PlaceSum) (hR : RamBasic) (hE : ErrSumGood) : OnSum := by
  unfold OnSum
  intro K _ _ _ S Bad eb heb Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hPS
    errl herr
  set X : ℕ → ℝ := fun p => if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p with hX
  have hX0 : ∀ p, 0 ≤ X p := fun p => by
    simp only [hX]
    split_ifs
    · exact heb p
    · exact errGood_nonneg Y X2 A1 A2 kw T th add hA1 hA2 hkw hT hth hadd p
  have hlw : ∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ lw w := fun w => by
    unfold lw
    exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have hram : ∀ w : HeightOneSpectrum (𝓞 K), (0:ℝ) ≤ (ramw w : ℝ) := fun w => by
    have h1 := (hR K w).2.1
    exact_mod_cast (le_trans (by norm_num) h1)
  have step1 : ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w) ≤
      ∑ w ∈ S, lw w * ((ramw w : ℝ) * X (plc w)) :=
    Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (herr w hw) (hram w)) (hlw w)
  have step2 := hP K S X hX0
  have hsplit := Finset.sum_filter_add_sum_filter_not (S.image plc) (fun p => p ∈ Bad)
    (fun p => Real.log (p : ℝ) * X p)
  have step3 : ∑ p ∈ (S.image plc).filter (fun p => p ∈ Bad), Real.log (p : ℝ) * X p ≤
      ∑ p ∈ Bad, Real.log (p : ℝ) * eb p := by
    calc _ = ∑ p ∈ (S.image plc).filter (fun p => p ∈ Bad), Real.log (p : ℝ) * eb p :=
          Finset.sum_congr rfl fun p hp => by
            rw [Finset.mem_filter] at hp
            simp only [hX, if_pos hp.2]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).2)
          (fun p _ _ => mul_nonneg (Real.log_natCast_nonneg p) (heb p))
  have step4 : ∑ p ∈ (S.image plc).filter (fun p => p ∉ Bad), Real.log (p : ℝ) * X p ≤
      2 * (A1 * Real.log Y + kw * Cth + Cadd + 2.04 * A2 / X2 + 1.02 * Y) := by
    have hprime : ∀ p ∈ (S.image plc).filter (fun p => p ∉ Bad), p.Prime := by
      intro p hp
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hp).1
      exact (hR K w).1
    calc _ = ∑ p ∈ (S.image plc).filter (fun p => p ∉ Bad),
            Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p :=
          Finset.sum_congr rfl fun p hp => by
            rw [Finset.mem_filter] at hp
            simp only [hX, if_neg hp.2]
      _ ≤ _ := hE _ hprime Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hPS
  linarith

theorem absorb_local_conditions : AbsorbOn := by
  unfold AbsorbOn
  intro C Cb L xe f m b k ws Se Y X2 bad hC hCb hL hLx hf hm hb hk hlk hws0 hws hSe hkSe hY hlY
    hYmb hkX hbad
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hf0 : (0:ℝ) ≤ f := by linarith
  have hm0 : (0:ℝ) ≤ m := by linarith
  have hL0 : (0:ℝ) ≤ L := by linarith
  have hk0 : (0:ℝ) < k := by linarith
  have hX2 : (0:ℝ) < X2 := by linarith
  have hxe : (1:ℝ) ≤ xe := by linarith
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk
  have hfmb : 0 ≤ f * m * b := mul_nonneg (mul_nonneg hf0 hm0) hb.le
  have hQ : 0 ≤ f * m * b * L := mul_nonneg hfmb hL0
  have hLxe : 1 ≤ L * xe := one_le_mul_of_one_le_of_one_le hL hxe
  have fmb_le : f * m * b ≤ f * m * b * L * xe := by
    have := mul_le_mul_of_nonneg_left hLxe hfmb
    linarith
  have QL_le : f * m * b * L * L ≤ f * m * b * L * xe := mul_le_mul_of_nonneg_left hLx hQ
  have hQx : 0 ≤ f * m * b * L * xe := by linarith
  have hA0 : 0 ≤ Real.log k * m * ws := mul_nonneg (mul_nonneg hlogk hm0) hws0
  have hB0 : 0 ≤ f * k * Se := mul_nonneg (mul_nonneg hf0 hk0.le) hSe
  have a1 : Real.log k * (m * ws) ≤ L * (m * (2 * f * b)) :=
    mul_le_mul hlk (mul_le_mul_of_nonneg_left hws hm0) (mul_nonneg hm0 hws0) hL0
  have a2 : f * (k * Se * L) ≤ f * (m * b) := mul_le_mul_of_nonneg_left hkSe hf0
  have t1a : (Real.log k * m * ws + f * k * Se) * Real.log Y ≤
      (Real.log k * m * ws + f * k * Se) * (2 * L) :=
    mul_le_mul_of_nonneg_left hlY (add_nonneg hA0 hB0)
  have t1b : Real.log k * m * ws * (2 * L) ≤ 2 * (f * m * b * L) * (2 * L) := by
    have h1 : Real.log k * m * ws ≤ 2 * (f * m * b * L) := by linarith
    exact mul_le_mul_of_nonneg_right h1 (by linarith)
  have t1 : (Real.log k * m * ws + f * k * Se) * Real.log Y ≤ 6 * (f * m * b * L * xe) := by
    linarith
  have u1 : C * ((Real.log k * m * ws + f * k * Se) * Real.log Y) ≤
      C * (6 * (f * m * b * L * xe)) := mul_le_mul_of_nonneg_left t1 hC0
  have fb_le : f * b ≤ f * m * b := by
    have := mul_le_mul_of_nonneg_left hm (mul_nonneg hf0 hb.le)
    linarith
  have ws_le : ws ≤ 2 * (f * m * b * L * xe) := by linarith
  have u2 : C ^ 2 * ws ≤ C ^ 2 * (2 * (f * m * b * L * xe)) :=
    mul_le_mul_of_nonneg_left ws_le (by positivity)
  have mb_le : m * b ≤ f * m * b * L * xe := by
    have := mul_le_mul_of_nonneg_left hf (mul_nonneg hm0 hb.le)
    linarith
  have u3 : C * (m * b) ≤ C * (f * m * b * L * xe) := mul_le_mul_of_nonneg_left mb_le hC0
  have u4 : C * ws ≤ C * (2 * (f * m * b * L * xe)) := mul_le_mul_of_nonneg_left ws_le hC0
  have u5a : f * m * b * L * xe ≤ C * (f * m * b * L * xe) := le_mul_of_one_le_left hQx hC
  have u6a : Cb * (f * m * b * L) ≤ Cb * (f * m * b * L * xe) := by
    have := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hQ hxe) hCb
    linarith
  have u8 : 0 ≤ C * (f * m * b * L * xe) := mul_nonneg hC0 hQx
  have t2e : C * k * ws * (C / k) = C ^ 2 * ws := by
    have : k ≠ 0 := hk0.ne'
    field_simp
  have t4 : 2.04 * (C * k * ws) / X2 ≤ 2.04 * (C * ws) := by
    rw [div_le_iff₀ hX2]
    have := mul_le_mul_of_nonneg_left hkX (mul_nonneg hC0 hws0)
    linarith
  linarith

end Formalism.EigenvalueLevelCeiling
end

-- bundled from Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem plc_prime (w : HeightOneSpectrum (𝓞 K)) : (plc w).Prime := by
  haveI := w.isMaximal
  letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  unfold plc
  exact (CharP.char_is_prime_or_zero (𝓞 K ⧸ w.asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal))).resolve_right
    (CharP.char_ne_zero_of_finite (𝓞 K ⧸ w.asIdeal) _)

theorem plc_mem (w : HeightOneSpectrum (𝓞 K)) : ((plc w : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  unfold plc
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

private theorem vw_coe_eq_count_factors_span_of_ne_zero (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    vw w (x : K) = ((Associates.mk w.asIdeal).count
      (Associates.mk (Ideal.span {x} : Ideal (𝓞 K))).factors : ℤ) := by
  have hspan : (Ideal.span {x} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  unfold vw
  rw [← FractionalIdeal.count_coe K w hspan, FractionalIdeal.coeIdeal_span_singleton]

theorem intValuation_eq_exp' (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    w.intValuation x = WithZero.exp (-(vw w (x : K))) := by
  rw [vw_coe_eq_count_factors_span_of_ne_zero w x hx, IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg w hx]

theorem one_le_ramw (w : HeightOneSpectrum (𝓞 K)) : 1 ≤ ramw w := by
  have hm := plc_mem w
  have hne : ((plc w : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast (plc_prime w).ne_zero
  have h1 := (w.intValuation_lt_one_iff_mem _).mpr hm
  rw [intValuation_eq_exp' w _ hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  unfold ramw
  push_cast at h1
  omega

theorem plc_conjPl (w : HeightOneSpectrum (𝓞 K)) : plc (conjPl w) = plc w := by
  unfold plc
  let e := Ideal.quotientEquiv w.asIdeal (conjPl w).asIdeal (cO K) rfl
  haveI := ringChar.charP (𝓞 K ⧸ w.asIdeal)
  haveI : CharP (𝓞 K ⧸ (conjPl w).asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal)) :=
    charP_of_injective_ringHom (f := (e : 𝓞 K ⧸ w.asIdeal →+* 𝓞 K ⧸ (conjPl w).asIdeal))
      e.injective _
  exact ringChar.eq _ _

theorem ramw_conjPl (w : HeightOneSpectrum (𝓞 K)) : ramw (conjPl w) = ramw w := by
  unfold ramw
  rw [plc_conjPl, ← (valuation_basic_properties K w).2.1 ((plc w : ℕ) : K), star_natCast]

theorem sum_lw_vw_natCast_le (T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (hn : n ≠ 0) :
    ∑ w ∈ T, lw w * (vw w (n : K) : ℝ) ≤ Real.log (n : ℝ) := by
  classical
  have hd0 : (0 : ℝ) < (finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hn0 : ((n : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hn
  have hI0 : (Ideal.span {((n : ℕ) : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hn0

  obtain ⟨e, he⟩ : ∃ e : HeightOneSpectrum (𝓞 K) → ℕ, ∀ w, e w =
      (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {((n : ℕ) : 𝓞 K)})).factors :=
    ⟨_, fun _ => rfl⟩
  have hv : ∀ w, vw w (n : K) = (e w : ℤ) := by
    intro w
    have h := vw_coe_eq_count_factors_span_of_ne_zero w _ hn0
    rw [he w]
    have hc : (((n : ℕ) : 𝓞 K) : K) = (n : K) := by
      first
        | (push_cast; rfl)
        | push_cast
        | simp
    rw [hc] at h
    exact h

  have hdiv : ∀ w : HeightOneSpectrum (𝓞 K),
      w.asIdeal ^ e w ∣ Ideal.span {((n : ℕ) : 𝓞 K)} := by
    intro w
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem,
      ← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem,
      IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg w hn0, he w]
  have hdvd : ∏ w ∈ T, w.asIdeal ^ e w ∣ Ideal.span {((n : ℕ) : 𝓞 K)} := by
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      show IsCoprime (a.asIdeal ^ e a) (b.asIdeal ^ e b)
      apply IsCoprime.pow
      rw [Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne a.isMaximal b.isMaximal
        (fun h => hab (HeightOneSpectrum.ext h))
    · intro w _
      exact hdiv w
  have hP0 : Ideal.absNorm (∏ w ∈ T, w.asIdeal ^ e w) ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]
    intro h
    rw [h, zero_dvd_iff] at hdvd
    exact hI0 hdvd
  have hle : Ideal.absNorm (∏ w ∈ T, w.asIdeal ^ e w) ≤
      Ideal.absNorm (Ideal.span {((n : ℕ) : 𝓞 K)} : Ideal (𝓞 K)) := by
    apply Nat.le_of_dvd
    · apply Nat.pos_of_ne_zero
      rw [ne_eq, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]
      exact hI0
    · exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)
  have hnormI : Ideal.absNorm (Ideal.span {((n : ℕ) : 𝓞 K)} : Ideal (𝓞 K)) =
      n ^ finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 K)) n,
      Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have hNw : ∀ w : HeightOneSpectrum (𝓞 K), (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := by
    intro w
    have : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    exact_mod_cast this
  have hlog : Real.log (Ideal.absNorm (∏ w ∈ T, w.asIdeal ^ e w) : ℝ) =
      ∑ w ∈ T, (e w : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ) := by
    rw [map_prod, Nat.cast_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [map_pow, Nat.cast_pow, Real.log_pow]
    · intro w _
      rw [map_pow, Nat.cast_pow]
      exact pow_ne_zero _ (hNw w)
  have hlogle : ∑ w ∈ T, (e w : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ) ≤
      (finrank ℚ K : ℝ) * Real.log (n : ℝ) := by
    rw [← hlog, ← Real.log_pow, ← Nat.cast_pow, ← hnormI]
    apply Real.log_le_log
    · exact_mod_cast Nat.pos_of_ne_zero hP0
    · exact_mod_cast hle
  have hsum : ∑ w ∈ T, lw w * (vw w (n : K) : ℝ) =
      (∑ w ∈ T, (e w : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ)) / (finrank ℚ K : ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hv w]
    unfold lw
    push_cast
    ring
  rw [hsum, div_le_iff₀ hd0, mul_comm (Real.log (n : ℝ))]
  exact hlogle

end SlopeTestRemainingChoices

theorem ramified_basic_bound : RamBasic := by
  unfold RamBasic
  intro K _ _ _ w
  refine ⟨plc_prime w, one_le_ramw w, plc_conjPl w, ramw_conjPl w, ?_⟩
  have h1 : (1:ℝ) ≤ (ramw w : ℝ) := by exact_mod_cast one_le_ramw w
  have hp : (0:ℝ) < (plc w : ℝ) := by exact_mod_cast (plc_prime w).pos
  unfold ellw
  rw [div_pow, Real.sq_sqrt (by linarith)]
  have h2 : (ramw w : ℝ) ≠ 0 := by linarith
  have h3 : (plc w : ℝ) ≠ 0 := hp.ne'
  first
    | (field_simp; ring)
    | field_simp

theorem place_sum : PlaceSum := by
  unfold PlaceSum
  intro K _ _ _ S X hX
  rw [← Finset.sum_fiberwise_of_maps_to (fun w hw => Finset.mem_image_of_mem plc hw)]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp0 : p ≠ 0 := by
    obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hp
    rw [← hw]
    exact (plc_prime w).ne_zero
  have e : ∑ w ∈ S with plc w = p, lw w * ((ramw w : ℝ) * X (plc w)) =
      (∑ w ∈ S with plc w = p, lw w * (vw w (p : K) : ℝ)) * X p := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun w hw => ?_
    have h4 : plc w = p := (Finset.mem_filter.mp hw).2
    unfold ramw
    rw [h4]
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (sum_lw_vw_natCast_le _ p hp0) (hX p)

end Formalism.EigenvalueLevelCeiling
end
end

