import Formalism.TruncatedSeriesCounting.Bundle0001
import Mathlib

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.RrBound
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

open Finset

private theorem geom_sum_range_mul_one_sub (x : ℝ) :
    ∀ n : ℕ, Finset.sum (range n) (fun i => x ^ i) * (1 - x) = 1 - x ^ n := fun
  | 0 => by simp
  | n + 1 => by rw [sum_range_succ, add_mul, geom_sum_range_mul_one_sub x n, pow_succ]; ring

theorem tsum_le_two_level (x A B D : ℝ) (j : ℕ) (f : ℕ → ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hA0 : 0 ≤ A) (hf0 : ∀ a, 0 ≤ f a) (hfB : ∀ a, f a ≤ (B + D) * x ^ a)
    (hfA : ∀ a, a < j → f a ≤ (A + D) * x ^ a) :
    ∑' a, f a ≤ (A + B * x ^ j + D) * (1 - x)⁻¹ := by
  have hx1' : 0 < 1 - x := by linarith
  have hgeo : Summable (fun a : ℕ => (B + D) * x ^ a) :=
    (summable_geometric_of_lt_one hx0 hx1).mul_left (B + D)
  have hsum : Summable f := Summable.of_nonneg_of_le hf0 hfB hgeo
  have hsplit : Finset.sum (range j) f + ∑' a, f (a + j) = ∑' a, f a := by
    exact hsum.sum_add_tsum_nat_add j
  have hshift : Summable (fun a => f (a + j)) := by
    exact (summable_nat_add_iff j).mpr hsum
  have hg2 : HasSum (fun a : ℕ => (B + D) * x ^ j * x ^ a) ((B + D) * x ^ j * (1 - x)⁻¹) :=
    (hasSum_geometric_of_lt_one hx0 hx1).mul_left _
  have h2 : ∑' a, f (a + j) ≤ (B + D) * x ^ j * (1 - x)⁻¹ :=
    hasSum_le (fun a => by
      calc f (a + j) ≤ (B + D) * x ^ (a + j) := hfB (a + j)
        _ = (B + D) * x ^ j * x ^ a := by rw [pow_add]; ring) hshift.hasSum hg2
  have h1 : Finset.sum (range j) f ≤ (A + D) * Finset.sum (range j) (fun a => x ^ a) := by
    rw [mul_sum]
    exact sum_le_sum fun a ha => hfA a (mem_range.mp ha)
  have hS' : Finset.sum (range j) (fun a => x ^ a) = (1 - x ^ j) * (1 - x)⁻¹ := by
    rw [← geom_sum_range_mul_one_sub x j, mul_assoc, mul_inv_cancel₀ hx1'.ne', mul_one]
  have hpos : 0 ≤ A * x ^ j * (1 - x)⁻¹ :=
    mul_nonneg (mul_nonneg hA0 (pow_nonneg hx0 _)) (inv_nonneg.mpr hx1'.le)
  rw [← hsplit]
  calc Finset.sum (range j) f + ∑' a, f (a + j)
      ≤ (A + D) * Finset.sum (range j) (fun a => x ^ a) + (B + D) * x ^ j * (1 - x)⁻¹ :=
        add_le_add h1 h2
    _ = (A + B * x ^ j + D) * (1 - x)⁻¹ - A * x ^ j * (1 - x)⁻¹ := by rw [hS']; ring
    _ ≤ (A + B * x ^ j + D) * (1 - x)⁻¹ := by linarith

theorem rr_arith (l d G h y C L s r q : ℝ) (hld : l = d + 1) (hd2 : 2 ≤ d) (hG0 : 0 ≤ G)
    (hh0 : 0 ≤ h) (hy0 : 0 ≤ y) (hC0 : 0 ≤ C) (hCL : C ≤ 3 + L) (hL0 : 0 ≤ L)
    (hq : q = d / (d - 1)) (hsA : s ≤ (2 * G + 2 * h * y + C + 3) * q)
    (hr : r ≤ s * l / d ^ 2 + C) : r ≤ 20 * (G / l + h * y / d + L + 1) := by
  subst hld
  subst hq
  have hd1 : 0 < d - 1 := by linarith
  have hd0 : 0 < d := by linarith
  have hl0 : 0 < d + 1 := by linarith
  have hdd : 0 < (d - 1) * d := mul_pos hd1 hd0
  have hst : s * (d + 1) / d ^ 2 ≤ (2 * G + 2 * h * y + C + 3) * ((d + 1) / ((d - 1) * d)) := by
    have h1 : s * (d + 1) / d ^ 2 ≤ (2 * G + 2 * h * y + C + 3) * (d / (d - 1)) * (d + 1) / d ^ 2 := by
      have e : (2 * G + 2 * h * y + C + 3) * (d / (d - 1)) * (d + 1) / d ^ 2 - s * (d + 1) / d ^ 2
          = ((2 * G + 2 * h * y + C + 3) * (d / (d - 1)) - s) * ((d + 1) / d ^ 2) := by ring
      have : 0 ≤ ((2 * G + 2 * h * y + C + 3) * (d / (d - 1)) - s) * ((d + 1) / d ^ 2) :=
        mul_nonneg (by linarith) (div_nonneg hl0.le (sq_nonneg d))
      linarith
    have h2 : (2 * G + 2 * h * y + C + 3) * (d / (d - 1)) * (d + 1) / d ^ 2
        = (2 * G + 2 * h * y + C + 3) * ((d + 1) / ((d - 1) * d)) := by
      have hd1' : d - 1 ≠ 0 := hd1.ne'
      have hd0' : d ≠ 0 := hd0.ne'
      field_simp
    linarith
  have ht0 : 0 ≤ (d + 1) / ((d - 1) * d) := div_nonneg hl0.le hdd.le
  have htc : (d + 1) / ((d - 1) * d) ≤ 3 / 2 := by
    have key : d + 1 ≤ 3 / 2 * ((d - 1) * d) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d - 2) (by linarith : (0:ℝ) ≤ 3 * d + 1)]
    exact (div_le_iff₀ hdd).mpr key
  have htG : (d + 1) / ((d - 1) * d) ≤ 10 / (d + 1) := by
    have key : (d + 1) * (d + 1) ≤ 10 * ((d - 1) * d) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d - 2) (by linarith : (0:ℝ) ≤ 9 * d + 6)]
    exact (div_le_div_iff₀ hdd hl0).mpr key
  have hth : (d + 1) / ((d - 1) * d) ≤ 3 / d := by
    have key : (d + 1) * d ≤ 3 * ((d - 1) * d) := by
      nlinarith [mul_nonneg hd0.le (by linarith : (0:ℝ) ≤ d - 2)]
    exact (div_le_div_iff₀ hdd hd0).mpr key
  have e1 : 2 * G * ((d + 1) / ((d - 1) * d)) ≤ 20 * (G / (d + 1)) := by
    calc 2 * G * ((d + 1) / ((d - 1) * d)) ≤ 2 * G * (10 / (d + 1)) :=
          mul_le_mul_of_nonneg_left htG (by linarith)
      _ = 20 * (G / (d + 1)) := by ring
  have hhy : 0 ≤ h * y := mul_nonneg hh0 hy0
  have e2 : 2 * h * y * ((d + 1) / ((d - 1) * d)) ≤ 20 * (h * y / d) := by
    have hq0 : 0 ≤ h * y / d := div_nonneg hhy hd0.le
    calc 2 * h * y * ((d + 1) / ((d - 1) * d)) = 2 * (h * y) * ((d + 1) / ((d - 1) * d)) := by ring
      _ ≤ 2 * (h * y) * (3 / d) := mul_le_mul_of_nonneg_left hth (by linarith)
      _ = 6 * (h * y / d) := by ring
      _ ≤ 20 * (h * y / d) := by linarith
  have e3 : (C + 3) * ((d + 1) / ((d - 1) * d)) ≤ (C + 3) * (3 / 2) :=
    mul_le_mul_of_nonneg_left htc (by linarith)
  have expand : (2 * G + 2 * h * y + C + 3) * ((d + 1) / ((d - 1) * d)) + C
      = 2 * G * ((d + 1) / ((d - 1) * d)) + 2 * h * y * ((d + 1) / ((d - 1) * d))
        + (C + 3) * ((d + 1) / ((d - 1) * d)) + C := by ring
  linarith

theorem remainder_bound_of_tsum : RrBound := by
  intro ℓ hℓ n _ H G h j cut s r hh hH hG hs hr
  have hL3 : (3:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hℓ
  have hb : (1:ℝ) < (ℓ:ℝ) := by linarith
  have hh1 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hlog0 : 0 ≤ Real.logb ℓ (2 * h + 1) := Real.logb_nonneg hb (by linarith)
  have hceil := Nat.ceil_lt_add_one (R := ℝ) (a := 1 + Real.logb ℓ (2 * h + 1)) (by linarith)
  have hlog3 : Real.logb ℓ 3 ≤ 1 := by
    rw [← Real.logb_self_eq_one hb]
    exact (Real.logb_le_logb hb (by norm_num) (by linarith)).mpr hL3
  have hlogmul : Real.logb ℓ (2 * h + 1) ≤ Real.logb ℓ 3 + Real.logb ℓ h := by
    rw [← Real.logb_mul (by norm_num) (by linarith)]
    exact (Real.logb_le_logb hb (by linarith) (by nlinarith)).mpr (by linarith)
  have hL0 : 0 ≤ Real.logb ℓ h := Real.logb_nonneg hb hh1
  have hC0 : (0:ℝ) ≤ (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) := Nat.cast_nonneg _
  have hCL : (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) ≤ 3 + Real.logb ℓ h := by linarith
  have hd2 : (2:ℝ) ≤ (ℓ:ℝ) - 1 := by linarith
  have hdpos : (0:ℝ) < (ℓ:ℝ) - 1 := by linarith
  have hx0 : (0:ℝ) ≤ 1 / ((ℓ:ℝ) - 1) := by positivity
  have hx1 : 1 / ((ℓ:ℝ) - 1) < 1 := by rw [div_lt_one hdpos]; linarith
  have hser := tsum_le_two_level (1 / ((ℓ:ℝ) - 1)) (2 * G) (2 * h)
    ((⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) + 3) j
    (fun a : ℕ => ((H (cut + ((a + 1 : ℕ) : ZMod n)) : ℝ) +
        (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) + 3) / ((ℓ : ℝ) - 1) ^ a)
    hx0 hx1 (by positivity) (fun a => by positivity)
    (fun a => by
      have h' : ((H (cut + ((a + 1 : ℕ) : ZMod n)) : ℝ)) ≤ 2 * h := by
        exact_mod_cast hH (cut + ((a + 1 : ℕ) : ZMod n))
      rw [one_div, inv_pow, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hdpos.le a))
    (fun a ha => by
      have h' : ((H (cut + ((a + 1 : ℕ) : ZMod n)) : ℝ)) ≤ 2 * G := by
        exact_mod_cast hG (a + 1) (by omega) (by omega)
      rw [one_div, inv_pow, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hdpos.le a))
  have hsA := hs.trans hser
  have hq : (1 - 1 / ((ℓ:ℝ) - 1))⁻¹ = ((ℓ:ℝ) - 1) / ((ℓ:ℝ) - 1 - 1) := by
    have hd0 : (ℓ:ℝ) - 1 ≠ 0 := by linarith
    have hd1 : (ℓ:ℝ) - 1 - 1 ≠ 0 := by linarith
    field_simp
  have hyd : (h:ℝ) / ((ℓ:ℝ) - 1) ^ (j + 1) =
      (h:ℝ) * (1 / ((ℓ:ℝ) - 1)) ^ j / ((ℓ:ℝ) - 1) := by
    have hd0 : (ℓ:ℝ) - 1 ≠ 0 := by linarith
    rw [pow_succ, one_div_pow]
    field_simp
  rw [hyd]
  have key := rr_arith (ℓ:ℝ) ((ℓ:ℝ) - 1) (G:ℝ) (h:ℝ) ((1 / ((ℓ:ℝ) - 1)) ^ j)
    (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) (Real.logb ℓ h) s r
    (1 - 1 / ((ℓ:ℝ) - 1))⁻¹ (by ring) hd2 (Nat.cast_nonneg _) (by linarith)
    (pow_nonneg hx0 j) hC0 hCL hL0 hq (by linarith) hr
  exact key

end Formalism.TruncatedSeriesCounting.WachCoordinates
end
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SaturationCriterion
section
namespace Formalism.TruncatedSeriesCounting.X

private theorem iter_nzd {A : Type} [CommRing A] (ℓ g : A)
    (h : ∀ a : A, ℓ * a ∈ Ideal.span {g} → a ∈ Ideal.span {g}) :
    ∀ (n : ℕ) (z : A), ℓ ^ n * z ∈ Ideal.span {g} → z ∈ Ideal.span {g} := by
  intro n
  induction n with
  | zero => intro z hz; simpa using hz
  | succ n ih =>
    intro z hz
    apply ih
    apply h
    have e : ℓ * (ℓ ^ n * z) = ℓ ^ (n + 1) * z := by ring
    rw [e]; exact hz

theorem saturation_criterion : SatA := by
  intro A _ _ ℓ f f' hf' hℓf hℓf' x k ⟨b, hb⟩ ⟨a, ha⟩
  have inj : Function.Injective (algebraMap A (FractionRing A)) := IsFractionRing.injective A (FractionRing A)
  have h1 : ℓ ^ k * b = f' * (f * a) := by
    apply inj
    rw [map_mul, map_pow, hb, map_mul (algebraMap A (FractionRing A)) f', ha]
    ring
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (iter_nzd ℓ f' hℓf' k b (by
    rw [h1]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f')))
  have hf'0 : algebraMap A (FractionRing A) f' ≠ 0 := (map_ne_zero_iff _ inj).mpr hf'
  have hx : x = algebraMap A (FractionRing A) c := by
    apply mul_left_cancel₀ hf'0
    rw [← hb, hc, map_mul]
  have h2 : ℓ ^ k * c = f * a := by
    apply inj
    rw [map_mul, map_pow, ← hx, ha]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (iter_nzd ℓ f hℓf k c (by
    rw [h2]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))
  exact ⟨d, by rw [hx, hd]⟩

end Formalism.TruncatedSeriesCounting.X
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ThmEExp
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

private lemma sigma_exponent_le_real (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (g h j : ℕ) (hj : 1 ≤ j) :
    (sigE ℓ g h j : ℝ) ≤
      3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) + 9 / 4 * g + 11 / 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hjm : m + 1 - 1 = m := by omega
  unfold sigE
  rw [hjm]
  have hL : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hq : (2 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
  have hq0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hq2 : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2 := by positivity
  have hg0 : (0 : ℝ) ≤ g := by positivity
  have hA0 : (0 : ℝ) ≤ (h : ℝ) + 2 * g := by positivity
  have hP1 : (1 : ℝ) ≤ (ℓ : ℝ) ^ m := one_le_pow₀ (by linarith)
  have hPq : ((ℓ : ℝ) - 1) ^ m ≤ (ℓ : ℝ) ^ m := pow_le_pow_left₀ hq0.le (by linarith) m
  have hP0 : (0 : ℝ) < (ℓ : ℝ) ^ m := by linarith
  have hM : (Mpar ℓ g h : ℝ) ≤ ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) + 1 := by
    unfold Mpar
    push_cast
    have hc : (((ℓ - 1 : ℕ)) : ℝ) = (ℓ : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    have := Nat.cast_div_le (α := ℝ) (m := h + 2 * g) (n := ℓ - 1)
    rw [hc] at this
    push_cast at this
    linarith
  have hM0 : (0 : ℝ) ≤ (Mpar ℓ g h : ℝ) := by positivity
  have hr : (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2 ≤ 3 / 4 := by
    rw [div_le_iff₀ hq2]
    nlinarith
  have hr0 : (0 : ℝ) ≤ (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2 := by positivity
  have hX0 : (0 : ℝ) ≤ ((3 * g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ m) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 1 := by
    positivity
  have hceil := Nat.ceil_lt_add_one hX0
  have e1 : ((3 * g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ m) * ℓ / ((ℓ : ℝ) - 1) ^ 2 =
      3 * g * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) +
        (Mpar ℓ g h : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m := by
    field_simp
  have t1 : 3 * g * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) ≤ 9 / 4 * g := by nlinarith
  have t2 : (Mpar ℓ g h : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m ≤
      3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (m + 1 + 1) + 3 / 4 := by
    have hB : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ (m + 1 + 1) := by positivity
    have s1 : (Mpar ℓ g h : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m ≤
        (((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) + 1) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m := by
      gcongr
    have s2 : (((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) + 1) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m =
        ((h : ℝ) + 2 * g) * ℓ / (((ℓ : ℝ) - 1) ^ 3 * (ℓ : ℝ) ^ m) +
          ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m := by
      field_simp
    have s3 : ((h : ℝ) + 2 * g) * ℓ / (((ℓ : ℝ) - 1) ^ 3 * (ℓ : ℝ) ^ m) ≤
        3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (m + 1 + 1) := by
      rw [div_le_div_iff₀ (by positivity) hB]
      have k1 : (ℓ : ℝ) * ((ℓ : ℝ) - 1) ^ m ≤ 3 / 2 * ((ℓ : ℝ) - 1) * (ℓ : ℝ) ^ m := by
        have : (ℓ : ℝ) ≤ 3 / 2 * ((ℓ : ℝ) - 1) := by linarith
        calc (ℓ : ℝ) * ((ℓ : ℝ) - 1) ^ m ≤ 3 / 2 * ((ℓ : ℝ) - 1) * ((ℓ : ℝ) - 1) ^ m :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ ≤ 3 / 2 * ((ℓ : ℝ) - 1) * (ℓ : ℝ) ^ m :=
              mul_le_mul_of_nonneg_left hPq (by positivity)
      have k2 := mul_le_mul_of_nonneg_left k1 (mul_nonneg hA0 hq2.le)
      have e2 : ((ℓ : ℝ) - 1) ^ (m + 1 + 1) = ((ℓ : ℝ) - 1) ^ m * ((ℓ : ℝ) - 1) ^ 2 := by ring
      rw [e2]
      nlinarith [k2]
    have s4 : ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m ≤ 3 / 4 := by
      rw [div_le_iff₀ hP0]
      nlinarith
    linarith
  rw [e1] at hceil ⊢
  linarith

theorem total_exponent_le_eight_hundred : ExponentBoundOfRankAndKappaBounds := by
  intro ℓ hℓ G g h j ell rr kap hj hG hg hgh hell hrr hkap
  have hσ := sigma_exponent_le_real ℓ hℓ g h j hj
  unfold eE a0E
  have hL : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hq : (2 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
  have hB4 : (4 : ℝ) ≤ ((ℓ : ℝ) - 1) ^ (j + 1) := by
    have := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (ℓ : ℝ) - 1) (by omega : 2 ≤ j + 1)
    nlinarith
  have hB0 : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ (j + 1) := by linarith
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hGg : (G : ℝ) ≤ g := by exact_mod_cast hG
  have hgh' : (g : ℝ) ≤ h := by exact_mod_cast hgh
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hell1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hT : (0 : ℝ) ≤ (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) := by positivity
  have hΛ : (0 : ℝ) ≤ Real.logb ℓ h := Real.logb_nonneg (by linarith) hh1
  have hlog2 : Real.logb ℓ (2 * h) = Real.logb ℓ 2 + Real.logb ℓ h :=
    Real.logb_mul (by norm_num) (by positivity)
  have hl2 : Real.logb ℓ 2 ≤ 1 := by
    have := Real.logb_le_logb_of_le (by linarith : (1 : ℝ) < ℓ) (by norm_num : (0 : ℝ) < 2)
      (by linarith : (2 : ℝ) ≤ ℓ)
    rwa [Real.logb_self_eq_one (by linarith)] at this
  have hGL : (G : ℝ) / ℓ ≤ g / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hgB : (g : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) ≤ g / 4 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hB4
  have h4g : 4 * (g : ℝ) / ((ℓ : ℝ) - 1) ≤ 2 * g := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have eσ : 3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) =
      3 / 2 * ((h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1)) + 3 * ((g : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1)) := by
    ring
  rw [eσ] at hσ
  rw [hlog2] at hkap
  have hge : (g : ℝ) ≤ g * ell := by nlinarith
  have hee : (ell : ℝ) ≤ g * ell := by nlinarith
  have h1e : (1 : ℝ) ≤ g * ell := by nlinarith
  nlinarith

end Formalism.TruncatedSeriesCounting.WachCoordinates
end
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.TruncSig
section
namespace Formalism.TruncatedSeriesCounting.X

theorem truncation_signature_bound : TruncSig := by
  unfold TruncSig
  intro ℓ hℓ y X M η
  have hl : (3 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have ha : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hlpos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hy : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  have gen : ∀ T : ℝ, 0 ≤ T → (y : ℝ) * ℓ / (ℓ - 1) - max 0 ((ℓ : ℝ) * y - T) ≤ T / (ℓ - 1) := by
    intro T hT
    rw [sub_le_iff_le_add, div_le_iff₀ ha, add_mul, div_mul_cancel₀ _ (ne_of_gt ha)]
    rcases le_total ((ℓ : ℝ) * y - T) 0 with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]
      nlinarith [mul_nonneg h (by linarith : (0 : ℝ) ≤ (ℓ : ℝ) - 2)]
  have mono : ∀ T : ℝ, T / ((ℓ : ℝ) - 1) ≤ (T + 1) / ((ℓ : ℝ) - 1) + 1 := by
    intro T
    have h1 : 0 ≤ 1 / ((ℓ : ℝ) - 1) := by positivity
    rw [add_div]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · exact (gen X (Nat.cast_nonneg _)).trans (mono _)
  · have e : (ℓ : ℝ) * y - η - M = (ℓ : ℝ) * y - (η + M) := by ring
    rw [e]
    have := gen ((η : ℝ) + M) (by positivity)
    have h2 : ((η : ℝ) + M) / (ℓ - 1) ≤ ((M : ℝ) + η) / (ℓ - 1) + 1 := by
      rw [add_comm (η : ℝ)]
      have h3 : 0 ≤ 1 / ((ℓ : ℝ) - 1) := by positivity
      linarith
    linarith
  · have hsq : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2 := pow_pos ha 2
    have e : (y : ℝ) * ℓ / (ℓ - 1) = (y : ℝ) * ℓ * (ℓ - 1) / (ℓ - 1) ^ 2 := by
      field_simp
    have key : (y : ℝ) * ℓ / (ℓ - 1) - max 0 (((ℓ : ℝ) - 1) * y - X / ℓ) ≤ X / (ℓ - 1) ^ 2 := by
      rw [e, sub_le_iff_le_add, div_le_iff₀ hsq, add_mul, div_mul_cancel₀ _ (ne_of_gt hsq)]
      have hX : (X : ℝ) = X / ℓ * ℓ := (div_mul_cancel₀ _ hlpos.ne').symm
      rcases le_total (((ℓ : ℝ) - 1) * y - X / ℓ) 0 with h | h
      · rw [max_eq_left h]
        have h4 : ((ℓ : ℝ) - 1) * y * ℓ ≤ X := by
          have h5 : ((ℓ : ℝ) - 1) * y ≤ X / ℓ := by linarith
          have := mul_le_mul_of_nonneg_right h5 hlpos.le
          linarith
        nlinarith
      · rw [max_eq_right h]
        have hs2 : (0 : ℝ) ≤ ((ℓ : ℝ) - 1) ^ 2 - ℓ := by nlinarith
        nlinarith [mul_nonneg h hs2]
    have h6 : (0 : ℝ) ≤ 1 := zero_le_one
    linarith

end Formalism.TruncatedSeriesCounting.X
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.TruncationRemainderBound
section
namespace Formalism.TruncatedSeriesCounting.X

theorem truncation_remainder_bound : TruncRem1 := by
  intro R _ ℓ hℓ π₀ y K c hc
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy
    have hc0 : c = 0 := by push_cast at hc; omega
    subst hc0
    rw [pow_zero]
    exact Ideal.subset_span (Set.mem_insert _ _) |> fun h => by simpa using h
  · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    have e : (π₀ * (π₀ + (ℓ : R)) ^ (ℓ - 1)) ^ (y' + 1) =
        π₀ * ((π₀ + (ℓ : R)) + (-(ℓ : R))) ^ y' * (π₀ + (ℓ : R)) ^ ((ℓ - 1) * (y' + 1)) := by
      rw [show (π₀ + (ℓ : R)) + (-(ℓ : R)) = π₀ by ring, mul_pow, ← pow_mul, pow_succ]
      ring
    rw [e, add_pow (π₀ + (ℓ : R)) (-(ℓ : R)) y', Finset.mul_sum, Finset.sum_mul]
    refine Ideal.sum_mem _ fun m hm => ?_
    have hm' : m ≤ y' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    by_cases hj : c ≤ y' - m
    · have h1 : (-(ℓ : R)) ^ (y' - m) = (ℓ : R) ^ c * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c)) := by
        have hsplit : (ℓ : R) ^ (y' - m) = (ℓ : R) ^ c * (ℓ : R) ^ (y' - m - c) := by
          rw [← pow_add]
          congr 1
          omega
        rw [neg_pow, hsplit]
        ring
      have hmem : (ℓ : R) ^ c ∈ Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K} :=
        Ideal.subset_span (Set.mem_insert _ _)
      rw [h1]
      have : π₀ * ((π₀ + ↑ℓ) ^ m * ((ℓ : R) ^ c * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c))) * ↑(y'.choose m)) *
          (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)) = (ℓ : R) ^ c * (π₀ * (π₀ + ↑ℓ) ^ m * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c)) *
          ↑(y'.choose m) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1))) := by ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hmem
    · have hK : K ≤ m + (ℓ - 1) * (y' + 1) := by
        push_neg at hj
        have h2 : (c : ℤ) ≤ (ℓ : ℤ) * ((y' + 1 : ℕ) : ℤ) - K := hc
        push_cast at h2
        have h3 : (c : ℤ) ≥ (y' : ℤ) - m + 1 := by omega
        zify [hℓ]
        nlinarith [h2, h3]
      have hmem : π₀ * (π₀ + (ℓ : R)) ^ K ∈ Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      have : π₀ * ((π₀ + ↑ℓ) ^ m * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m)) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)) =
          π₀ * (π₀ + (ℓ : R)) ^ K * ((π₀ + ↑ℓ) ^ (m + (ℓ - 1) * (y' + 1) - K) * (-(ℓ : R)) ^ (y' - m) *
            ↑(y'.choose m)) := by
        have e2 : (π₀ + (ℓ : R)) ^ K * (π₀ + (ℓ : R)) ^ (m + (ℓ - 1) * (y' + 1) - K) =
            (π₀ + (ℓ : R)) ^ m * (π₀ + (ℓ : R)) ^ ((ℓ - 1) * (y' + 1)) := by
          rw [← pow_add, ← pow_add, Nat.add_sub_cancel' hK]
        linear_combination (π₀ * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m)) * e2.symm
      rw [this]
      exact Ideal.mul_mem_right _ _ hmem

end Formalism.TruncatedSeriesCounting.X
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.UnitCoefficientPowerMod
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.X

open PowerSeries

theorem unit_coefficient_power_mod : UnitCoefficientPowerMod := by
  intro O _ ℓ ε u y
  have hsplit : ∃ W : PowerSeries O,
      (Formalism.WindowSums.p1 ℓ ε u) ^ y = (u * X ^ ℓ) ^ y + C (ℓ : O) * W := by
    obtain ⟨V, hV⟩ := sub_dvd_pow_sub_pow (Formalism.WindowSums.p1 ℓ ε u) (u * X ^ ℓ) y
    refine ⟨ε * V, ?_⟩
    have : Formalism.WindowSums.p1 ℓ ε u - u * X ^ ℓ = C (ℓ : O) * ε := by unfold Formalism.WindowSums.p1; ring
    rw [this] at hV
    linear_combination hV
  obtain ⟨W, hW⟩ := hsplit
  have hc : coeff (ℓ * y) ((Formalism.WindowSums.p1 ℓ ε u) ^ y) =
      constantCoeff u ^ y + (ℓ : O) * coeff (ℓ * y) W := by
    rw [hW, map_add, coeff_C_mul, mul_pow, ← pow_mul, mul_comm ℓ y]
    have := coeff_mul_X_pow (u ^ y) (y * ℓ) 0
    rw [zero_add] at this
    rw [this, coeff_zero_eq_constantCoeff, map_pow]
  refine ⟨?_, ?_⟩
  · rw [hc, add_sub_cancel_left, Ideal.mem_span_singleton]; exact dvd_mul_right _ _
  · intro hloc hℓ hu
    rw [hc]
    have h0 : IsUnit (constantCoeff u ^ y) := (hu.map constantCoeff).pow y
    have h1 : (ℓ : O) * coeff (ℓ * y) W ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hℓ)
    by_contra hne
    have h2 : constantCoeff u ^ y + (ℓ : O) * coeff (ℓ * y) W ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr hne
    have h3 := Ideal.sub_mem _ h2 h1
    rw [add_sub_cancel_right] at h3
    exact ((IsLocalRing.mem_maximalIdeal _).mp h3) h0

end Formalism.TruncatedSeriesCounting.X
end
end

