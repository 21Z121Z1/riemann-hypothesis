import Formalism.PolynomialDimension.EdgeSumGoodRank
import Mathlib
import Formalism.PolynomialDimension.Bundle0002
import Formalism.PolynomialDimension.MultinomialDepth.Bundle0003

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.DvdPowOfNotPowSuccDvd
section
noncomputable section

open scoped BigOperators TensorProduct
open Finset

namespace Formalism.CountingSumsFrames

theorem one_sub_sum_mul_prod_le_prod {ι : Type} (s : Finset ι) (κ n d : ι → ℝ) (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1)
    (hd : ∀ j, 0 ≤ d j) (h : ∀ j, (1 - κ j) * d j ≤ n j) :
    (1 - ∑ j ∈ s, κ j) * ∏ j ∈ s, d j ≤ ∏ j ∈ s, n j := by
  classical
  have hP : ∀ t : Finset ι, 1 - ∑ j ∈ t, κ j ≤ ∏ j ∈ t, (1 - κ j) := by
    intro t
    refine Finset.induction_on t (by simp) ?_
    intro i t hi ih
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have h1 : 0 ≤ 1 - κ i := by linarith [(hκ i).2]
    have h2 : 0 ≤ ∑ j ∈ t, κ j := Finset.sum_nonneg fun j _ => (hκ j).1
    have h3 := mul_le_mul_of_nonneg_left ih h1
    nlinarith [mul_nonneg (hκ i).1 h2]
  have hd0 : 0 ≤ ∏ j ∈ s, d j := Finset.prod_nonneg fun j _ => hd j
  calc (1 - ∑ j ∈ s, κ j) * ∏ j ∈ s, d j ≤ (∏ j ∈ s, (1 - κ j)) * ∏ j ∈ s, d j :=
        mul_le_mul_of_nonneg_right (hP s) hd0
    _ = ∏ j ∈ s, ((1 - κ j) * d j) := Finset.prod_mul_distrib.symm
    _ ≤ ∏ j ∈ s, n j := Finset.prod_le_prod
        (fun j _ => mul_nonneg (by linarith [(hκ j).2]) (hd j)) (fun j _ => h j)

theorem share_product_bound : ShareProd := by
  intro J κ n d hκ h
  push_cast
  exact one_sub_sum_mul_prod_le_prod Finset.univ κ (fun j => (n j : ℝ)) (fun j => (d j : ℝ)) hκ (fun j => Nat.cast_nonneg _) h

section Partner

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end Partner

end Formalism.CountingSumsFrames
end
end

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.IntervalCleanDepthBound
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

namespace IntervalBounds

open ParamsIProof

theorem basics (C C₀ : ℝ) (p N N₁ J k n' G' : ℕ) (Y Yb a b' Ib cl D cStar : ℝ)
    (hC : 1 ≤ C) (hC₀ : 1 ≤ C₀) (h : PolynomialDimensionIntervalConditions C C₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar) :
    (1 : ℝ) ≤ N ∧ (1 : ℝ) ≤ N₁ ∧ (5 : ℝ) ≤ k ∧ (1 : ℝ) ≤ J ∧ (J : ℝ) ≤ N ∧ (25 : ℝ) ≤ p ∧
    1 ≤ (p : ℝ) ^ G' ∧ 0 < a ∧ 1 ≤ Real.log a ∧ 1 ≤ Real.logb p a ∧ 0 ≤ logBaseP p a k ∧
    logBaseP p a k ≤ 3 * Real.logb p a ∧ 1 ≤ logScale C₀ N₁ a ∧ (N : ℝ) ≤ k ∧ (N₁ : ℝ) ^ 2 ≤ k ∧
    0 ≤ D ∧ 1 ≤ b' := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
    g20, g21, g22, g23, g24⟩ := h
  unfold logScale at *
  have hC0 : 0 < C := by linarith
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast g4
  have hN1 : (1 : ℝ) ≤ N₁ := by exact_mod_cast g5
  have hkn : 2 * N₁ + 3 ≤ k := by omega
  have hk : (2 : ℝ) * N₁ + 3 ≤ k := by exact_mod_cast hkn
  have hk5 : (5 : ℝ) ≤ k := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast g7
  have hJN : (J : ℝ) ≤ N := by exact_mod_cast g8
  have hY0 : 0 < Y := by linarith
  have hk2 : (25 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk5]
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ g2
  have hkp : (k : ℝ) ^ 2 ≤ p := le_trans (le_mul_of_one_le_right (by positivity) hY2) g3
  have hp25 : (25 : ℝ) ≤ p := by linarith
  have hp1 : (1 : ℝ) < p := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hQ : 1 ≤ (p : ℝ) ^ G' := one_le_pow₀ hp1.le
  have hab : (p : ℝ) * b' < a := (lt_div_iff₀ g17).mp g18
  have ha0 : 0 < a := lt_trans (by positivity) hab
  have hNY : 1 ≤ (N : ℝ) * Y := one_le_mul_of_one_le_of_one_le hN g2
  have hCN : 1 ≤ C₀ * (N₁ : ℝ) ^ 2 :=
    one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hN1)
  have hLa0 : 0 ≤ C₀ * (N₁ : ℝ) ^ 2 * Real.log a := by
    have := Real.log_nonneg hNY
    linarith
  have hL0 : 0 ≤ Real.log a := by
    by_contra hneg
    rw [not_le] at hneg
    have : C₀ * (N₁ : ℝ) ^ 2 * Real.log a < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
    linarith
  have ha1 : 1 ≤ a := (Real.log_nonneg_iff ha0).mp hL0
  have hl0 : 0 ≤ Real.logb p a := Real.logb_nonneg hp1 ha1
  have hD0 : 0 ≤ D := le_trans (by positivity) g22
  have hcS : 8 ≤ cStar := by linarith
  have hNcl : 0 ≤ (N : ℝ) * cl := by positivity
  have hncl : 0 ≤ (n' : ℝ) * cl := by positivity
  have hX : 8 ≤ cStar + N * cl + n' * cl := by linarith
  have hk3 : 1 ≤ (k : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hQ4 : 1 ≤ ((p : ℝ) ^ G') ^ 4 := one_le_pow₀ hQ
  have hb1 : 1 ≤ b' := le_trans
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hk3) hN) hQ4)
      (by linarith)) g2) g24
  have hpa : (p : ℝ) ≤ a := le_trans (le_mul_of_one_le_right hp0.le hb1) hab.le
  have hL1 : 1 ≤ Real.log a := one_le_log_of_three_le a (by linarith)
  have hl1 : 1 ≤ Real.logb p a := by
    rw [← Real.logb_self_eq_one hp1]
    exact (Real.logb_le_logb hp1 hp0 ha0).mpr hpa
  have hka : (k : ℝ) ≤ a := by
    have : (k : ℝ) ≤ (k : ℝ) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have hlg0 : 0 ≤ logBaseP p a k := by
    unfold logBaseP
    have := Real.logb_nonneg hp1 (show 1 ≤ 8 * a + k by linarith)
    linarith
  have hlg : logBaseP p a k ≤ 3 * Real.logb p a := by
    unfold logBaseP
    have hh : Real.logb p (8 * a + k) ≤ Real.logb p (p * a) :=
      (Real.logb_le_logb hp1 (by linarith) (by positivity)).mpr (by
        have : 25 * a ≤ p * a := mul_le_mul_of_nonneg_right hp25 ha0.le
        linarith)
    rw [Real.logb_mul hp0.ne' ha0.ne', Real.logb_self_eq_one hp1] at hh
    linarith
  have hLaN : (N₁ : ℝ) ^ 2 ≤ C₀ * (N₁ : ℝ) ^ 2 * Real.log a := by
    have h3 : 1 ≤ C₀ * Real.log a := one_le_mul_of_one_le_of_one_le hC₀ hL1
    have := le_mul_of_one_le_right (by positivity : (0:ℝ) ≤ (N₁ : ℝ) ^ 2) h3
    linarith
  have hLa1 : 1 ≤ C₀ * (N₁ : ℝ) ^ 2 * Real.log a := one_le_mul_of_one_le_of_one_le hCN hL1
  generalize C₀ * (N₁ : ℝ) ^ 2 * Real.log a = La at *
  have hLa2 : 1 ≤ La ^ 2 := one_le_pow₀ hLa1
  have hNk : (N : ℝ) ≤ k := by
    have h3 : 1 ≤ C * La ^ 2 := one_le_mul_of_one_le_of_one_le hC hLa2
    have := le_mul_of_one_le_right (by linarith : (0:ℝ) ≤ N) h3
    linarith
  have sq_level_le_degree : (N₁ : ℝ) ^ 2 ≤ k := by
    have h3 : 1 ≤ C * N * La := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hC hN) hLa1
    have := le_mul_of_one_le_right (by linarith : (0:ℝ) ≤ La) h3
    linarith
  exact ⟨hN, hN1, hk5, hJ1, hJN, hp25, hQ, ha0, hL1, hl1, hlg0, hlg, hLa1, hNk, sq_level_le_degree, hD0, hb1⟩

theorem log_size_bound_le (k lg kap1 : ℝ) (hk : 1 ≤ k) (hlg : 0 ≤ lg) (h : kap1 ≤ (k - 1) ^ 2 * lg) :
    kap1 ≤ k ^ 2 * lg := by
  have h1 : (k - 1) ^ 2 ≤ k ^ 2 := by nlinarith
  exact le_trans h (mul_le_mul_of_nonneg_right h1 hlg)

theorem sum_shift {ι : Type} (T : Finset ι) (f g : ι → ℝ) (e Nr : ℝ) (he : 0 ≤ e)
    (hT : (T.card : ℝ) ≤ Nr) (h : ∀ y ∈ T, f y ≤ g y + e) :
    ∑ y ∈ T, f y ≤ ∑ y ∈ T, g y + Nr * e := by
  calc ∑ y ∈ T, f y ≤ ∑ y ∈ T, (g y + e) := Finset.sum_le_sum h
    _ = ∑ y ∈ T, g y + T.card * e := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ y ∈ T, g y + Nr * e := by
        have := mul_le_mul_of_nonneg_right hT he
        linarith

end IntervalBounds

open ParamsIProof IntervalBounds

theorem interval_kappa_bound : KapI := by
  intro CW C1 hCW hC1
  refine ⟨3 * C1 + 1000 * CW + 1002, by linarith, ?_⟩
  intro C₀ hC₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar h mH mHp hmH hmHp
  obtain ⟨hN, hN1, hk5, hJ1, hJN, hp25, hQ, ha0, hL1, hl1, hlg0, hlg, hLa1, hNk, sq_level_le_degree, hD0, hb1⟩ :=
    basics _ C₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar (by linarith) hC₀ h
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
    g20, g21, g22, g23, g24⟩ := h
  generalize hCdef : 3 * C1 + 1000 * CW + 1002 = C at *
  have hC0 : 0 < C := by linarith
  have hY0 : 0 < Y := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hNcl : 0 ≤ (N : ℝ) * cl := by positivity
  have hncl : 0 ≤ (n' : ℝ) * cl := by positivity
  have hQ4 : 1 ≤ ((p : ℝ) ^ G') ^ 4 := one_le_pow₀ hQ
  have hM : C * (k : ℝ) ^ 3 * Y * (N * cl) ≤ b' := by
    have e1 : C * (k : ℝ) ^ 3 * Y * (N * cl) ≤ C * (k : ℝ) ^ 3 * Y * (cStar + N * cl + n' * cl) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e2 : C * (k : ℝ) ^ 3 * Y * (cStar + N * cl + n' * cl) ≤
        C * (k : ℝ) ^ 3 * Y * (cStar + N * cl + n' * cl) * (N * ((p : ℝ) ^ G') ^ 4) :=
      le_mul_of_one_le_right (mul_nonneg (by positivity) (by linarith))
        (one_le_mul_of_one_le_of_one_le hN hQ4)
    linarith
  have hsh := share C k Y (N * cl) a b' Ib Yb N (logScale C₀ N₁ a) (Real.log a) (by linarith)
    (by linarith) g2 hNcl hM g17 (by linarith) hN hLa1 hL1 g16 g12
  have hcn := cnkc C (CW + 1) k Y N cl b' (by linarith) (by linarith) (by linarith) g2
    (by linarith) g20 g17 hM
  have hcn2 : CW * N * k * (2 * cl) / b' ≤ (CW + 1) * N * k * (2 * cl) / b' := by
    apply div_le_div_of_nonneg_right _ g17.le
    have : 0 ≤ (N : ℝ) * k * (2 * cl) := by positivity
    linarith
  have hinv : 1 / (a / ((k : ℝ) * Y)) = k * Y / a := one_div_div _ _
  rw [hinv]
  have hNN : 1 ≤ (N : ℝ) * N₁ := one_le_mul_of_one_le_of_one_le hN hN1
  have hY1 : 1 / Y ≤ (N : ℝ) * N₁ / Y := div_le_div_of_nonneg_right hNN hY0.le
  have hZ : 0 ≤ (N : ℝ) * N₁ / Y := by positivity
  have e1 : C1 * N * N₁ / Y = C1 * ((N : ℝ) * N₁ / Y) := by ring
  have e2 : C * N * N₁ / Y = C * ((N : ℝ) * N₁ / Y) := by ring
  have e3 : (3 * C1 + 2) * ((N : ℝ) * N₁ / Y) ≤ C * ((N : ℝ) * N₁ / Y) :=
    mul_le_mul_of_nonneg_right (by linarith) hZ
  rw [e1] at hmH hmHp
  rw [e2]
  linarith

end Formalism.CountingSumsFrames
end
end

-- bundled from Formalism.PolynomialDimension.MultinomialDepth.IntervalRoomBound
section
noncomputable section

namespace Formalism.CountingSumsFrames

open Real

namespace RoomIProof

theorem core (C Cm N1 k Q c La b' Ib X Nr Y Yb : ℝ)
    (hCm : 0 ≤ Cm) (hC : 192 + 32 * Cm ≤ C) (hN1 : 1 ≤ N1) (hk : 1 ≤ k) (hQ : 1 ≤ Q)
    (hLa : N1 ^ 2 ≤ La) (hYb : C ≤ Yb) (hb : 0 < b') (hc0 : 0 ≤ c) (hc : c ≤ 4 * X) (hX : 0 ≤ X)
    (hN : 1 ≤ Nr) (hY : 1 ≤ Y) (hb' : C * k ^ 3 * Nr * Q ^ 4 * X * Y ≤ b')
    (hIb : Yb * Nr * La * b' / k ≤ Ib) :
    12 * c + (N1 + 1) * (Cm * k * N1 * Q * c) ≤ (2 * Ib / b') * (b' / (2 * Q)) / 4 := by
  have hQ0 : 0 < Q := by linarith
  have hk0 : 0 < k := by linarith
  have hC1 : 1 ≤ C := by linarith
  have hN10 : 0 < N1 := by linarith
  have hR : (2 * Ib / b') * (b' / (2 * Q)) / 4 = Ib / (4 * Q) := by
    field_simp
  rw [hR, le_div_iff₀ (by positivity)]

  have hW : 1 ≤ k * N1 ^ 2 * Q :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hk (one_le_pow₀ hN1)) hQ
  have a1 : 12 * c ≤ 12 * c * (k * N1 ^ 2 * Q) := le_mul_of_one_le_right (by linarith) hW
  have a2 : (N1 + 1) * (Cm * k * N1 * Q * c) ≤ (2 * N1) * (Cm * k * N1 * Q * c) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have a3 : (12 + 2 * Cm) * (k * N1 ^ 2 * Q) * c ≤ (12 + 2 * Cm) * (k * N1 ^ 2 * Q) * (4 * X) :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  have hL : 12 * c + (N1 + 1) * (Cm * k * N1 * Q * c) ≤ (48 + 8 * Cm) * (k * N1 ^ 2 * Q * X) := by
    linarith
  have hV : 0 ≤ k * N1 ^ 2 * Q ^ 2 * X := by positivity
  have hL2 : (12 * c + (N1 + 1) * (Cm * k * N1 * Q * c)) * (4 * Q) ≤ C * (k * N1 ^ 2 * Q ^ 2 * X) := by
    have b1 := mul_le_mul_of_nonneg_right hL (by positivity : 0 ≤ 4 * Q)
    have b2 := mul_le_mul_of_nonneg_right hC hV
    linarith

  have hq4 : Q ^ 2 ≤ Q ^ 4 := pow_le_pow_right₀ hQ (by norm_num)
  have hq : Q ^ 2 ≤ Nr * Q ^ 4 * Y := by
    have h2 : Q ^ 4 ≤ Nr * Q ^ 4 := le_mul_of_one_le_left (by positivity) hN
    have h3 : Nr * Q ^ 4 ≤ Nr * Q ^ 4 * Y := le_mul_of_one_le_right (by positivity) hY
    linarith
  have hb2 : C * k ^ 3 * Q ^ 2 * X ≤ b' := by
    have h4 : C * k ^ 3 * Q ^ 2 * X ≤ C * k ^ 3 * (Nr * Q ^ 4 * Y) * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by positivity)) hX
    linarith
  have hIb' : Yb * Nr * La * b' ≤ Ib * k := (div_le_iff₀ hk0).mp hIb
  have hYN : 1 ≤ Yb * Nr := one_le_mul_of_one_le_of_one_le (by linarith) hN
  have hLa0 : 0 ≤ La := le_trans (by positivity) hLa
  have c1 : N1 ^ 2 * b' ≤ Yb * Nr * La * b' := by
    have d1 : N1 ^ 2 * b' ≤ La * b' := mul_le_mul_of_nonneg_right hLa hb.le
    have d2 : La * b' ≤ (Yb * Nr) * (La * b') := le_mul_of_one_le_left (by positivity) hYN
    linarith
  have c2 : N1 ^ 2 * (C * k ^ 3 * Q ^ 2 * X) ≤ N1 ^ 2 * b' := mul_le_mul_of_nonneg_left hb2 (by positivity)
  have c3 : C * (k * N1 ^ 2 * Q ^ 2 * X) * k ≤ C * (k * N1 ^ 2 * Q ^ 2 * X) * k * k :=
    le_mul_of_one_le_right (by positivity) hk
  have c4 : C * (k * N1 ^ 2 * Q ^ 2 * X) * k ≤ Ib * k := by linarith
  have c5 : C * (k * N1 ^ 2 * Q ^ 2 * X) ≤ Ib := le_of_mul_le_mul_right c4 hk0
  linarith

end RoomIProof

end Formalism.CountingSumsFrames
end
end

