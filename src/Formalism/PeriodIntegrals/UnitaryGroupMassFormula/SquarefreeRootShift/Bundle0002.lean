import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootShift.Bundle0001

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootShift.ArithP
section
open Finset

noncomputable section

namespace PI.SqfRootShift.W

theorem geom_part (G : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    ∑ k ∈ Finset.Ioc 1 r, (G - 1) * G ^ (r - k) = G ^ (r - 1) - 1 := by
  induction r, hr using Nat.le_induction with
  | base => simp
  | succ r hr ih =>
    rw [Finset.sum_Ioc_succ_top (by omega : 1 ≤ r), Nat.sub_self, pow_zero, mul_one]
    have h : ∑ k ∈ Finset.Ioc 1 r, (G - 1) * G ^ (r + 1 - k) =
        G * ∑ k ∈ Finset.Ioc 1 r, (G - 1) * G ^ (r - k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Ioc] at hk
      rw [show r + 1 - k = (r - k) + 1 by omega, pow_succ]; ring
    rw [h, ih, show r + 1 - 1 = (r - 1) + 1 by omega, pow_succ]; ring

theorem harm_tail (r : ℕ) (hr : 1 ≤ r) : ∑ k ∈ Finset.Ioc 1 r, ((k : ℝ))⁻¹ ≤ Real.log r := by
  have h := harmonic_le_one_add_log r
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  rw [← Finset.add_sum_erase _ _ (Finset.left_mem_Icc.mpr hr), Finset.Icc_erase_left,
    Nat.cast_one, inv_one] at h
  linarith

theorem arithP : ArithP := by
  intro g r q d e hg hq hd hq8 hd16 he hq16 hd16' hgm hr hg12
  have hL : 4 * 2 ^ e * q * d ∣ g - 1 := by
    have := Nat.dvd_sub_mod (n := 4 * 2 ^ e * q * d) g
    rwa [hgm] at this
  have h16L : 16 ∣ 4 * 2 ^ e * q * d := by
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
    exact ⟨2 ^ e' * q * d, by ring⟩
  have h16 : 16 ∣ g - 1 := h16L.trans hL
  have hqg : q ∣ g - 1 := (Dvd.intro (4 * 2 ^ e * d) (by ring)).trans hL
  have hdg : d ∣ g - 1 := (Dvd.intro_left (4 * 2 ^ e * q) rfl).trans hL
  have h4 : 4 ∣ g - 1 := (by norm_num : 4 ∣ 16).trans h16
  have hqd : q ≠ d := by omega
  have hg4096 : 4096 ≤ g := by simpa using hg12
  have hg2 : 2 ≤ g := by omega
  have hA1 := arith1 (n := g - 1) (by omega) hq hd hqd hq16 hd16' h16 hqg hdg
  have hm16 : 16 ≤ min q d := le_min hq16 hd16'
  generalize min q d = m at hA1 hm16 ⊢
  set G : ℝ := (g : ℝ) with hGdef
  have hG : (4096 : ℝ) ≤ G := by rw [hGdef]; exact_mod_cast hg4096
  have hG0 : (0 : ℝ) < G := by linarith
  have hG1 : (0 : ℝ) < G - 1 := by linarith
  have hm : (16 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm16
  have hA1r : 4 * (m : ℝ) * (ppSum (g - 1) : ℝ) ≤ G - 1 := by
    have := (Nat.cast_le (α := ℝ)).mpr hA1
    push_cast [Nat.cast_sub (by omega : 1 ≤ g)] at this
    exact this
  have hP0 : (0 : ℝ) ≤ (ppSum (g - 1) : ℝ) := Nat.cast_nonneg _
  have hP : (ppSum (g - 1) : ℝ) ≤ G - 1 := by nlinarith
  have hA2r : ∀ k : ℕ, 1 ≤ k →
      (ppSum (g ^ k - 1) : ℝ) ≤ k * (ppSum (g - 1) : ℝ) + (G ^ k - 1) / (G - 1) := by
    intro k hk
    have h := arith2 hg2 h4 (k := k) (by omega)
    have hS : (((g ^ k - 1) / (g - 1) : ℕ) : ℝ) = (G ^ k - 1) / (G - 1) := by
      rw [eq_div_iff hG1.ne']
      have hdvd : g - 1 ∣ g ^ k - 1 := by simpa using Nat.sub_dvd_pow_sub_pow g 1 k
      have h1 := Nat.div_mul_cancel hdvd
      have hc := congrArg (fun x : ℕ => (x : ℝ)) h1
      have hgk : 1 ≤ g ^ k := Nat.one_le_pow _ _ (by omega)
      push_cast [Nat.cast_sub (by omega : 1 ≤ g), Nat.cast_sub hgk] at hc
      exact hc
    have hc := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at hc
    rw [hS] at hc
    exact hc
  have hterm : ∀ k ∈ Finset.Ioc 1 r, (ppSum (g ^ k - 1) : ℝ) / k * G ^ (r - k) ≤
      (G - 1) * G ^ (r - k) + G ^ r / (G - 1) * ((k : ℝ))⁻¹ := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hB : (0 : ℝ) ≤ G ^ (r - k) := pow_nonneg hG0.le _
    have h1 : (ppSum (g ^ k - 1) : ℝ) / k ≤ (ppSum (g - 1) : ℝ) + (G ^ k - 1) / (G - 1) / k := by
      rw [div_le_iff₀ hk0, add_mul, div_mul_cancel₀ _ hk0.ne']
      have := hA2r k (by omega)
      linarith
    have hAB : (G ^ k - 1) * G ^ (r - k) ≤ G ^ r := by
      have : G ^ k * G ^ (r - k) = G ^ r := by rw [← pow_add]; congr 1; omega
      nlinarith
    calc (ppSum (g ^ k - 1) : ℝ) / k * G ^ (r - k)
        ≤ ((ppSum (g - 1) : ℝ) + (G ^ k - 1) / (G - 1) / k) * G ^ (r - k) :=
          mul_le_mul_of_nonneg_right h1 hB
      _ = (ppSum (g - 1) : ℝ) * G ^ (r - k) + ((G ^ k - 1) * G ^ (r - k)) / (G - 1) * ((k : ℝ))⁻¹ := by
          ring
      _ ≤ (G - 1) * G ^ (r - k) + G ^ r / (G - 1) * ((k : ℝ))⁻¹ :=
          add_le_add (mul_le_mul_of_nonneg_right hP hB)
            (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hAB hG1.le) (by positivity))
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, geom_part G r (by omega), ← Finset.mul_sum] at hsum
  have hharm := harm_tail r (by omega)
  have hGr0 : (0 : ℝ) ≤ G ^ r / (G - 1) := div_nonneg (pow_nonneg hG0.le _) hG1.le
  have hh := mul_le_mul_of_nonneg_left hharm hGr0
  have hGr : G ^ r = G * G ^ (r - 1) := by rw [← pow_succ']; congr 1; omega
  have hgeo : G ^ (r - 1) - 1 ≤ G ^ r / (G - 1) := by
    rw [le_div_iff₀ hG1, hGr]
    nlinarith [pow_nonneg hG0.le (r - 1)]
  have t1 : (ppSum (g - 1) : ℝ) * G ^ (r - 1) ≤ G ^ r / (4 * (m : ℝ)) := by
    rw [le_div_iff₀ (by positivity), hGr]
    nlinarith [mul_le_mul_of_nonneg_right hA1r (pow_nonneg hG0.le (r - 1)),
      pow_nonneg hG0.le (r - 1)]
  rw [← Finset.add_sum_erase _ _ (Finset.left_mem_Icc.mpr (by omega : 1 ≤ r)),
    Finset.Icc_erase_left]
  simp only [pow_one, Nat.cast_one, div_one]
  have hR : (1 / (4 * (m : ℝ)) + (1 + Real.log r) / (G - 1)) * G ^ r =
      G ^ r / (4 * (m : ℝ)) + G ^ r / (G - 1) + G ^ r / (G - 1) * Real.log r := by ring
  rw [hR]
  linarith

end PI.SqfRootShift.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootShift.CountB
section
open Polynomial

noncomputable section

namespace PI.SqfRootShift.W

open PI.SqfLab

variable {g : ℕ} [Fact g.Prime]

theorem frob_fix (x : Fbar g) :
    x ^ (g ^ (minpoly (ZMod g) x).natDegree) = x := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hfr := IntermediateField.adjoin.finrank hint
  have : FiniteDimensional (ZMod g) (IntermediateField.adjoin (ZMod g) {x}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  let _ := Fintype.ofFinite (IntermediateField.adjoin (ZMod g) {x})
  have hc : Fintype.card (IntermediateField.adjoin (ZMod g) {x}) =
      g ^ (minpoly (ZMod g) x).natDegree := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := ZMod g), Nat.card_zmod, hfr]
  have h := FiniteField.pow_card
    (⟨x, IntermediateField.mem_adjoin_simple_self (ZMod g) x⟩ :
      IntermediateField.adjoin (ZMod g) {x})
  rw [hc] at h
  exact congrArg Subtype.val h

def Good (c : (ZMod g)ˣ) (P : (ZMod g)[X]) : Prop :=
  P.Monic ∧ Irreducible P ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ ∃ j : ℕ,
    P ∣ X ^ (ℓ ^ j) - C ((c : ZMod g) ^ (ℓ ^ j))

theorem aeval_eq_zero_of_dvd' {P Q : (ZMod g)[X]} (h : P ∣ Q) {z : Fbar g}
    (hz : aeval z P = 0) : aeval z Q = 0 := by
  obtain ⟨q, rfl⟩ := h
  simp [hz]

theorem good_root (c : (ZMod g)ˣ) (P : (ZMod g)[X]) (hP : Good c P) (z : Fbar g)
    (hz : z ∈ (P.map (algebraMap (ZMod g) (Fbar g))).roots) :
    (z * (algebraMap (ZMod g) (Fbar g) (c : ZMod g))⁻¹) ^ (g ^ P.natDegree - 1) = 1 ∧
      ∃ ℓ, ℓ.Prime ∧ ∃ j, (z * (algebraMap (ZMod g) (Fbar g) (c : ZMod g))⁻¹) ^ (ℓ ^ j) = 1 := by
  obtain ⟨hmon, hirr, ℓ, hℓ, j, hdvd⟩ := hP
  set c' := algebraMap (ZMod g) (Fbar g) (c : ZMod g) with hc'
  have hc0 : c' ≠ 0 := by
    rw [hc']; exact (_root_.map_ne_zero _).2 c.ne_zero
  have hz0 : aeval z P = 0 := by
    rw [mem_roots_map hmon.ne_zero] at hz
    rwa [aeval_def]
  have hmin : P = minpoly (ZMod g) z := minpoly.eq_of_irreducible_of_monic hirr hz0 hmon
  have hfix : z ^ (g ^ P.natDegree) = z := by rw [hmin]; exact frob_fix z
  have hℓj : z ^ (ℓ ^ j) = c' ^ (ℓ ^ j) := by
    have := aeval_eq_zero_of_dvd' hdvd hz0
    simp only [map_sub, map_pow, aeval_X, aeval_C] at this
    rw [sub_eq_zero] at this
    exact this
  have hzne : z ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_pos hℓ.pos j).ne'] at hℓj
    exact pow_ne_zero _ hc0 hℓj.symm
  have hcfix : c' ^ (g ^ P.natDegree) = c' := by
    rw [hc', ← map_pow, ZMod.pow_card_pow]
  set y := z * c'⁻¹ with hy
  have hy0 : y ≠ 0 := mul_ne_zero hzne (inv_ne_zero hc0)
  have hyfix : y ^ (g ^ P.natDegree) = y := by
    rw [hy, mul_pow, inv_pow, hfix, hcfix]
  have hpos : 1 ≤ g ^ P.natDegree := Nat.one_le_pow _ _ (Fact.out : g.Prime).pos
  refine ⟨?_, ℓ, hℓ, j, ?_⟩
  · have h2 : y ^ (g ^ P.natDegree - 1) * y = 1 * y := by
      rw [← pow_succ, Nat.sub_add_cancel hpos, hyfix, one_mul]
    exact mul_right_cancel₀ hy0 h2
  · rw [hy, mul_pow, inv_pow, hℓj, mul_inv_cancel₀ (pow_ne_zero _ hc0)]

end PI.SqfRootShift.W
end
end

