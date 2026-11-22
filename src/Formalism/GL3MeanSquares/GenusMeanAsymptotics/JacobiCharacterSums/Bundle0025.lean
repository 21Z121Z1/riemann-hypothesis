import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0018
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensPair
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0019
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0007
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0020

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensBlock
section
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

lemma char_mul_conj_self {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (a : ZMod M) :
    χ a * (starRingEnd ℂ) (χ a) = (1 : DirichletCharacter ℂ M) a := by
  have h : (starRingEnd ℂ) (χ a) = χ⁻¹ a := MulChar.star_apply' χ a
  rw [h, ← MulChar.mul_apply, mul_inv_cancel]

lemma char_mul_conj {M : ℕ} [NeZero M] (χ χ' : DirichletCharacter ℂ M) (a : ZMod M) :
    χ a * (starRingEnd ℂ) (χ' a) = (χ * χ'⁻¹) a := by
  have h : (starRingEnd ℂ) (χ' a) = χ'⁻¹ a := MulChar.star_apply' χ' a
  rw [h, ← MulChar.mul_apply]

lemma offdiag_term {M : ℕ} [NeZero M] (σ T : ℝ) (U : ℕ) (hU : 1 ≤ U) (hT : 2 ≤ T) (hσ : 1 / 2 ≤ σ)
    (p p' : DirichletCharacter ℂ M × ℂ)
    (hp : σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T) (hp' : σ ≤ p'.2.re ∧ p'.2.re ≤ 1 ∧ |p'.2.im| ≤ T)
    (hsp : p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) :
    ‖∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
        (n : ℂ) ^ (-((p.2 - (σ : ℂ)) + (starRingEnd ℂ) (p'.2 - (σ : ℂ))))‖ ≤
      (if p' = p then (U : ℝ) else 0) +
        (if p'.1 = p.1 then 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|) else 0) +
        4 * ((M : ℝ) + 1) * (2 + 2 * T) := by
  obtain ⟨hl, hu, hi⟩ := hp
  obtain ⟨hl', hu', hi'⟩ := hp'
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  set w : ℂ := (p.2 - (σ : ℂ)) + (starRingEnd ℂ) (p'.2 - (σ : ℂ)) with hw
  have hwre : w.re = p.2.re + p'.2.re - 2 * σ := by
    simp only [hw, add_re, sub_re, ofReal_re, conj_re]; ring
  have hwim : w.im = p.2.im - p'.2.im := by
    simp only [hw, add_im, sub_im, ofReal_im, conj_im]; ring
  have hw0 : 0 ≤ w.re := by rw [hwre]; linarith
  have hw1 : w.re ≤ 1 := by rw [hwre]; linarith
  have hwn : ‖w‖ ≤ 1 + 2 * T := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    rw [abs_of_nonneg hw0, hwim]
    have : |p.2.im - p'.2.im| ≤ |p.2.im| + |p'.2.im| := abs_sub _ _
    linarith
  have hB : 4 * ((M : ℝ) + 1) * (1 + ‖w‖) ≤ 4 * ((M : ℝ) + 1) * (2 + 2 * T) := by
    have : 1 + ‖w‖ ≤ 2 + 2 * T := by linarith
    gcongr
  have hB0 : 0 ≤ 4 * ((M : ℝ) + 1) * (2 + 2 * T) := by positivity
  have hq0 : 0 ≤ 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|) := by positivity
  by_cases h1 : p' = p
  · rw [if_pos h1, if_pos (by rw [h1])]
    have hdiag : ‖∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
        (n : ℂ) ^ (-w)‖ ≤ U := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ n ∈ Ioc U (2 * U), ‖p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
          (n : ℂ) ^ (-w)‖ ≤ 1 := by
        intro n hn
        have hn1 : 1 ≤ n := by have := (mem_Ioc.1 hn).1; omega
        rw [norm_mul, norm_mul, Complex.norm_conj]
        have a1 : ‖p.1 (n : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
        have a2 : ‖p'.1 (n : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
        have a3 : ‖(n : ℂ) ^ (-w)‖ ≤ 1 := norm_natCast_cpow_neg_le_one hn1 hw0
        calc ‖p.1 (n : ZMod M)‖ * ‖p'.1 (n : ZMod M)‖ * ‖(n : ℂ) ^ (-w)‖ ≤ 1 * 1 * 1 := by
              gcongr
          _ = 1 := by norm_num
      refine (sum_le_sum this).trans ?_
      rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
      exact_mod_cast (by omega : 2 * U - U ≤ U)
    linarith
  · rw [if_neg h1]
    by_cases h2 : p'.1 = p.1
    · rw [if_pos h2]
      have hgap : 1 ≤ |p.2.im - p'.2.im| := hsp (fun h => h1 h.symm) h2.symm
      have him : w.im ≠ 0 := by
        rw [hwim]; intro h0; rw [h0, abs_zero] at hgap; linarith
      have hsame := pair_same_bound M w hw0 hw1 him U hU
      have heq : ∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
          (n : ℂ) ^ (-w) =
          ∑ n ∈ Ioc U (2 * U), (1 : DirichletCharacter ℂ M) (n : ZMod M) * (n : ℂ) ^ (-w) := by
        refine sum_congr rfl (fun n _ => ?_)
        rw [h2, char_mul_conj_self]
      rw [heq]
      have hUp : (U : ℝ) ^ (1 - w.re) ≤ U := by
        calc (U : ℝ) ^ (1 - w.re) ≤ (U : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
          _ = U := Real.rpow_one _
      have hdiv : 4 * (U : ℝ) ^ (1 - w.re) / |w.im| ≤ 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|) := by
        rw [hwim, mul_one_div]
        gcongr
      linarith
    · rw [if_neg h2]
      have hne : p.1 * p'.1⁻¹ ≠ 1 := by
        intro h; exact h2 (mul_inv_eq_one.1 h).symm
      have hcross := pair_cross_bound M (p.1 * p'.1⁻¹) hne w hw0 U hU
      have heq : ∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
          (n : ℂ) ^ (-w) =
          ∑ n ∈ Ioc U (2 * U), (p.1 * p'.1⁻¹) (n : ZMod M) * (n : ℂ) ^ (-w) := by
        refine sum_congr rfl (fun n _ => ?_)
        rw [char_mul_conj]
      rw [heq]
      linarith

theorem off_diagonal_bound : Offdiag := by
  intro M _ S σ T U hU hT hσ hS hsp p hp
  classical
  have hU0 : (0 : ℝ) ≤ U := by positivity
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  have hterm := fun p' (hp' : p' ∈ S) =>
    offdiag_term σ T U hU hT hσ p p' (hS p hp) (hS p' hp') (hsp p hp p' hp')
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, sum_ite_eq' S p, if_pos hp,
    ← sum_filter, ← mul_sum]
  set Fib : Finset (DirichletCharacter ℂ M × ℂ) := S.filter (fun p' => p'.1 = p.1) with hFib
  set P : Finset ℝ := Fib.image (fun p' => p'.2.im) with hP
  have hinj : Set.InjOn (fun p' : DirichletCharacter ℂ M × ℂ => p'.2.im) (Fib : Set _) := by
    intro a ha b hb hab
    have ha' := mem_filter.1 (mem_coe.1 ha)
    have hb' := mem_filter.1 (mem_coe.1 hb)
    by_contra hne
    have := hsp a ha'.1 b hb'.1 hne (ha'.2.trans hb'.2.symm)
    simp only at hab
    rw [hab, sub_self, abs_zero] at this
    linarith
  have hpF : p ∈ Fib := mem_filter.2 ⟨hp, rfl⟩
  have htP : p.2.im ∈ P := mem_image_of_mem _ hpF
  have hsp' := (zero_spacing P T (by linarith)
    (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
      exact (hS a (mem_filter.1 ha).1).2.2)
    (by
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
      obtain ⟨b, hb, rfl⟩ := mem_image.1 hy
      have ha' := mem_filter.1 ha
      have hb' := mem_filter.1 hb
      exact hsp a ha'.1 b hb'.1 (fun h => hxy (by rw [h])) (ha'.2.trans hb'.2.symm))).2 _ htP
  have hsumeq : ∑ p' ∈ Fib, 1 / |p.2.im - p'.2.im| = ∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x| := by
    rw [← add_zero (∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x|)]
    have h0 : (0 : ℝ) = 1 / |p.2.im - p.2.im| := by simp
    rw [h0, sum_erase_add P _ htP, hP, sum_image hinj]
  rw [hsumeq]
  have hc0 : (0 : ℝ) ≤ S.card := by positivity
  have hB0 : 0 ≤ ((M : ℝ) + 1) * (2 + 2 * T) := by positivity
  have h1 : 4 * (U : ℝ) * ∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x| ≤
      4 * (U : ℝ) * (2 * (1 + Real.log (2 * T + 1))) := by gcongr
  have h2 : (S.card : ℝ) * (4 * ((M : ℝ) + 1) * (2 + 2 * T)) ≤
      (S.card : ℝ) * (8 * ((M : ℝ) + 1) * (2 + 2 * T)) := by
    apply mul_le_mul_of_nonneg_left _ hc0
    nlinarith
  linarith

lemma conj_natCast_cpow_neg' (n : ℕ) (z : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-z)) = (n : ℂ) ^ (-(starRingEnd ℂ) z) := by
  have h := Complex.cpow_conj (n : ℂ) (-z) (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)
  rw [map_neg] at h
  rw [h, Complex.conj_natCast]

theorem dyadic_block_count : BlockCnt := by
  intro α S f ρ Y N U σ θ G K hU hθ hσ hG hK hf hρ hoff hlarge hsmall
  set b : ℕ → ℂ := fun n => mco Y N n * (n : ℂ) ^ (-(σ : ℂ)) with hb
  set v : α → ℕ → ℂ := fun p n => f p n * (n : ℂ) ^ (-(ρ p - (σ : ℂ))) with hv
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hbv : ∀ p, ∀ n ∈ Ioc U (2 * U), b n * v p n = mco Y N n * f p n * (n : ℂ) ^ (-ρ p) := by
    intro p n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (mem_Ioc.1 hn).1; exact_mod_cast (by omega : n ≠ 0)
    have : (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(ρ p - (σ : ℂ))) = (n : ℂ) ^ (-ρ p) := by
      rw [← Complex.cpow_add _ _ hn0]; congr 1; ring
    simp only [hb, hv]
    rw [← this]; ring
  have hsum : ∀ p, ∑ n ∈ Ioc U (2 * U), b n * v p n = blkD Y N U (f p) (ρ p) := by
    intro p; unfold blkD; exact sum_congr rfl (hbv p)
  have heq : ∀ p p', ∑ n ∈ Ioc U (2 * U), v p n * (starRingEnd ℂ) (v p' n) =
      ∑ n ∈ Ioc U (2 * U), f p n * (starRingEnd ℂ) (f p' n) *
        (n : ℂ) ^ (-((ρ p - (σ : ℂ)) + (starRingEnd ℂ) (ρ p' - (σ : ℂ)))) := by
    intro p p'
    refine sum_congr rfl (fun n hn => ?_)
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (mem_Ioc.1 hn).1; exact_mod_cast (by omega : n ≠ 0)
    simp only [hv]
    rw [map_mul, conj_natCast_cpow_neg']
    have : (n : ℂ) ^ (-(ρ p - (σ : ℂ))) * (n : ℂ) ^ (-(starRingEnd ℂ) (ρ p' - (σ : ℂ))) =
        (n : ℂ) ^ (-((ρ p - (σ : ℂ)) + (starRingEnd ℂ) (ρ p' - (σ : ℂ)))) := by
      rw [← Complex.cpow_add _ _ hn0]; congr 1; ring
    rw [← this]; ring
  have hΔ : ∀ p ∈ S, ∑ p' ∈ S, ‖∑ n ∈ Ioc U (2 * U), v p n * (starRingEnd ℂ) (v p' n)‖ ≤
      (U : ℝ) * G + (S.card : ℝ) * K := by
    intro p hp
    simp only [heq]
    exact hoff p hp
  have hΔ0 : (0 : ℝ) ≤ (U : ℝ) * G + (S.card : ℝ) * K := by positivity
  have hmain := duality_inequality α ℕ S (Ioc U (2 * U)) b v _ hΔ0 hΔ
  simp only [hsum] at hmain
  set a : ℝ := 2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 with ha
  have hbn : ∑ n ∈ Ioc U (2 * U), ‖b n‖ ^ 2 ≤ a := by
    refine le_trans (le_of_eq ?_) (coefficient_block_bound Y N U σ hU hσ)
    refine sum_congr rfl (fun n hn => ?_)
    have hn1 : 0 < n := by have := (mem_Ioc.1 hn).1; omega
    simp only [hb, norm_mul, norm_natCast_cpow_of_pos hn1, neg_re, ofReal_re]
  have hlow : (S.card : ℝ) * θ ^ 2 ≤ ∑ p ∈ S, ‖blkD Y N U (f p) (ρ p)‖ ^ 2 := by
    have : ∀ p ∈ S, θ ^ 2 ≤ ‖blkD Y N U (f p) (ρ p)‖ ^ 2 := by
      intro p hp
      exact pow_le_pow_left₀ hθ.le (hlarge p hp) 2
    have h := sum_le_sum this
    rw [sum_const, nsmul_eq_mul] at h
    exact h
  have haU : a * U = 2 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 := by
    have : (U : ℝ) ^ (2 - 2 * σ) = (U : ℝ) ^ (1 - 2 * σ) * (U : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hU0]; congr 1; ring
    rw [this, Real.rpow_one, ha]; ring
  have h1 : (S.card : ℝ) * θ ^ 2 ≤ a * ((U : ℝ) * G + (S.card : ℝ) * K) :=
    hlow.trans (hmain.trans (mul_le_mul_of_nonneg_right hbn hΔ0))
  have hS0 : (0 : ℝ) ≤ S.card := by positivity
  have h2 : (S.card : ℝ) * θ ^ 2 ≤ 2 * (a * U) * G := by
    have := mul_le_mul_of_nonneg_left hsmall hS0
    nlinarith
  have hθ2 : 0 < θ ^ 2 := by positivity
  rw [le_div_iff₀ hθ2]
  rw [haU] at h2
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplRectF
section
open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem ex_phi_hasDerivAt (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun w : ℂ => (y : ℂ) ^ w / w) ((y : ℂ) * (Real.log y : ℂ) - y) 1 := by
  have h1 : HasDerivAt (fun w : ℂ => (y : ℂ) ^ w) ((y : ℂ) ^ (1 : ℂ) * Complex.log y * 1) 1 :=
    (hasDerivAt_id' (1 : ℂ)).const_cpow (Or.inl (by exact_mod_cast hy.ne'))
  have h2 := h1.div (hasDerivAt_id' (1 : ℂ)) one_ne_zero
  have e : ((y : ℂ) ^ (1 : ℂ) * Complex.log y * 1 * 1 - (y : ℂ) ^ (1 : ℂ) * 1) / 1 ^ 2 =
      (y : ℂ) * (Real.log y : ℂ) - y := by
    rw [Complex.cpow_one, ← Complex.ofReal_log hy.le]
    ring
  exact h2.congr_deriv e

theorem ex_phi_differentiableOn (y : ℝ) (hy : 0 < y) :
    DifferentiableOn ℂ (fun w : ℂ => (y : ℂ) ^ w / w) {w : ℂ | 0 < w.re} := by
  intro w hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  exact ((differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hy.ne'))).div differentiableAt_id hw0).differentiableWithinAt

theorem ex_rect_double (y : ℝ) (hy : 0 < y) (x₀ x₁ y₀ y₁ : ℝ) (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx₁ : 1 < x₁)
    (hy₀ : y₀ < 0) (hy₁ : 0 < y₁) :
    Formalism.ZF.rectInt (fun w => exKer y w / (w - 1)) x₀ x₁ y₀ y₁ =
      2 * Real.pi * I * ((y : ℂ) * (Real.log y : ℂ) - y) := by
  have hb : HasDerivAt (fun w : ℂ => (y : ℂ) ^ w / w) ((y : ℂ) * (Real.log y : ℂ) - y) 1 := ex_phi_hasDerivAt y hy
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1U : {w : ℂ | 0 < w.re} ∈ nhds (1 : ℂ) := hU.mem_nhds (by simp)
  have hφd : DifferentiableOn ℂ (fun w : ℂ => (y : ℂ) ^ w / w) {w : ℂ | 0 < w.re} := ex_phi_differentiableOn y hy
  have hG : DifferentiableOn ℂ (dslope (dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1) 1) {w : ℂ | 0 < w.re} :=
    (differentiableOn_dslope h1U).2 ((differentiableOn_dslope h1U).2 hφd)
  have hd1 : dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1 1 = (y : ℂ) * (Real.log y : ℂ) - y := by
    rw [dslope_same, hb.deriv]
  refine Formalism.ZF.rectangle_double_pole (fun w => exKer y w / (w - 1))
    (dslope (dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1) 1) (y : ℂ) ((y : ℂ) * (Real.log y : ℂ) - y) 1 x₀ x₁ y₀ y₁
    (by simpa using hx₀1) (by simpa using hx₁) (by simpa using hy₀) (by simpa using hy₁)
    ⟨{w : ℂ | 0 < w.re}, hU, ?_, hG⟩ ?_
  · intro z hz
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hz
    show 0 < z.re
    linarith [hz.1.1]
  · intro w hw
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw
    rw [dslope_of_ne _ hw, slope_def_field, dslope_of_ne _ hw, slope_def_field, hd1]
    simp only [exKer, Complex.cpow_one, div_one]
    by_cases h0 : w = 0
    · subst h0
      simp
      ring
    · field_simp
      ring

def exBdry (x₀ x₁ y₀ y₁ : ℝ) : Set ℂ :=
  {w : ℂ | x₀ ≤ w.re ∧ w.re ≤ x₁ ∧ y₀ ≤ w.im ∧ w.im ≤ y₁ ∧
    (w.re = x₀ ∨ w.re = x₁ ∨ w.im = y₀ ∨ w.im = y₁)}

theorem ex_mem_horiz {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {c : ℝ} (hc : c = y₀ ∨ c = y₁) {x : ℝ}
    (h : x ∈ Set.uIcc x₀ x₁) : ((x : ℂ) + c * I) ∈ exBdry x₀ x₁ y₀ y₁ := by
  rw [Set.uIcc_of_le hx] at h
  obtain ⟨h1, h2⟩ := h
  have hc' : y₀ ≤ c ∧ c ≤ y₁ := by
    rcases hc with rfl | rfl <;> constructor <;> linarith
  refine ⟨by simpa using h1, by simpa using h2, by simpa using hc'.1, by simpa using hc'.2, ?_⟩
  right; right
  simpa using hc

theorem ex_mem_vert {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {c : ℝ} (hc : c = x₀ ∨ c = x₁) {t : ℝ}
    (h : t ∈ Set.uIcc y₀ y₁) : ((c : ℂ) + t * I) ∈ exBdry x₀ x₁ y₀ y₁ := by
  rw [Set.uIcc_of_le hy] at h
  obtain ⟨h1, h2⟩ := h
  have hc' : x₀ ≤ c ∧ c ≤ x₁ := by
    rcases hc with rfl | rfl <;> constructor <;> linarith
  refine ⟨by simpa using hc'.1, by simpa using hc'.2, by simpa using h1, by simpa using h2, ?_⟩
  rcases hc with hc | hc
  · left
    simpa using hc
  · right; left
    simpa using hc

theorem ex_rectInt_congr {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (h : ∀ w ∈ exBdry x₀ x₁ y₀ y₁, f w = g w) :
    Formalism.ZF.rectInt f x₀ x₁ y₀ y₁ = Formalism.ZF.rectInt g x₀ x₁ y₀ y₁ := by
  have hh : ∀ c : ℝ, (c = y₀ ∨ c = y₁) →
      (∫ x : ℝ in x₀..x₁, f (x + c * I)) = ∫ x : ℝ in x₀..x₁, g (x + c * I) := by
    intro c hc
    exact intervalIntegral.integral_congr fun x hx' => h _ (ex_mem_horiz hx hy hc hx')
  have hv : ∀ c : ℝ, (c = x₀ ∨ c = x₁) →
      (∫ t : ℝ in y₀..y₁, f (c + t * I)) = ∫ t : ℝ in y₀..y₁, g (c + t * I) := by
    intro c hc
    exact intervalIntegral.integral_congr fun t ht => h _ (ex_mem_vert hx hy hc ht)
  unfold Formalism.ZF.rectInt
  rw [hh y₀ (Or.inl rfl), hh y₁ (Or.inr rfl), hv x₀ (Or.inl rfl), hv x₁ (Or.inr rfl)]

theorem ex_ii_horiz {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (exBdry x₀ x₁ y₀ y₁)) {c : ℝ} (hc : c = y₀ ∨ c = y₁) :
    IntervalIntegrable (fun x : ℝ => f (x + c * I)) MeasureTheory.volume x₀ x₁ := by
  apply ContinuousOn.intervalIntegrable
  exact hf.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + c * I).continuousOn
    fun x hx' => ex_mem_horiz hx hy hc hx'

theorem ex_ii_vert {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (exBdry x₀ x₁ y₀ y₁)) {c : ℝ} (hc : c = x₀ ∨ c = x₁) :
    IntervalIntegrable (fun t : ℝ => f (c + t * I)) MeasureTheory.volume y₀ y₁ := by
  apply ContinuousOn.intervalIntegrable
  exact hf.comp (by fun_prop : Continuous fun t : ℝ => (c : ℂ) + t * I).continuousOn
    fun t ht => ex_mem_vert hx hy hc ht

theorem ex_rectInt_add {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (exBdry x₀ x₁ y₀ y₁)) (hg : ContinuousOn g (exBdry x₀ x₁ y₀ y₁)) :
    Formalism.ZF.rectInt (fun w => f w + g w) x₀ x₁ y₀ y₁ =
      Formalism.ZF.rectInt f x₀ x₁ y₀ y₁ + Formalism.ZF.rectInt g x₀ x₁ y₀ y₁ := by
  unfold Formalism.ZF.rectInt
  rw [intervalIntegral.integral_add (ex_ii_horiz hx hy hf (Or.inl rfl)) (ex_ii_horiz hx hy hg (Or.inl rfl)),
    intervalIntegral.integral_add (ex_ii_horiz hx hy hf (Or.inr rfl)) (ex_ii_horiz hx hy hg (Or.inr rfl)),
    intervalIntegral.integral_add (ex_ii_vert hx hy hf (Or.inr rfl)) (ex_ii_vert hx hy hg (Or.inr rfl)),
    intervalIntegral.integral_add (ex_ii_vert hx hy hf (Or.inl rfl)) (ex_ii_vert hx hy hg (Or.inl rfl))]
  ring

theorem exKer_continuousAt (y : ℝ) (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    ContinuousAt (exKer y) w := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  unfold exKer
  apply ContinuousAt.div
  · exact continuousAt_const_cpow hy0
  · fun_prop
  · exact mul_ne_zero h0 (sub_ne_zero.mpr h1)

theorem ex_bdry_ne {x₀ x₁ y₀ y₁ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx₁ : 1 < x₁)
    (hy₀ : y₀ < 0) (hy₁ : 0 < y₁) {w : ℂ} (hw : w ∈ exBdry x₀ x₁ y₀ y₁) : w ≠ 0 ∧ w ≠ 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  constructor
  · rintro rfl
    simp at h1
    linarith
  · rintro rfl
    simp at h5
    rcases h5 with h | h | h | h <;> linarith

private theorem neg_div_mul_eq_neg_add_div_mul_add_div (a b K u : ℂ) (ha : a ≠ 0) (hu : u ≠ 0) :
    -(b / a) * K = -((1 * a + u * b) / (u * a)) * K + K / u := by
  field_simp
  ring

set_option maxHeartbeats 800000 in
theorem ex_rect_Fchi {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y : ℝ) (hy : 0 < y) (σ₁ σ₀ T' : ℝ)
    (hσ₁ : 0 < σ₁) (hσ₁1 : σ₁ < 1) (hσ₀ : 1 < σ₀) (hT' : 0 < T')
    (Z : Finset ℂ) (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ |ρ.im| < T'))
    (hedge : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T' → exLF χ w = 0 → σ₁ < w.re ∧ |w.im| < T') :
    Formalism.ZF.rectInt (Fchi χ y) σ₁ σ₀ (-T') T' =
      2 * Real.pi * I * (explicitFormulaConstant χ * y + (if χ = 1 then (y : ℂ) * (Real.log y : ℂ) - y else 0) -
        ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * exKer y ρ) := by
  have hfd : Differentiable ℂ (exLF χ) := exLF_differentiable χ
  have hx : σ₁ ≤ σ₀ := by linarith
  have hyy : -T' ≤ T' := by linarith
  have hZ' : ∀ ρ : ℂ, ρ ∈ Z ↔ exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ ρ.re < σ₀ ∧ -T' < ρ.im ∧ ρ.im < T' := by
    intro ρ
    rw [hZ ρ]
    constructor
    · rintro ⟨h0, h1, h2⟩
      have := exLF_re_lt_one χ h0
      exact ⟨h0, h1, by linarith, (abs_lt.mp h2).1, (abs_lt.mp h2).2⟩
    · rintro ⟨h0, h1, -, h3, h4⟩
      exact ⟨h0, h1, abs_lt.mpr ⟨h3, h4⟩⟩
  have hedge' : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → -T' ≤ w.im → w.im ≤ T' → exLF χ w = 0 →
      σ₁ < w.re ∧ w.re < σ₀ ∧ -T' < w.im ∧ w.im < T' := by
    intro w h1 h2 h3 h4 h0
    obtain ⟨h5, h6⟩ := hedge w h1 h2 (abs_le.mpr ⟨h3, h4⟩) h0
    have := exLF_re_lt_one χ h0
    exact ⟨h5, by linarith, (abs_lt.mp h6).1, (abs_lt.mp h6).2⟩
  have hmain := ex_rect_logDeriv (exLF χ) hfd (exLF_one_ne_zero χ) y hy σ₁ σ₀ (-T') T' hσ₁ hσ₁1 hσ₀
    (by linarith) hT' Z hZ' hedge'
  by_cases hχ : χ = 1
  · subst hχ
    have hbd : ∀ w ∈ exBdry σ₁ σ₀ (-T') T', w ≠ 0 ∧ w ≠ 1 ∧ exLF (1 : DirichletCharacter ℂ M) w ≠ 0 := by
      intro w hw
      obtain ⟨h0, h1⟩ := ex_bdry_ne hσ₁ hσ₁1 hσ₀ (by linarith) hT' hw
      refine ⟨h0, h1, fun hfw => ?_⟩
      obtain ⟨a1, a2, a3, a4, a5⟩ := hw
      obtain ⟨b1, b2, b3, b4⟩ := hedge' w a1 a2 a3 a4 hfw
      rcases a5 with h | h | h | h <;> linarith
    have hA : ContinuousOn (fun w => -(deriv (exLF (1 : DirichletCharacter ℂ M)) w /
        exLF (1 : DirichletCharacter ℂ M) w) * exKer y w) (exBdry σ₁ σ₀ (-T') T') := by
      intro w hw
      obtain ⟨h0, h1, h2⟩ := hbd w hw
      have hd : ContinuousAt (deriv (exLF (1 : DirichletCharacter ℂ M))) w :=
        (hfd.analyticAt w).deriv.continuousAt
      exact (((hd.div (hfd w).continuousAt h2).neg).mul (exKer_continuousAt y hy h0 h1)).continuousWithinAt
    have hK : ContinuousOn (fun w => exKer y w / (w - 1)) (exBdry σ₁ σ₀ (-T') T') := by
      intro w hw
      obtain ⟨h0, h1, -⟩ := hbd w hw
      have hs : ContinuousAt (fun s : ℂ => s - 1) w := continuousAt_id.sub continuousAt_const
      exact ((exKer_continuousAt y hy h0 h1).div hs (sub_ne_zero.mpr h1)).continuousWithinAt
    have hB : ∀ w ∈ exBdry σ₁ σ₀ (-T') T', Fchi (1 : DirichletCharacter ℂ M) y w =
        -(deriv (exLF (1 : DirichletCharacter ℂ M)) w / exLF (1 : DirichletCharacter ℂ M) w) * exKer y w +
          exKer y w / (w - 1) := by
      intro w hw
      obtain ⟨h0, h1, h2⟩ := hbd w hw
      have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
      have hfw : exLF (1 : DirichletCharacter ℂ M) w =
          (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := exLF_one_char_apply h1
      have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w ≠ 0 := by
        intro h
        apply h2
        rw [hfw, h, mul_zero]
      have hLd : DifferentiableAt ℂ (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w :=
        DirichletCharacter.differentiableAt_LFunction 1 w (Or.inl h1)
      have hev : exLF (1 : DirichletCharacter ℂ M) =ᶠ[nhds w]
          fun s => (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) s :=
        (eventually_ne_nhds h1).mono fun s hs => exLF_one_char_apply hs
      have hder : deriv (exLF (1 : DirichletCharacter ℂ M)) w =
          1 * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w +
            (w - 1) * deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w := by
        rw [hev.deriv_eq]
        exact (((hasDerivAt_id' w).sub_const 1).mul hLd.hasDerivAt).deriv
      have e1 : Fchi (1 : DirichletCharacter ℂ M) y w =
          -(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w /
            DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w) * exKer y w := by
        simp only [Fchi, negLD, exKer, mul_div_assoc]
      rw [e1, hder, hfw]
      exact neg_div_mul_eq_neg_add_div_mul_add_div _ _ _ _ hL hw1
    rw [ex_rectInt_congr hx hyy hB, ex_rectInt_add hx hyy hA hK, hmain,
      ex_rect_double y hy σ₁ σ₀ (-T') T' hσ₁ hσ₁1 hσ₀ (by linarith) hT', if_pos rfl]
    simp only [explicitFormulaConstant, exOrd]
    ring
  · have hfL : exLF χ = DirichletCharacter.LFunction χ := exLF_of_ne hχ
    have hF : Fchi χ y = fun w => -(deriv (exLF χ) w / exLF χ w) * exKer y w := by
      funext w
      simp only [Fchi, negLD, exKer, hfL, mul_div_assoc]
    rw [hF, hmain, if_neg hχ]
    simp only [explicitFormulaConstant, exOrd]
    ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

