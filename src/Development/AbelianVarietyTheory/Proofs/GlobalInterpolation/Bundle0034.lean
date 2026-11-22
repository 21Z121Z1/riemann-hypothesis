import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0031
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLeNormLFunctionOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionConjEqZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZeroFreePrincipal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpSumBounds
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodLiftEqIdempotentLift
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0022
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DirichletLFewZerosSmallDisc
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.SmallDiscZeros

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
private lemma derSeries_one_eq_tsum_vonMangoldt (σ : ℝ) :
    _root_.GlobalTheory.Lin.derSeries (fun n ↦ (1 : DirichletCharacter ℂ 1) n) 0 ((σ : ℂ) + (0 : ℝ) * I) =
      ((∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  unfold _root_.GlobalTheory.Lin.derSeries
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n ↦ ?_
  dsimp only
  rw [MulChar.one_apply (isUnit_of_subsingleton _)]
  push_cast
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  simp

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
private lemma re_natCast_div_pow_zero_add_one (m : ℕ) (z : ℂ) :
    ((m : ℂ) / z ^ (0 + 1)).re = m * (z⁻¹).re := by
  rw [zero_add, pow_one, div_eq_mul_inv, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
private lemma re_lt_one_of_mem_zerosDisc {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {c w : ℂ}
    {R : ℝ} (hw : w ∈ _root_.GlobalTheory.Lin.zerosDisc χ c R) : w.re < 1 := by
  simp only [_root_.GlobalTheory.Lin.zerosDisc, Set.mem_setOf_eq] at hw
  obtain ⟨-, h1, h0⟩ := hw
  by_contra h
  exact LFunction_ne_zero_of_one_le_re χ h1 (not_lt.mp h) h0

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
private lemma inv_re_nonneg_of_re_nonneg {z : ℂ} (h : 0 ≤ z.re) : 0 ≤ (z⁻¹).re := by
  rw [Complex.inv_re]
  exact div_nonneg h (Complex.normSq_nonneg _)

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
private lemma summable_vonMangoldt_mul_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ ↦ vonMangoldt n * (n : ℝ) ^ (-σ) := by
  have h := LSeriesSummable_vonMangoldt (s := (σ : ℂ)) (by simpa using hσ)
  have h' : Summable fun n ↦ ‖LSeries.term (fun n ↦ (vonMangoldt n : ℂ)) (σ : ℂ) n‖ :=
    summable_norm_iff.mpr h
  refine h'.congr fun n ↦ ?_
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
private lemma norm_derSeries_le_tsum_vonMangoldt {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    ‖_root_.GlobalTheory.Lin.derSeries (fun n ↦ χ n) 0 s‖ ≤
      ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-s.re) := by
  unfold _root_.GlobalTheory.Lin.derSeries
  refine tsum_of_norm_bounded (summable_vonMangoldt_mul_rpow_neg hs).hasSum fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
      Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg, Complex.neg_re]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _))
      (by positivity)

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
private lemma inv_re_ge_of_norm_sub_le {t r : ℝ} {w : ℂ} (hr : 0 < r) (hw : ‖w - (1 + t * I)‖ ≤ r)
    (hre : w.re < 1) : 1 / (4 * r) ≤ ((((1 + r : ℝ) : ℂ) + t * I - w)⁻¹).re := by
  set z : ℂ := ((1 + r : ℝ) : ℂ) + t * I - w with hz
  have hzre : z.re = 1 + r - w.re := by simp [hz]
  have hzre' : r < z.re := by linarith
  have hznorm : ‖z‖ ≤ 2 * r := by
    have hz' : z = (r : ℂ) - (w - (1 + t * I)) := by rw [hz]; push_cast; ring
    rw [hz']
    calc ‖(r : ℂ) - (w - (1 + t * I))‖ ≤ ‖(r : ℂ)‖ + ‖w - (1 + t * I)‖ := norm_sub_le _ _
      _ ≤ r + r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]; linarith
      _ = 2 * r := by ring
  have hpos : 0 < Complex.normSq z := by
    refine Complex.normSq_pos.mpr fun h ↦ ?_
    rw [h, Complex.zero_re] at hzre'
    linarith
  rw [Complex.inv_re, div_le_div_iff₀ (by positivity) hpos, Complex.normSq_eq_norm_sq]
  nlinarith [mul_le_mul hznorm hznorm (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * r)]

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in

theorem _root_.GlobalTheory.SmallDiscZeros.few_zeros : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t r : ℝ), (χ ≠ 1 ∨ 2 ≤ |t|) → 0 < r → r ≤ 1 / 2 → (_root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r).Finite ∧ (∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r, (_root_.GlobalTheory.Lin.ord χ w : ℝ)) ≤ C * (1 + r * Real.log (q * (|t| + 2))) := by
  obtain ⟨C, hC, hmain⟩ := _root_.GlobalTheory.LogDerivHigher.main
  refine ⟨6 + 4 * C, by positivity, ?_⟩
  intro q _ χ t r hχt hr hr2
  have hσ1 : 1 < 1 + r := by linarith
  have hσ2 : 1 + r ≤ 2 := by linarith
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hL0 : 0 ≤ Real.log (q * (|t| + 2)) :=
    Real.log_nonneg (by nlinarith [abs_nonneg t])
  have hTS : _root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r ⊆ _root_.GlobalTheory.Lin.zerosDisc χ (2 + t * I) 3 := by
    intro w hw
    simp only [_root_.GlobalTheory.Lin.zerosDisc, Set.mem_setOf_eq] at hw ⊢
    refine ⟨?_, hw.2⟩
    calc ‖w - (2 + t * I)‖ = ‖(w - (1 + t * I)) - 1‖ := by ring_nf
      _ ≤ ‖w - (1 + t * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 := by rw [norm_one]; linarith [hw.1]
  obtain ⟨hfin, -, hbound⟩ := hmain q χ (1 + r) t 0 hσ1 hσ2
  obtain ⟨hfin₁, -, hbound₁⟩ := hmain 1 1 (1 + r) 0 0 hσ1 hσ2
  have hTfin := hfin.subset hTS
  refine ⟨hTfin, ?_⟩
  set G : ℝ := ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + r)) with hG
  have hG_le : G ≤ 1 / r + C := by
    rw [derSeries_one_eq_tsum_vonMangoldt, if_pos rfl] at hbound₁
    have hP : (1 : ℂ) / (((1 + r : ℝ) : ℂ) + (0 : ℝ) * I - 1) ^ (0 + 1) = ((1 / r : ℝ) : ℂ) := by
      push_cast; ring
    rw [hP] at hbound₁
    have hZ₁ : 0 ≤ (∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc (1 : DirichletCharacter ℂ 1) (2 + (0 : ℝ) * I) 3,
        ((_root_.GlobalTheory.Lin.ord (1 : DirichletCharacter ℂ 1) w : ℕ) : ℂ) /
          (((1 + r : ℝ) : ℂ) + (0 : ℝ) * I - w) ^ (0 + 1)).re := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hfin₁, Complex.re_sum]
      refine Finset.sum_nonneg fun w hw ↦ ?_
      rw [re_natCast_div_pow_zero_add_one]
      have hw' := re_lt_one_of_mem_zerosDisc ((Set.Finite.mem_toFinset hfin₁).mp hw)
      refine mul_nonneg (Nat.cast_nonneg _) (inv_re_nonneg_of_re_nonneg ?_)
      simp
      linarith
    have hre := (Complex.re_le_norm _).trans hbound₁
    rw [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re] at hre
    have hlog : Real.log ((1 : ℕ) * (|(0 : ℝ)| + 2)) ≤ 1 := by
      norm_num
      linarith [Real.log_two_lt_d9]
    have hCl : C * Real.log ((1 : ℕ) * (|(0 : ℝ)| + 2)) / (1 + r) ^ 0 ≤ C := by
      rw [pow_zero, div_one]
      nlinarith
    linarith
  have key : ∀ (X Y W : ℂ) (B : ℝ), ‖(X - Y) + W‖ ≤ B → ‖W‖ ≤ B + ‖X‖ + ‖Y‖ := by
    intro X Y W B h
    have hW : W = ((X - Y) + W) - X + Y := by ring
    rw [hW]
    calc ‖((X - Y) + W) - X + Y‖ ≤ ‖(X - Y) + W‖ + ‖X‖ + ‖Y‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ B + ‖X‖ + ‖Y‖ := by linarith
  have hZnorm := key _ _ _ _ hbound
  rw [pow_zero, div_one] at hZnorm
  have hre : (((1 + r : ℝ) : ℂ) + t * I).re = 1 + r := by simp
  have hA := norm_derSeries_le_tsum_vonMangoldt χ (s := ((1 + r : ℝ) : ℂ) + t * I) (by rw [hre]; exact hσ1)
  rw [hre] at hA
  have hZn : ‖∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc χ (2 + t * I) 3,
      ((_root_.GlobalTheory.Lin.ord χ w : ℕ) : ℂ) / (((1 + r : ℝ) : ℂ) + t * I - w) ^ (0 + 1)‖ ≤
      C * Real.log (q * (|t| + 2)) + G + 1 := by
    split_ifs at hZnorm with h1
    · have ht : 2 ≤ |t| := hχt.resolve_left (not_not.mpr h1)
      have him : |t| ≤ ‖((1 + r : ℝ) : ℂ) + t * I - 1‖ := by
        have := Complex.abs_im_le_norm (((1 + r : ℝ) : ℂ) + t * I - 1)
        simpa using this
      have hY : ‖(1 : ℂ) / (((1 + r : ℝ) : ℂ) + t * I - 1) ^ (0 + 1)‖ ≤ 1 := by
        rw [zero_add, pow_one, norm_div, norm_one, div_le_one (by linarith)]
        linarith
      linarith
    · rw [norm_zero] at hZnorm
      linarith
  have hZre : (∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r, (_root_.GlobalTheory.Lin.ord χ w : ℝ)) *
      (1 / (4 * r)) ≤ (∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc χ (2 + t * I) 3,
      ((_root_.GlobalTheory.Lin.ord χ w : ℕ) : ℂ) / (((1 + r : ℝ) : ℂ) + t * I - w) ^ (0 + 1)).re := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hTfin, Finset.sum_mul,
      finsum_mem_eq_finite_toFinset_sum _ hfin, Complex.re_sum]
    refine (Finset.sum_le_sum fun w hw ↦ ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Set.Finite.toFinset_subset_toFinset.mpr hTS)
        fun w hw _ ↦ ?_)
    · rw [re_natCast_div_pow_zero_add_one]
      have hw' := (Set.Finite.mem_toFinset hTfin).mp hw
      refine mul_le_mul_of_nonneg_left (inv_re_ge_of_norm_sub_le hr ?_ (re_lt_one_of_mem_zerosDisc hw'))
        (Nat.cast_nonneg _)
      simp only [_root_.GlobalTheory.Lin.zerosDisc, Set.mem_setOf_eq] at hw'
      exact hw'.1
    · rw [re_natCast_div_pow_zero_add_one]
      have hw' := re_lt_one_of_mem_zerosDisc ((Set.Finite.mem_toFinset hfin).mp hw)
      refine mul_nonneg (Nat.cast_nonneg _) (inv_re_nonneg_of_re_nonneg ?_)
      simp
      linarith
  set N := ∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r, (_root_.GlobalTheory.Lin.ord χ w : ℝ) with hN
  set L := Real.log (q * (|t| + 2)) with hL
  have h1 : N * (1 / (4 * r)) ≤ C * L + G + 1 := hZre.trans ((Complex.re_le_norm _).trans hZn)
  have h2 : N ≤ 4 * r * (C * L + G + 1) := by
    have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * r)
    have e : 4 * r * (N * (1 / (4 * r))) = N := by field_simp
    linarith
  have h3 : 4 * r * (C * L + G + 1) ≤ 4 * (C * (r * L)) + 4 + 4 * r * (C + 1) := by
    have e : 4 * r * (1 / r) = 4 := by field_simp
    have h5 := mul_le_mul_of_nonneg_left hG_le (by positivity : (0 : ℝ) ≤ 4 * r)
    nlinarith
  have hrL : 0 ≤ r * L := by positivity
  have h6 := mul_le_mul_of_nonneg_right hr2 (by positivity : (0 : ℝ) ≤ C + 1)
  nlinarith [mul_nonneg hC.le hrL]

end GlobalTheory.SmallDiscZeros
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDirichletLFunctionZeroGapNearOne
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.ZeroGapNearOne

lemma log_pos {x : ℝ} (hx : 1 ≤ x) : 0 < Real.log (3 * x) := Real.log_pos (by linarith)

lemma weaken {x c d : ℝ} (hx : 1 ≤ x) (hc : 0 < c) (hcd : c ≤ d) :
    c / (x ^ 2 * Real.log (3 * x)) ≤ d / Real.log (3 * x) := by
  have hL := log_pos hx
  have h2 : 1 ≤ x ^ 2 := one_le_pow₀ hx
  apply div_le_div₀ (by linarith) hcd hL
  nlinarith

lemma of_region {x c d t r : ℝ} (hx : 1 ≤ x) (hc : 0 < c) (hcd : c ≤ d) (ht : |t| ≤ 1)
    (h : r < 1 - d / Real.log (x * (|t| + 2))) :
    c / (x ^ 2 * Real.log (3 * x)) ≤ 1 - r := by
  have h0 := abs_nonneg t
  have h1 : 0 < Real.log (x * (|t| + 2)) := Real.log_pos (by nlinarith)
  have h2 : Real.log (x * (|t| + 2)) ≤ Real.log (3 * x) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have h3 : d / Real.log (3 * x) ≤ d / Real.log (x * (|t| + 2)) :=
    div_le_div_of_nonneg_left (by linarith) h1 h2
  have := weaken hx hc hcd
  linarith

lemma log_le_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log (3 * x) ≤ 4 * √x := by
  have hs : 0 < √x := Real.sqrt_pos.2 (by linarith)
  have hsq : √x * √x = x := Real.mul_self_sqrt (by linarith)
  have h1 : Real.log (3 * x) ≤ Real.log ((2 * √x) ^ 2) :=
    Real.log_le_log (by linarith) (by nlinarith)
  rw [Real.log_pow] at h1
  have h2 := Real.log_le_sub_one_of_pos (show 0 < 2 * √x by positivity)
  push_cast at h1
  linarith

lemma real_case {x a C c δ : ℝ} (hx : 1 ≤ x) (hC : 0 < C) (hδ : 0 ≤ δ) (hc : 0 < c)
    (hca : c ≤ a / (4 * C))
    (h : a / x ^ ((3 : ℝ) / 2) ≤ C * Real.log (3 * x) ^ 2 * δ) :
    c / (x ^ 2 * Real.log (3 * x)) ≤ δ := by
  have hL := log_pos hx
  have hs : 0 < √x := Real.sqrt_pos.2 (by linarith)
  have hsq : √x * √x = x := Real.mul_self_sqrt (by linarith)
  have hx0 : 0 < x := by linarith
  have hp : x ^ ((3 : ℝ) / 2) = x * √x := by
    rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hx0,
      Real.rpow_one]
  rw [hp, div_le_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity)] at hca
  rw [div_le_iff₀ (by positivity)]
  have hl := log_le_sqrt hx
  have h3 : C * Real.log (3 * x) ^ 2 * δ * (x * √x)
      ≤ (C * Real.log (3 * x) * δ * (x * √x)) * (4 * √x) := by
    calc _ = (C * Real.log (3 * x) * δ * (x * √x)) * Real.log (3 * x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
  have h4 : (C * Real.log (3 * x) * δ * (x * √x)) * (4 * √x)
      = δ * (x ^ 2 * Real.log (3 * x)) * (4 * C) := by
    calc _ = 4 * C * Real.log (3 * x) * δ * x * (√x * √x) := by ring
      _ = _ := by rw [hsq]; ring
  have h5 : c * (4 * C) ≤ δ * (x ^ 2 * Real.log (3 * x)) * (4 * C) := by linarith
  exact le_of_mul_le_mul_right h5 (by positivity)

theorem exists_gap : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
    (χ ≠ 1 ∨ ρ ≠ 1) → LFunction χ ρ = 0 → |ρ.im| ≤ 1 →
      c / ((q : ℝ) ^ 2 * Real.log (3 * q)) ≤ 1 - ρ.re := by
  obtain ⟨a, ha, Ha⟩ := GlobalTheory.LOneLower.exists_le_norm_LFunction_one
  obtain ⟨C, hC, HC⟩ := GlobalTheory.DirichletDeriv.exists_norm_deriv_LFunction_le
  obtain ⟨d, hd, Hd⟩ := GlobalTheory.ZeroFreeComplex.zero_free_region
  obtain ⟨e, he, He⟩ := GlobalTheory.ZeroFreePrincipal.zero_free
  refine ⟨min (min 1 (a / (4 * C))) (min d e), by positivity, ?_⟩
  intro q _ χ ρ hne hz him
  have hc : 0 < min (min 1 (a / (4 * C))) (min d e) := by positivity
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le
  by_cases h1 : χ = 1
  · subst h1
    have hρ : ρ ≠ 1 := hne.resolve_left (by simp)
    exact of_region hq hc ((min_le_right _ _).trans (min_le_right _ _)) him (He q ρ hρ hz)
  by_cases h2 : χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0
  · exact of_region hq hc ((min_le_right _ _).trans (min_le_left _ _)) him (Hd q χ ρ h1 hz h2)
  push_neg at h2
  obtain ⟨hsq, hreal⟩ := h2
  have hlt : ρ.re < 1 := by
    by_contra h
    exact LFunction_ne_zero_of_one_le_re χ hne (not_lt.1 h) hz
  by_cases h3 : 1 / Real.log (3 * q) ≤ 1 - ρ.re
  · exact (weaken hq hc ((min_le_left _ _).trans (min_le_left _ _))).trans h3
  push_neg at h3
  refine real_case hq hC (by linarith) hc ((min_le_left _ _).trans (min_le_right _ _)) ?_
  refine (Ha q χ h1 hsq).trans ?_
  have hconv : Convex ℝ {z : ℂ | z.im = 0 ∧ ρ.re ≤ z.re ∧ z.re ≤ 1} := by
    intro x hx y hy s t hs ht hst
    obtain ⟨hx1, hx2, hx3⟩ := hx
    obtain ⟨hy1, hy2, hy3⟩ := hy
    refine ⟨by simp [hx1, hy1], ?_, ?_⟩
    · simp only [add_re, smul_re, smul_eq_mul]
      have : ρ.re = s * ρ.re + t * ρ.re := by rw [← add_mul, hst, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left hx2 hs, mul_le_mul_of_nonneg_left hy2 ht]
    · simp only [add_re, smul_re, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left hx3 hs, mul_le_mul_of_nonneg_left hy3 ht]
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := LFunction χ)
    (C := C * Real.log (3 * q) ^ 2) (x := ρ) (y := 1)
    (fun z _ => differentiable_LFunction h1 z)
    (fun z hz' => by
      obtain ⟨h4, h5, h6⟩ := hz'
      have : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h4])
      rw [this]
      exact HC q χ h1 z.re (by linarith) h6)
    hconv ⟨hreal, le_rfl, hlt.le⟩ ⟨by simp, by simpa using hlt.le, by simp⟩
  rw [hz, sub_zero] at key
  have hn : ‖(1 : ℂ) - ρ‖ = 1 - ρ.re := by
    have : (1 : ℂ) - ρ = ((1 - ρ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hreal])
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rwa [hn] at key

end GlobalTheory.ZeroGapNearOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpSumBoundsStatement
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_exp_mul_aChi_bounds : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), (∀ t : ℝ, 0 < t → Summable (fun n : ℕ => ‖𝓕.aChi χ n‖ * Real.exp (-(t * n))) ∧ ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) - 𝓕.res χ / t‖ ≤ C * 𝓕.B ^ 11 * min t (1 / t)) ∧ (χ ≠ 1 → (∀ t : ℝ, 1 ≤ t → ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ)‖ ≤ C * 𝓕.B * Real.exp (-(t / 2))) ∧ ∫ t in Set.Ioi (0 : ℝ), ∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) = 𝓕.F χ 1) := by
  first | exact @GlobalTheory.Hk.LFam.exp_sum_bounds | exact GlobalTheory.Hk.LFam.exp_sum_bounds | (intros; apply GlobalTheory.Hk.LFam.exp_sum_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodLiftEqIdempotentLiftStatement
section
open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodLift_eq_idempotent_lift : ∀ (q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ), S.Ok → GlobalTheory.MomOne.Split S.d q → S.NNBasis q b → S.IsTheta e → ∀ N₀ : ℕ, 0 < N₀ → Nat.Coprime N₀ q → (N₀ : ℂ) • t ∈ S.La → ∀ (n : ℕ), ∀ y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ OK S.d, ‖lamA lam (conj κ)‖ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (q : ℂ) ^ n) • x}, (∃ z : ℤ, (beta S.d S.Hm y y).re = z) ∧ ∃ (m : ℕ) (eps : ℂ) (yt : Fin r → Fin (q ^ n)), IsIdem lam S.d m eps ∧ 2 * n ≤ m ∧ (∀ i, ∃ z : ℤ, (hf S.Hm (eps • b i) t).im = z) ∧ opW S.d S.Hm y (opU S.Hm t e) = opW S.d S.Hm (liftY q n eps b yt) (opU S.Hm t e) ∧ ∀ a : Fin r → ℕ, kap S.Hm (∑ i, (a i : ℂ) • b i) y = kap S.Hm (vecA n b fun i => (a i : ℤ_[q])) (liftY q n eps b yt) := by
  first | exact @GlobalTheory.MomN.goodLift_eq | exact GlobalTheory.MomN.goodLift_eq | (intros; apply GlobalTheory.MomN.goodLift_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleFiniteProduct
section
open Complex
open scoped Real

namespace GlobalTheory.JacobiTriple

theorem finTriple_sum_odd (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

theorem finTriple_term (s x : ℂ) (hs : s ≠ 0) (hx : x ≠ 0) (n k : ℕ) (hk : k ≤ 2 * n) :
    (x⁻¹ ^ n * s ^ (n ^ 2)) *
        (qBinom (s ^ 2) (2 * n) k * s ^ (k * (k - 1)) * (x * s ^ ((1 : ℤ) - 2 * n)) ^ k) =
      finCoeff (s ^ 2) n ((k : ℤ) - n) * (x ^ ((k : ℤ) - n) * s ^ (((k : ℤ) - n) ^ 2)) := by
  have hc : finCoeff (s ^ 2) n ((k : ℤ) - n) = qBinom (s ^ 2) (2 * n) k := by
    unfold finCoeff
    rw [if_pos (by omega)]
    congr 1
    omega
  rw [hc]
  have hkk : ((k * (k - 1) : ℕ) : ℤ) = (k : ℤ) * ((k : ℤ) - 1) := by
    rcases k with _ | k
    · simp
    · push_cast [Nat.add_sub_cancel]; ring
  have he : ((k : ℤ) - n) ^ 2 = ((n ^ 2 + k * (k - 1) : ℕ) : ℤ) + (1 - 2 * n) * k := by
    rw [Nat.cast_add, hkk]; push_cast; ring
  have hxz : x ^ ((k : ℤ) - n) = x ^ k * x⁻¹ ^ n := by
    rw [zpow_sub₀ hx, zpow_natCast, zpow_natCast, div_eq_mul_inv, inv_pow]
  rw [hxz, he, zpow_add₀ hs, zpow_natCast, zpow_mul, zpow_natCast, pow_add, mul_pow]
  ring

theorem finTriple (s x : ℂ) (hs : s ≠ 0) (hs1 : ‖s‖ < 1) (hx : x ≠ 0) (n : ℕ) :
    ∏ k ∈ Finset.range n, ((1 + x * s ^ (2 * k + 1)) * (1 + x⁻¹ * s ^ (2 * k + 1))) =
      ∑ j ∈ Finset.Icc (-(n : ℤ)) n, finCoeff (s ^ 2) n j * (x ^ j * s ^ (j ^ 2)) := by
  set X := x * s ^ ((1 : ℤ) - 2 * n) with hX
  have ha : ∀ k ∈ Finset.range n, 1 + x * s ^ (2 * k + 1) = 1 + X * s ^ (2 * (n + k)) := by
    intro k _
    rw [hX, mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hs]
    congr 3
    push_cast; ring
  have hb : ∀ k ∈ Finset.range n, 1 + x⁻¹ * s ^ (2 * k + 1) =
      (x⁻¹ * s ^ (2 * k + 1)) * (1 + X * s ^ (2 * (n - 1 - k))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have e : ((2 * k + 1 : ℕ) : ℤ) + (1 - 2 * n) + ((2 * (n - 1 - k) : ℕ) : ℤ) = 0 := by omega
    have hab : x⁻¹ * s ^ (2 * k + 1) * (X * s ^ (2 * (n - 1 - k))) = 1 := by
      calc x⁻¹ * s ^ (2 * k + 1) * (X * s ^ (2 * (n - 1 - k)))
          = (x⁻¹ * x) * (s ^ ((2 * k + 1 : ℕ) : ℤ) * s ^ ((1 : ℤ) - 2 * n) *
              s ^ ((2 * (n - 1 - k) : ℕ) : ℤ)) := by
            rw [hX, zpow_natCast, zpow_natCast]; ring
        _ = 1 := by
            rw [inv_mul_cancel₀ hx, ← zpow_add₀ hs, ← zpow_add₀ hs, e, zpow_zero, one_mul]
    linear_combination -hab
  have hr : ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * (n - 1 - k))) =
      ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * k)) :=
    Finset.prod_range_reflect (fun k => 1 + X * s ^ (2 * k)) n
  have hC : ∏ k ∈ Finset.range n, (x⁻¹ * s ^ (2 * k + 1)) = x⁻¹ ^ n * s ^ (n ^ 2) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_pow_eq_pow_sum, finTriple_sum_odd]
  have hsplit : ∏ k ∈ Finset.range (2 * n), (1 + X * s ^ (2 * k)) =
      (∏ k ∈ Finset.range n, (1 + X * s ^ (2 * k))) *
        ∏ k ∈ Finset.range n, (1 + X * s ^ (2 * (n + k))) := by
    rw [two_mul, Finset.prod_range_add]
  rw [Finset.prod_mul_distrib, Finset.prod_congr rfl ha, Finset.prod_congr rfl hb,
    Finset.prod_mul_distrib, hr, hC]
  calc _ = x⁻¹ ^ n * s ^ (n ^ 2) * ∏ k ∈ Finset.range (2 * n), (1 + X * s ^ (2 * k)) := by
        rw [hsplit]; ring
    _ = x⁻¹ ^ n * s ^ (n ^ 2) * ∑ k ∈ Finset.range (2 * n + 1),
          qBinom (s ^ 2) (2 * n) k * s ^ (k * (k - 1)) * X ^ k := by
        rw [GlobalTheory.T.prod_range_one_add_mul_pow_two_mul_eq_sum_qBinom s X hs1 (2 * n)]
    _ = ∑ k ∈ Finset.range (2 * n + 1),
          finCoeff (s ^ 2) n ((k : ℤ) - n) * (x ^ ((k : ℤ) - n) * s ^ (((k : ℤ) - n) ^ 2)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        exact finTriple_term s x hs hx n k (by omega)
    _ = _ := by
        refine Finset.sum_nbij' (fun k : ℕ => (k : ℤ) - n) (fun j : ℤ => (j + n).toNat)
          ?_ ?_ ?_ ?_ ?_
        · intro a ha; simp only [Finset.mem_coe, Finset.mem_range] at ha
          simp only [Finset.mem_coe, Finset.mem_Icc]; omega
        · intro a ha; simp only [Finset.mem_coe, Finset.mem_Icc] at ha
          simp only [Finset.mem_coe, Finset.mem_range]; omega
        · intro a _; omega
        · intro a ha; simp only [Finset.mem_coe, Finset.mem_Icc] at ha
          omega
        · intro a _; rfl

end GlobalTheory.JacobiTriple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleProductLimit
section
open Complex
open scoped Real

namespace GlobalTheory.JacobiTriple

theorem tendsto_finCoeff_sum_jacobiTheta₂ : ∀ (τ : ℂ) (z : ℂ), 0 < τ.im →
    Filter.Tendsto (fun n : ℕ => ∑ j ∈ Finset.Icc (-(n : ℤ)) n,
      GlobalTheory.JacobiTriple.finCoeff (cexp (π * I * τ) ^ 2) n j * jacobiTheta₂_term j z τ)
      Filter.atTop (nhds (jacobiTheta₂ z τ * (GlobalTheory.JacobiTriple.qPochInf (cexp (π * I * τ) ^ 2))⁻¹)) := by
  intro τ z hτ
  set t := cexp (π * I * τ) ^ 2 with ht
  have hs : ‖cexp (π * I * τ)‖ < 1 := norm_exp_pi_I_lt_one τ hτ
  have ht1 : ‖t‖ < 1 := by
    rw [ht, norm_pow]
    nlinarith [norm_nonneg (cexp (π * I * τ))]
  obtain ⟨hlim, C, hC⟩ := GlobalTheory.T.jacobiTripleFiniteCoeff_tendsto_and_bounded t ht1
  have hsum : Summable (fun j : ℤ => C * ‖jacobiTheta₂_term j z τ‖) :=
    ((summable_jacobiTheta₂_term_iff z τ).2 hτ).norm.mul_left C
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
    (f := fun (n : ℕ) (j : ℤ) => finCoeff t n j * jacobiTheta₂_term j z τ)
    (g := fun j => jacobiTheta₂_term j z τ * (qPochInf t)⁻¹) hsum
    (fun j => by
      have := (hlim j).mul_const (jacobiTheta₂_term j z τ)
      simpa [mul_comm] using this)
    (Filter.Eventually.of_forall fun n j => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC n j) (norm_nonneg _))
  rw [tsum_mul_right] at hT
  refine hT.congr (fun n => ?_)
  apply tsum_eq_sum
  intro j hj
  have : ¬ j.natAbs ≤ n := by
    intro h
    apply hj
    rw [Finset.mem_Icc]
    omega
  simp [finCoeff, this]

end GlobalTheory.JacobiTriple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetsAreBoundedMeasureMomentsOfChartCoeffBoundStatement
section
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetsAreBoundedMeasureMoments_of_chart_coeff_bound : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ), Differentiable ℂ G → Bd 1 (hat ι (C ω * logS) G) → MomInt ι (fun _ : Unit => ι.symm ω) G := by
  first | exact @GlobalTheory.MomOneAmice.momInt_of_bd_hat | exact GlobalTheory.MomOneAmice.momInt_of_bd_hat | (intros; apply GlobalTheory.MomOneAmice.momInt_of_bd_hat <;> assumption)
end

