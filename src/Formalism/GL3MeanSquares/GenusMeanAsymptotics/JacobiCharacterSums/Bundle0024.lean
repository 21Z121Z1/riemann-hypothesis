import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0017
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0018
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0016
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0006
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0020
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplLoc

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHLocalB
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

lemma dhl_geom (t : ℝ) (z : ℂ) (hz : ‖z - ((26 / 25 : ℂ) + t * I)‖ ≤ 12 / 25) :
    1 / 2 ≤ z.re ∧ 1 + ‖z‖ ≤ 2 * (|t| + 2) := by
  have hre : ((26 / 25 : ℂ) + t * I).re = 26 / 25 := by
    simp
  have h1 := abs_re_le_norm (z - ((26 / 25 : ℂ) + t * I))
  rw [sub_re, hre] at h1
  have hn : ‖((26 / 25 : ℂ) + t * I)‖ ≤ 26 / 25 + |t| := by
    calc ‖((26 / 25 : ℂ) + t * I)‖ ≤ ‖(26 / 25 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 26 / 25 + |t| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        norm_num
  refine ⟨?_, ?_⟩
  · have := (abs_le.mp (h1.trans hz)).1; linarith
  · have := norm_sub_norm_le z ((26 / 25 : ℂ) + t * I)
    linarith [abs_nonneg t]

lemma dhl_core (hCau : DHCauchy) (f : ℂ → ℂ) (t K X : ℝ) (hK : 1 ≤ K) (hX : 3 ≤ X)
    (hf : Differentiable ℂ f) (hf0 : f ((26 / 25 : ℂ) + t * I) ≠ 0)
    (hB : ∀ z, ‖z - ((26 / 25 : ℂ) + t * I)‖ ≤ 12 / 25 →
      ‖f z‖ ≤ K * X ^ 2 * ‖f ((26 / 25 : ℂ) + t * I)‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (‖ρ - ((26 / 25 : ℂ) + t * I)‖ ≤ 4 / 25 ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ 150 * (Real.log K + 2) * Real.log X ∧
      ∀ (k : ℕ) (s : ℂ), ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 → f s ≠ 0 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z => -(deriv f z / f z)) s
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤
          150 * (Real.log K + 2) * Real.log X * 25 ^ k := by
  have hB1 : 1 ≤ K * X ^ 2 := by nlinarith
  obtain ⟨Z, m, hZ, hm, hsum, hexp⟩ := hCau f ((26 / 25 : ℂ) + t * I) (12 / 25) (K * X ^ 2)
    (by norm_num) hB1 hf.differentiableOn hf0
    (fun z hz => hB z (by rwa [Metric.mem_closedBall, dist_eq] at hz))
  have hlog := dhl_log K X hK hX
  have hlog0 : 0 ≤ Real.log (K * X ^ 2) := Real.log_nonneg hB1
  refine ⟨Z, m, ?_, hm, ?_, ?_⟩
  · intro ρ
    rw [hZ ρ, Metric.mem_closedBall, dist_eq]
    norm_num
  · refine hsum.trans ?_
    have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · intro k s hs hfs
    have := hexp k s (by rw [Metric.mem_closedBall, dist_eq]; norm_num; linarith) hfs
    refine this.trans ?_
    have e : (72 * Real.log (K * X ^ 2) / (12 / 25) * (12 / (12 / 25)) ^ k : ℝ)
        = 150 * Real.log (K * X ^ 2) * 25 ^ k := by
      norm_num; ring
    rw [e]
    have : (0 : ℝ) < 25 ^ k := by positivity
    nlinarith

lemma dhl_z0re (t : ℝ) : ((26 / 25 : ℂ) + t * I).re = 26 / 25 := by
  simp

lemma dhl_inv (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ) :
    1 ≤ 26 * ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by
  have h := inverseBound M ψ ((26 / 25 : ℂ) + t * I) (by rw [dhl_z0re]; norm_num)
  rw [dhl_z0re] at h
  have hne : DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ
      (Or.inr (by intro h; have := congrArg Complex.re h; rw [dhl_z0re] at this; norm_num at this))
      (by rw [dhl_z0re]; norm_num)
  have hpos : 0 < ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := norm_pos_iff.mpr hne
  rw [inv_le_comm₀ hpos (by norm_num)] at h
  norm_num at h
  linarith

def DHLocalAt (C : ℝ) (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ) : Prop :=
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (‖ρ - ((26 / 25 : ℂ) + t * I)‖ ≤ 4 / 25 ∧ IsLZero ψ ρ)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, ρ.re < 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ C * Real.log ((M : ℝ) * (|t| + 2)) ∧
      ∀ (k : ℕ) (s : ℂ), 1 < s.re → ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD ψ) s
            - (if ψ = 1 then 1 / (s - 1) ^ (k + 1) else 0)
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤ C * Real.log ((M : ℝ) * (|t| + 2)) * 25 ^ k

lemma dhl_X (M : ℕ) (t : ℝ) (hM : 3 ≤ M) : 3 ≤ (M : ℝ) * (|t| + 2) := by
  have h3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith [abs_nonneg t]

lemma dhl_nontriv (hCau : DHCauchy) (C0 K : ℝ)
    (hC0 : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖DirichletCharacter.LFunction χ s‖ ≤ C0 * q * (1 + ‖s‖))
    (hK1 : 1 ≤ K) (hK : 52 * C0 ≤ K) (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (hψ : ψ ≠ 1)
    (t : ℝ) (hM : 3 ≤ M) : DHLocalAt (150 * (Real.log K + 2)) M ψ t := by
  have hX := dhl_X M t hM
  have h3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hinv := dhl_inv M ψ t
  have hf0 : DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hinv; norm_num at hinv
  obtain ⟨Z, m, hZ, hm, hsum, hexp⟩ := dhl_core hCau (DirichletCharacter.LFunction ψ) t K
    ((M : ℝ) * (|t| + 2)) hK1 hX (DirichletCharacter.differentiable_LFunction hψ) hf0 (by
      intro z hz
      obtain ⟨hre, hn⟩ := dhl_geom t z hz
      have h1 := hC0 M ψ hψ z hre
      have hz0 := norm_nonneg z
      have ht := abs_nonneg t
      calc ‖DirichletCharacter.LFunction ψ z‖ ≤ C0 * M * (1 + ‖z‖) := h1
        _ ≤ (K / 52) * M * (1 + ‖z‖) := by
            have : C0 ≤ K / 52 := by linarith
            gcongr
        _ ≤ (K / 52) * M * (2 * (|t| + 2)) := by gcongr
        _ = K * ((M : ℝ) * (|t| + 2)) * (1 / 26) := by ring
        _ ≤ K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by
            have hXX : (M : ℝ) * (|t| + 2) ≤ ((M : ℝ) * (|t| + 2)) ^ 2 := by nlinarith
            have : (1 / 26 : ℝ) ≤ ‖DirichletCharacter.LFunction ψ ((26 / 25 : ℂ) + t * I)‖ := by linarith
            gcongr)
  refine ⟨Z, m, ?_, hm, ?_, hsum, ?_⟩
  · intro ρ
    rw [hZ ρ]
    exact and_congr_right (fun _ => ⟨fun h => ⟨Or.inl hψ, h⟩, fun h => h.2⟩)
  · intro ρ hρ
    by_contra hcon
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) (not_lt.mp hcon)
      ((hZ ρ).mp hρ).2
  · intro k s hs1 hs
    have h := hexp k s hs (DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ) hs1.le)
    rw [if_neg hψ, sub_zero]
    exact h

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrimeA
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation ComplexOrder

def dhprC {M : ℕ} (χ₁ : DirichletCharacter ℂ M) (n : ℕ) : ℝ :=
  ((1 : DirichletCharacter ℂ M) (n : ZMod M)).re + (χ₁ (n : ZMod M)).re

lemma dhpr_hasSum {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (k : ℕ) {σ : ℝ}
    (hσ : 1 < σ) :
    HasSum (fun n : ℕ => (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n)
      ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  have h1 := dhPos_hasSum (1 : DirichletCharacter ℂ M) k hs
  have h2 := dhPos_hasSum χ₁ k hs
  have h3 := h1.add h2
  rw [show ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
      + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re =
      ((-1 : ℂ) ^ k * iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)).re +
      ((-1 : ℂ) ^ k * iteratedDeriv k (negLD χ₁) (σ : ℂ)).re by rw [mul_add, Complex.add_re]]
  convert h3 using 1
  funext n
  have hiter : ∀ (f : ℕ → ℂ) (j m : ℕ), (LSeries.logMul^[j] f) m = (Complex.log m) ^ j * f m := by
    intro f j
    induction j with
    | zero => intro m; simp
    | succ j ih =>
      intro m
      rw [Function.iterate_succ_apply', LSeries.logMul, ih]
      ring
  by_cases hn : n = 0
  · subst hn
    simp [LSeries.term]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, hiter, hiter]
  simp only [Pi.mul_apply]
  have hn' : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; rfl
  rw [hn', ← Complex.ofReal_log (Nat.cast_nonneg _), ← Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.ofReal_pow]
  simp only [Complex.div_ofReal_re, Complex.re_ofReal_mul, Complex.re_mul_ofReal]
  unfold dhprC
  ring

lemma dhpr_C_bounds {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1)
    (n : ℕ) : 0 ≤ dhprC χ₁ n ∧ dhprC χ₁ n ≤ 2 := by
  unfold dhprC
  by_cases hu : IsUnit (n : ZMod M)
  · have h2 : χ₁ (n : ZMod M) ^ 2 = 1 := by
      have e := congrArg (fun ψ : DirichletCharacter ℂ M => ψ hu.unit) h1
      simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at e
      simpa using e
    have h3 : χ₁ (n : ZMod M) = 1 ∨ χ₁ (n : ZMod M) = -1 := mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)
    rw [MulChar.one_apply hu]
    rcases h3 with h3 | h3 <;> rw [h3] <;> norm_num
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]
    norm_num

lemma dhpr_r_nonneg {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1)
    (n : ℕ) : 0 ≤ (zetaMul χ₁ n).re := by
  exact (Complex.nonneg_iff.mp (DirichletCharacter.zetaMul_nonneg h1 n)).1

set_option backward.isDefEq.respectTransparency.types false in
lemma dhpr_zetaMul_eq_sum {M : ℕ} (χ : DirichletCharacter ℂ M) (n : ℕ) :
    zetaMul χ n = ∑ d ∈ n.divisors, χ (d : ZMod M) := by
  rw [DirichletCharacter.zetaMul, ArithmeticFunction.coe_zeta_mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  first
    | exact if_neg hd0
    | simp only [LSeries.toArithmeticFunction, ArithmeticFunction.coe_mk, if_neg hd0]

lemma dhpr_zetaMul_prime_pow {M : ℕ} (χ : DirichletCharacter ℂ M) {p : ℕ} (hp : p.Prime)
    (a : ℕ) : zetaMul χ (p ^ a) = ∑ i ∈ range (a + 1), χ (p : ZMod M) ^ i := by
  rw [dhpr_zetaMul_eq_sum, Nat.divisors_prime_pow hp, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i _
  simp [Nat.cast_pow, map_pow]

lemma dhpr_coef_le {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1)
    (n : ℕ) : Λ n * dhprC χ₁ n ≤ 2 * Real.log n * (zetaMul χ₁ n).re := by
  have hr0 := dhpr_r_nonneg χ₁ h1 n
  have hl := Real.log_natCast_nonneg n
  by_cases hΛ : Λ n = 0
  · rw [hΛ, zero_mul]
    exact mul_nonneg (mul_nonneg (by norm_num) hl) hr0
  obtain ⟨p, a, hp', ha, rfl⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
  have hp : p.Prime := Nat.prime_iff.mpr hp'
  have ha0 : a ≠ 0 := Nat.pos_iff_ne_zero.mp ha
  have hΛp : Λ (p ^ a) = Real.log p := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow ha0, ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlog : Real.log ((p ^ a : ℕ) : ℝ) = a * Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]
  have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha

  have key : dhprC χ₁ (p ^ a) ≤ 2 * (zetaMul χ₁ (p ^ a)).re := by
    unfold dhprC
    rw [dhpr_zetaMul_prime_pow χ₁ hp a]
    by_cases hu : IsUnit (p : ZMod M)
    · have hua : IsUnit ((p ^ a : ℕ) : ZMod M) := by rw [Nat.cast_pow]; exact hu.pow a
      have h2 : χ₁ (p : ZMod M) ^ 2 = 1 := by
        have e := congrArg (fun ψ : DirichletCharacter ℂ M => ψ hu.unit) h1
        simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at e
        simpa using e
      have h3 : χ₁ (p : ZMod M) = 1 ∨ χ₁ (p : ZMod M) = -1 := mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)
      rw [MulChar.one_apply hua, Nat.cast_pow, map_pow]
      rcases h3 with h3 | h3
      · rw [h3]
        simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        simp
        linarith
      · rw [h3]
        have hsum : ∀ b : ℕ, 2 * ∑ i ∈ range (b + 1), ((-1 : ℂ)) ^ i = 1 + (-1) ^ b := by
          intro b
          induction b with
          | zero => norm_num
          | succ b ih =>
            rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
            ring
        have hre := congrArg Complex.re (hsum a)
        simp only [Complex.add_re, Complex.one_re] at hre
        have h2re : (2 * ∑ i ∈ range (a + 1), ((-1 : ℂ)) ^ i).re = 2 * (∑ i ∈ range (a + 1), ((-1 : ℂ)) ^ i).re := by
          simp [Complex.mul_re] <;> split_ifs <;> simp
        rw [h2re] at hre
        simp only [Complex.one_re]
        linarith
    · have hua : ¬ IsUnit ((p ^ a : ℕ) : ZMod M) := by
        rw [Nat.cast_pow]
        exact fun h => hu ((isUnit_pow_iff ha0).mp h)
      rw [MulChar.map_nonunit _ hua, MulChar.map_nonunit _ hua]
      have := (Complex.nonneg_iff.mp (DirichletCharacter.zetaMul_nonneg h1 (p ^ a))).1
      rw [dhpr_zetaMul_prime_pow χ₁ hp a] at this
      simp only [Complex.zero_re, add_zero]
      linarith
  rw [hΛp, hlog]
  calc Real.log p * dhprC χ₁ (p ^ a) ≤ Real.log p * (2 * (zetaMul χ₁ (p ^ a)).re) :=
        mul_le_mul_of_nonneg_left key hlp
    _ ≤ 2 * (a * Real.log p) * (zetaMul χ₁ (p ^ a)).re := by
        have hrr := dhpr_r_nonneg χ₁ h1 (p ^ a)
        nlinarith [mul_nonneg hlp hrr]

lemma dhpr_term_nonneg {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1)
    (k n : ℕ) (σ : ℝ) : 0 ≤ (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n := by
  have h1' := (dhpr_C_bounds χ₁ h1 n).1
  have hl := Real.log_natCast_nonneg n
  have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have hn : 0 ≤ (n : ℝ) ^ σ := Real.rpow_nonneg (Nat.cast_nonneg n) σ
  exact mul_nonneg (mul_nonneg (pow_nonneg hl k) (div_nonneg hΛ hn)) h1'

lemma dhpr_term_le_r {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1)
    (k n : ℕ) (σ : ℝ) :
    (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n ≤
      2 * (Real.log n) ^ (k + 1) * (zetaMul χ₁ n).re / (n : ℝ) ^ σ := by
  have hc := dhpr_coef_le χ₁ h1 n
  have hl := Real.log_natCast_nonneg n
  have h0 : 0 ≤ Real.log n ^ k / (n : ℝ) ^ σ :=
    div_nonneg (pow_nonneg hl k) (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  calc Real.log n ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n = (Real.log n ^ k / (n : ℝ) ^ σ) * (Λ n * dhprC χ₁ n) := by
        ring
    _ ≤ (Real.log n ^ k / (n : ℝ) ^ σ) * (2 * Real.log n * (zetaMul χ₁ n).re) := mul_le_mul_of_nonneg_left hc h0
    _ = 2 * Real.log n ^ (k + 1) * (zetaMul χ₁ n).re / (n : ℝ) ^ σ := by ring

lemma dhpr_term_le_small {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1)
    (k n : ℕ) {σ : ℝ} (hσ : 1 ≤ σ) :
    (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n ≤ 2 * (Real.log n) ^ k * (Λ n / n) := by
  have hC := dhpr_C_bounds χ₁ h1 n
  have hl := Real.log_natCast_nonneg n
  have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  by_cases hn : n = 0
  · subst hn
    simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ σ := by
    have := Real.rpow_le_rpow_of_exponent_le hn1 hσ
    rwa [Real.rpow_one] at this
  have hd : Λ n / (n : ℝ) ^ σ ≤ Λ n / n := div_le_div_of_nonneg_left hΛ (by linarith) hpow
  have h0 : 0 ≤ Real.log n ^ k * (Λ n / n) := mul_nonneg (pow_nonneg hl k) (div_nonneg hΛ (Nat.cast_nonneg n))
  calc Real.log n ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n ≤ Real.log n ^ k * (Λ n / n) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd (pow_nonneg hl k)) hC.2 hC.1 h0
    _ = 2 * Real.log n ^ k * (Λ n / n) := by ring

lemma lfunction_one_le_of_siegel_zero : ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ),
    χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    1 - 1 / Real.log (3 * M) ≤ β₁ → β₁ < 1 →
    ‖DirichletCharacter.LFunction χ₁ 1‖ ≤ C * Real.log (3 * M) ^ 2 * (1 - β₁) := by
  obtain ⟨C, hC⟩ := lfunction_deriv_near_one
  refine ⟨max C 0, le_max_right _ _, fun M _ χ₁ β₁ hχ hz hβ hβ1 => ?_⟩
  have hd := DirichletCharacter.differentiable_LFunction hχ
  have hder : ∀ t ∈ Set.Icc β₁ 1,
      HasDerivWithinAt (fun t : ℝ => DirichletCharacter.LFunction χ₁ (t : ℂ))
        (deriv (DirichletCharacter.LFunction χ₁) (t : ℂ)) (Set.Icc β₁ 1) t :=
    fun t _ => ((hd (t : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hbd : ∀ t ∈ Set.Ico β₁ 1,
      ‖deriv (DirichletCharacter.LFunction χ₁) (t : ℂ)‖ ≤ max C 0 * Real.log (3 * M) ^ 2 := by
    intro t ht
    exact (hC M χ₁ hχ t (le_trans hβ ht.1) ht.2.le).trans (by gcongr; exact le_max_left _ _)
  have := norm_image_sub_le_of_norm_deriv_le_segment' hder hbd 1 ⟨hβ1.le, le_rfl⟩
  simp only [hz, sub_zero, ofReal_one] at this
  exact this

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplLocL
section
open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem ex_centre_re (t : ℝ) : ((101 / 100 : ℂ) + t * I).re = 101 / 100 := by
  simp only [add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, mul_zero, mul_one, sub_self]
  have : ((101 / 100 : ℂ)).re = 101 / 100 := by
    have h : (101 / 100 : ℂ) = ((101 / 100 : ℝ) : ℂ) := by push_cast; ring
    rw [h, ofReal_re]
  rw [this]; ring

theorem ex_centre_norm (t : ℝ) : ‖(101 / 100 : ℂ) + t * I‖ ≤ 101 / 100 + |t| := by
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(101 / 100 : ℂ)‖ = 101 / 100 := by
    have h : (101 / 100 : ℂ) = ((101 / 100 : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have h2 : ‖(t : ℂ) * I‖ = |t| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2]

theorem ex_centre_lower {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (t : ℝ) :
    1 / 10100 ≤ ‖exLF χ ((101 / 100 : ℂ) + t * I)‖ := by
  have hre := ex_centre_re t
  have h := exLF_lower χ ((101 / 100 : ℂ) + t * I) (by rw [hre]; norm_num)
  rw [hre] at h
  have h1 : (1 / 100 : ℝ) ≤ ‖(101 / 100 : ℂ) + t * I - 1‖ := by
    have h2 := Complex.abs_re_le_norm ((101 / 100 : ℂ) + t * I - 1)
    rw [sub_re, hre, one_re] at h2
    rw [abs_of_pos (by norm_num)] at h2
    linarith
  have h3 : (1 / 100 : ℝ) ≤ min 1 ‖(101 / 100 : ℂ) + t * I - 1‖ := le_min (by norm_num) h1
  have h4 : (1 / 100 : ℝ) * ((101 / 100 - 1) / (101 / 100)) ≤
      min 1 ‖(101 / 100 : ℂ) + t * I - 1‖ * ((101 / 100 - 1) / (101 / 100)) :=
    mul_le_mul_of_nonneg_right h3 (by norm_num)
  refine le_trans ?_ (h4.trans h)
  norm_num

theorem ex_log_bound (C0 : ℝ) (hC0 : 1 ≤ C0) (M : ℕ) (hM : 3 ≤ M) (t : ℝ) :
    1 ≤ C0 * M * (|t| + 3) ^ 2 * 10100 ∧
    0 ≤ Real.log (C0 * M * (|t| + 3) ^ 2 * 10100) ∧
    Real.log (C0 * M * (|t| + 3) ^ 2 * 10100) ≤
      (Real.log (C0 * 10100) + 3) * Real.log ((M : ℝ) * (|t| + 2)) := by
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have ht : 0 ≤ |t| := abs_nonneg t
  have hB1 : 1 ≤ C0 * M * (|t| + 3) ^ 2 * 10100 := by
    have h1 : 1 ≤ C0 * M := by nlinarith
    have h2 : 1 ≤ (|t| + 3) ^ 2 := by nlinarith
    have h3 : 1 ≤ C0 * M * (|t| + 3) ^ 2 := by nlinarith
    linarith
  refine ⟨hB1, Real.log_nonneg hB1, ?_⟩
  set X : ℝ := (M : ℝ) * (|t| + 2) with hX
  have hX6 : 6 ≤ X := by rw [hX]; nlinarith
  have hX0 : 0 < X := by linarith
  have hMX : (M : ℝ) ≤ X := by rw [hX]; nlinarith
  have htX : |t| + 3 ≤ X := by rw [hX]; nlinarith
  have hlogX : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9
    linarith
  have hK : 1 ≤ C0 * 10100 := by linarith
  have hK0 : 0 ≤ Real.log (C0 * 10100) := Real.log_nonneg hK
  have hle : C0 * M * (|t| + 3) ^ 2 * 10100 ≤ C0 * 10100 * X ^ 3 := by
    have h1 : (|t| + 3) ^ 2 ≤ X ^ 2 := by gcongr
    have h2 : (M : ℝ) * (|t| + 3) ^ 2 ≤ X * X ^ 2 := by
      apply mul_le_mul hMX h1 (by positivity) hX0.le
    have h3 : C0 * 10100 * ((M : ℝ) * (|t| + 3) ^ 2) ≤ C0 * 10100 * (X * X ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    calc C0 * M * (|t| + 3) ^ 2 * 10100 = C0 * 10100 * ((M : ℝ) * (|t| + 3) ^ 2) := by ring
      _ ≤ C0 * 10100 * (X * X ^ 2) := h3
      _ = C0 * 10100 * X ^ 3 := by ring
  have h5 : Real.log (C0 * M * (|t| + 3) ^ 2 * 10100) ≤ Real.log (C0 * 10100 * X ^ 3) :=
    Real.log_le_log (by linarith) hle
  have h6 : Real.log (C0 * 10100 * X ^ 3) = Real.log (C0 * 10100) + 3 * Real.log X := by
    rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
    push_cast; ring
  rw [h6] at h5
  nlinarith

theorem ex_local : ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (t : ℝ), 3 ≤ M →
    ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall ((101 / 100 : ℂ) + t * I) (2 / 15) ∧ exLF χ ρ = 0)) ∧
      ((∑ ρ ∈ Z, exOrd χ ρ : ℕ) : ℝ) ≤ C * Real.log ((M : ℝ) * (|t| + 2)) ∧
      ∀ s ∈ Metric.closedBall ((101 / 100 : ℂ) + t * I) (1 / 15), exLF χ s ≠ 0 →
        ‖deriv (exLF χ) s / exLF χ s - ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) / (s - ρ)‖ ≤
          C * Real.log ((M : ℝ) * (|t| + 2)) := by
  obtain ⟨C0, hC0, hG⟩ := exLF_growth
  have hK0 : 0 ≤ Real.log (C0 * 10100) := Real.log_nonneg (by linarith)
  refine ⟨180 * (Real.log (C0 * 10100) + 3), by linarith, ?_⟩
  intro M _ χ t hM
  obtain ⟨hB1, hB0, hBlog⟩ := ex_log_bound C0 hC0 M hM t
  set B : ℝ := C0 * M * (|t| + 3) ^ 2 * 10100 with hB
  set z₀ : ℂ := (101 / 100 : ℂ) + t * I with hz₀
  have hlow : 1 / 10100 ≤ ‖exLF χ z₀‖ := ex_centre_lower χ t
  have hne : exLF χ z₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hlow; norm_num at hlow
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hbound : ∀ z ∈ Metric.closedBall z₀ (2 / 5), ‖exLF χ z‖ ≤ B * ‖exLF χ z₀‖ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre : 1 / 2 ≤ z.re := by
      have h1 := Complex.abs_re_le_norm (z - z₀)
      rw [sub_re, hz₀, ex_centre_re t] at h1
      have h2 := (abs_le.1 (h1.trans hz)).1
      linarith
    have hn : ‖z‖ ≤ |t| + 2 := by
      have h1 : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
        have := norm_add_le (z - z₀) z₀
        rwa [sub_add_cancel] at this
      have h2 := ex_centre_norm t
      rw [← hz₀] at h2
      linarith
    have h3 : (1 + ‖z‖) ^ 2 ≤ (|t| + 3) ^ 2 := by
      have : 0 ≤ ‖z‖ := norm_nonneg z
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h4 : C0 * M * (1 + ‖z‖) ^ 2 ≤ C0 * M * (|t| + 3) ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg (by linarith) hM0)
    have h5 : B * (1 / 10100) ≤ B * ‖exLF χ z₀‖ := mul_le_mul_of_nonneg_left hlow (by linarith)
    have h6 : B * (1 / 10100) = C0 * M * (|t| + 3) ^ 2 := by rw [hB]; ring
    linarith [hG M χ z hre]
  obtain ⟨Z, hZ1, -, hZ3, hZ4⟩ := ex_landau_ord (exLF χ) z₀ (2 / 5) B (by norm_num) hB1
    (exLF_differentiable χ).differentiableOn hne hbound
  have e3 : (2 / 5 : ℝ) / 3 = 2 / 15 := by norm_num
  have e6 : (2 / 5 : ℝ) / 6 = 1 / 15 := by norm_num
  rw [e3] at hZ1
  rw [e6] at hZ4
  refine ⟨Z, hZ1, ?_, ?_⟩
  · have h2 : Real.log B / Real.log 2 ≤ 180 * Real.log B := by
      have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have h3 : ((∑ ρ ∈ Z, exOrd χ ρ : ℕ) : ℝ) ≤ Real.log B / Real.log 2 := hZ3
    calc ((∑ ρ ∈ Z, exOrd χ ρ : ℕ) : ℝ) ≤ 180 * Real.log B := h3.trans h2
      _ ≤ 180 * (Real.log (C0 * 10100) + 3) * Real.log ((M : ℝ) * (|t| + 2)) := by linarith
  · intro s hs hs0
    have h1 : ‖deriv (exLF χ) s / exLF χ s - ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) / (s - ρ)‖ ≤
        72 * Real.log B / (2 / 5) := hZ4 s hs hs0
    have h2 : 72 * Real.log B / (2 / 5) = 180 * Real.log B := by ring
    rw [h2] at h1
    linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

