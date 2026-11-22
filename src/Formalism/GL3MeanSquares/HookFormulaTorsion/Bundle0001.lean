import Mathlib
import Formalism.GL3MeanSquares.ConcavityEquidistribution
import Formalism.LogVandermondeBounds.LogVandermondeProofs.GammaIntegralPolynomialBound
import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.BlockOperatorNormBound
section
namespace Formalism.HermitianLattices.TraceIntegrality

open MeasureTheory Finset

private lemma fock_real_integral (Om : ℝ) (hOm : 0 < Om) (k : ℕ) :
    ∫ z : ℂ, ‖z‖ ^ k * Real.exp (-‖z‖ ^ 2 / Om) =
      Real.pi * Om ^ ((k : ℝ) / 2 + 1) * Real.Gamma ((k : ℝ) / 2 + 1) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := k) (b := Om⁻¹)
    (by norm_num) (by linarith) (inv_pos.mpr hOm)
  have e : ∀ z : ℂ, ‖z‖ ^ (k : ℝ) * Real.exp (-Om⁻¹ * ‖z‖ ^ (2 : ℝ)) =
      ‖z‖ ^ k * Real.exp (-‖z‖ ^ 2 / Om) := by
    intro z
    rw [Real.rpow_natCast, Real.rpow_two]
    congr 2
    field_simp
  simp_rw [e] at h
  rw [h, Real.inv_rpow hOm.le, ← Real.rpow_neg hOm.le]
  have h1 : -(-((k : ℝ) + 2) / 2) = (k : ℝ) / 2 + 1 := by ring
  have h2 : ((k : ℝ) + 2) / 2 = (k : ℝ) / 2 + 1 := by ring
  rw [h1, h2]
  ring

private lemma fock_real_integrable (Om : ℝ) (hOm : 0 < Om) (k : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ k * Real.exp (-‖z‖ ^ 2 / Om)) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  by_contra hn
  have h0 := integral_undef hn
  rw [fock_real_integral Om hOm k] at h0
  have : 0 < Real.pi * Om ^ ((k : ℝ) / 2 + 1) * Real.Gamma ((k : ℝ) / 2 + 1) := by
    have := Real.Gamma_pos_of_pos (s := (k : ℝ) / 2 + 1) (by positivity)
    have := Real.rpow_pos_of_pos hOm ((k : ℝ) / 2 + 1)
    have := Real.pi_pos
    positivity
  linarith

private lemma fock_integrable (Om : ℝ) (hOm : 0 < Om) (p q : ℕ) :
    Integrable
      (fun z : ℂ => z ^ p * (starRingEnd ℂ z) ^ q * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ)) := by
  refine (fock_real_integrable Om hOm (p + q)).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · refine Filter.Eventually.of_forall (fun z => ?_)
    rw [norm_mul, norm_mul, norm_pow, norm_pow, RCLike.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_add]

private lemma fock_rotate (Om : ℝ) (p q : ℕ) (c : Circle) :
    ∫ z : ℂ, z ^ p * (starRingEnd ℂ z) ^ q * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ) =
      ((c : ℂ) ^ p * (starRingEnd ℂ (c : ℂ)) ^ q) *
        ∫ z : ℂ, z ^ p * (starRingEnd ℂ z) ^ q * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ) := by
  have hmp : MeasurePreserving (rotation c) (volume : Measure ℂ) volume :=
    (rotation c).measurePreserving
  have h := hmp.integral_comp (rotation c).toHomeomorph.measurableEmbedding
    (fun z : ℂ => z ^ p * (starRingEnd ℂ z) ^ q * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ))
  conv_lhs => rw [← h]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [rotation_apply, map_mul, norm_mul, Circle.norm_coe, one_mul, mul_pow]
  ring

theorem fock_monomial_orthogonality : FockMonomialOrthogonality := by
  intro Om p q hOm
  refine ⟨fock_integrable Om hOm p q, ?_⟩
  split_ifs with hpq
  · subst hpq
    have e : ∀ z : ℂ, z ^ p * (starRingEnd ℂ z) ^ p * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ) =
        ((‖z‖ ^ (2 * p) * Real.exp (-‖z‖ ^ 2 / Om) : ℝ) : ℂ) := by
      intro z
      rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rw [pow_mul]
    simp_rw [e]
    rw [integral_complex_ofReal, fock_real_integral Om hOm (2 * p)]
    congr 1
    have h1 : ((2 * p : ℕ) : ℝ) / 2 + 1 = (p : ℝ) + 1 := by push_cast; ring
    rw [h1, Real.Gamma_nat_eq_factorial, Real.rpow_add hOm, Real.rpow_natCast, Real.rpow_one]
    ring
  ·
    have hd : ((p : ℝ) - q) ≠ 0 := by
      intro h
      apply hpq
      have : (p : ℝ) = q := by linarith
      exact_mod_cast this
    set θ : ℝ := Real.pi / ((p : ℝ) - q) with hθ
    have hrot := fock_rotate Om p q (Circle.exp θ)
    have hc : ((Circle.exp θ : Circle) : ℂ) ^ p * (starRingEnd ℂ ((Circle.exp θ : Circle) : ℂ)) ^ q
        = -1 := by
      rw [Circle.coe_exp, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
        ← Complex.exp_add]
      have : (p : ℂ) * ((θ : ℂ) * Complex.I) + (q : ℂ) * (starRingEnd ℂ) ((θ : ℂ) * Complex.I)
          = (Real.pi : ℂ) * Complex.I := by
        rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
        have hd' : ((p : ℂ) - q) ≠ 0 := by exact_mod_cast hd
        rw [hθ]
        push_cast
        field_simp
        ring
      rw [this, Complex.exp_pi_mul_I]
    rw [hc] at hrot
    have h2 : (2 : ℂ) * ∫ z : ℂ, z ^ p * (starRingEnd ℂ z) ^ q *
        (Real.exp (-‖z‖ ^ 2 / Om) : ℂ) = 0 := by
      linear_combination hrot
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

theorem product_of_jets : JetsProductBound := by
  intro ι _ n g₀ Th S2 hg hS2 h
  set e : ι → ℝ := fun τ => if n τ = 0 then (1 : ℝ) else min 1 ((g₀ : ℝ) / n τ) with he
  have hg0 : (0 : ℝ) < g₀ := by exact_mod_cast hg
  have hepos : ∀ τ, 0 < e τ := by
    intro τ
    simp only [he]
    split_ifs with h0
    · exact one_pos
    · have : (0 : ℝ) < n τ := by exact_mod_cast Nat.pos_of_ne_zero h0
      exact lt_min one_pos (div_pos hg0 this)
  have hP : 0 < ∏ τ, (1 + e τ) ^ (n τ + g₀) :=
    Finset.prod_pos (fun τ _ => pow_pos (by linarith [hepos τ]) _)
  have h' : Th * (∏ τ, (1 + e τ) ^ (n τ + g₀))⁻¹ ≤ S2 * ∏ τ, ((e τ) ^ g₀)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact h
  have h1 : Th ≤ S2 * (∏ τ, ((e τ) ^ g₀)⁻¹) * ∏ τ, (1 + e τ) ^ (n τ + g₀) := by
    rwa [← div_eq_mul_inv, div_le_iff₀ hP] at h'
  refine h1.trans ?_
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  refine mul_le_mul_of_nonneg_left ?_ hS2
  refine Finset.prod_le_prod (fun τ _ => ?_) (fun τ _ => ?_)
  · have := hepos τ
    positivity
  · exact Formalism.LogVandermondeBounds.flipTwoThree.jet_exponential_bound (n τ) g₀ hg

theorem block_operator_norm_bound : BlockOperatorNormBound := by
  intro X X' V V' _ _ _ _ _ _ A φ β hβ
  have hφ : 0 ≤ ∑ x, ‖φ x‖ ^ 2 := Finset.sum_nonneg (fun x _ => by positivity)
  have h1 : ∑ x', ‖∑ x, A x' x (φ x)‖ ^ 2 ≤ (∑ x', ∑ x, ‖A x' x‖ ^ 2) * ∑ x, ‖φ x‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun x' _ => ?_)
    have h2 : ‖∑ x, A x' x (φ x)‖ ≤ ∑ x, ‖A x' x‖ * ‖φ x‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun x _ => (A x' x).le_opNorm (φ x)))
    calc ‖∑ x, A x' x (φ x)‖ ^ 2 ≤ (∑ x, ‖A x' x‖ * ‖φ x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ ≤ (∑ x, ‖A x' x‖ ^ 2) * ∑ x, ‖φ x‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  refine ⟨h1, h1.trans (mul_le_mul_of_nonneg_right ?_ hφ)⟩
  calc ∑ x', ∑ x, ‖A x' x‖ ^ 2 ≤ ∑ _x' : X', ∑ _x : X, β :=
        Finset.sum_le_sum (fun x' _ => Finset.sum_le_sum (fun x _ => hβ x' x))
    _ = (Fintype.card X' : ℝ) * Fintype.card X * β := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Formalism.HermitianLattices.TraceIntegrality
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.MinkowskiDivisorBound
section
namespace Formalism.HermitianLattices.TraceIntegrality

open Finset

private theorem mink_term (n p i : ℕ) (hp : 2 ≤ p) :
    n / (p ^ i * (p - 1)) ≤ 2 * n / p ^ (1 + i) := by
  have hpos : 0 < p ^ (1 + i) := Nat.pow_pos (by omega)
  rw [Nat.le_div_iff_mul_le hpos]
  have h1 : n / (p ^ i * (p - 1)) * (p ^ i * (p - 1)) ≤ n := Nat.div_mul_le_self _ _
  have h2 : p ≤ 2 * (p - 1) := by omega
  calc n / (p ^ i * (p - 1)) * p ^ (1 + i)
      = n / (p ^ i * (p - 1)) * p ^ i * p := by rw [pow_add, pow_one]; ring
    _ ≤ n / (p ^ i * (p - 1)) * p ^ i * (2 * (p - 1)) := Nat.mul_le_mul_left _ h2
    _ = 2 * (n / (p ^ i * (p - 1)) * (p ^ i * (p - 1))) := by ring
    _ ≤ 2 * n := Nat.mul_le_mul_left _ h1

theorem minkowski_divisor_bound : Minkowski_div := by
  intro n p hp
  have : Fact p.Prime := ⟨hp⟩
  have hlog : Nat.log p (2 * n) < 2 * n + 2 :=
    lt_of_le_of_lt (Nat.log_le_self _ _) (by omega)
  rw [padicValNat_factorial hlog]
  calc ∑ i ∈ range (n + 1), n / (p ^ i * (p - 1))
      ≤ ∑ i ∈ range (n + 1), 2 * n / p ^ (1 + i) :=
        Finset.sum_le_sum (fun i _ => mink_term n p i hp.two_le)
    _ = ∑ i ∈ Ico 1 (n + 2), 2 * n / p ^ i := by
        rw [Finset.sum_Ico_eq_sum_range]; rfl
    _ ≤ ∑ i ∈ Ico 1 (2 * n + 2), 2 * n / p ^ i := by
        apply Finset.sum_le_sum_of_subset
        apply Finset.Ico_subset_Ico le_rfl
        omega

theorem minkowski_log_bound : Minkowski_log := by
  refine ⟨12, ?_⟩
  intro M hM
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hfac : (((4 * M).factorial : ℕ) : ℝ) ≤ ((4 * M : ℕ) : ℝ) ^ (4 * M) := by
    exact_mod_cast Nat.factorial_le_pow (4 * M)
  have hfpos : (0 : ℝ) < ((4 * M).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have h1 : Real.log ((4 * M).factorial : ℝ) ≤ Real.log (((4 * M : ℕ) : ℝ) ^ (4 * M)) :=
    Real.log_le_log hfpos hfac
  have h2 : Real.log (((4 * M : ℕ) : ℝ) ^ (4 * M)) = (4 * (M : ℝ)) * (Real.log 4 + Real.log M) := by
    rw [Real.log_pow]
    push_cast
    rw [Real.log_mul (by norm_num) hM0.ne']
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h5 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hMr
  have h6 : Real.log 4 + Real.log M ≤ 3 * Real.log M := by linarith
  calc Real.log ((4 * M).factorial : ℝ) ≤ (4 * (M : ℝ)) * (Real.log 4 + Real.log M) := by
        rw [← h2]; exact h1
    _ ≤ (4 * (M : ℝ)) * (3 * Real.log M) := mul_le_mul_of_nonneg_left h6 (by linarith)
    _ = 12 * M * Real.log M := by ring

theorem moduli_arithmetic_bound : Ms_arith := by
  intro C₀ hC₀
  refine ⟨8 * Real.log C₀ + 31 + C₀, ?_⟩
  intro f N v T L logg R2 logh hf hN hv hT hL hg hlf hlN hlv hR2 hh
  have hfr : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hC0' : C₀ ≠ 0 := by positivity
  have hf' : (f : ℝ) ≠ 0 := by positivity
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hv' : v ≠ 0 := by positivity
  have hT' : T ≠ 0 := by positivity
  have hlogR : Real.log R2 = Real.log C₀ + Real.log f + 2 * Real.log N + 2 * Real.log v
      + 2 * Real.log T := by
    rw [hR2, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul hC0' hf', Real.log_pow, Real.log_pow,
      Real.log_pow]
    push_cast; ring
  have hR2' : R2 ≠ 0 := by rw [hR2]; positivity
  have hlogCR : Real.log (C₀ * R2) = Real.log C₀ + Real.log R2 := Real.log_mul hC0' hR2'
  set c := Real.log C₀ with hcdef
  set lT := Real.log T with hlTdef
  set X := L + lT + logg with hX
  clear_value X c lT
  have hX1 : 1 ≤ X := by linarith
  have hcX : c ≤ c * X := by nlinarith
  have hA : Real.log R2 ≤ (c + 5) * X := by
    have : Real.log R2 ≤ c + 5 * X := by rw [hlogR]; linarith
    linarith
  have hB : Real.log (C₀ * R2) ≤ (2 * c + 5) * X := by
    rw [hlogCR]; linarith
  have hfN2 : 0 ≤ (f : ℝ) * (N : ℝ) ^ 2 := by positivity
  have hP : 0 ≤ (f : ℝ) * (N : ℝ) ^ 2 * X := by positivity

  have t1 : (N : ℝ) ^ 2 * (2 * f * Real.log (C₀ * R2)) ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (2 * (2 * c + 5)) := by
    have := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 2 * ((f : ℝ) * (N : ℝ) ^ 2))
    linarith

  have t2 : 4 * f * N * ((N : ℝ) + 1) * (Real.log R2 / 2) ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (4 * (c + 5)) := by
    have h1 : 4 * f * N * ((N : ℝ) + 1) * (Real.log R2 / 2)
        ≤ 4 * f * N * ((N : ℝ) + 1) * ((c + 5) * X / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (N : ℝ) * ((N : ℝ) + 1) ≤ 2 * (N : ℝ) ^ 2 := by nlinarith
    have h3 : 0 ≤ 2 * (f : ℝ) * ((c + 5) * X) := by positivity
    have h4 := mul_le_mul_of_nonneg_left h2 h3
    linarith

  have t3 : (f : ℝ) * N * lT ≤ (f : ℝ) * (N : ℝ) ^ 2 * lT := by
    have h2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (f : ℝ) * lT)
    linarith
  have t3' : (f : ℝ) * (N : ℝ) ^ 2 * lT ≤ (f : ℝ) * (N : ℝ) ^ 2 * X :=
    mul_le_mul_of_nonneg_left (by linarith) hfN2
  have t4 : C₀ * f * (N : ℝ) ^ 2 * logg ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * C₀ := by
    have := mul_le_mul_of_nonneg_left (by linarith : logg ≤ X)
      (by positivity : 0 ≤ C₀ * ((f : ℝ) * (N : ℝ) ^ 2))
    linarith
  have hsum : logh ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (2 * (2 * c + 5)) + (f : ℝ) * (N : ℝ) ^ 2 * X * (4 * (c + 5))
        + ((f : ℝ) * (N : ℝ) ^ 2 * X + (f : ℝ) * (N : ℝ) ^ 2 * X * C₀) := by linarith
  calc logh ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (2 * (2 * c + 5)) + (f : ℝ) * (N : ℝ) ^ 2 * X * (4 * (c + 5))
        + ((f : ℝ) * (N : ℝ) ^ 2 * X + (f : ℝ) * (N : ℝ) ^ 2 * X * C₀) := hsum
    _ = (8 * c + 31 + C₀) * f * (N : ℝ) ^ 2 * X := by ring

end Formalism.HermitianLattices.TraceIntegrality
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.OrthogonalMinorBound
section
namespace Formalism.HermitianLattices.TraceIntegrality

open Finset Matrix
open scoped ComplexOrder

theorem am_gm_sum_lower_bound : AmGmSumLowerBound := by
  intro f v x hf hv hx hprod
  have h := Formalism.LogVandermondeBounds.flipTwoThree.amgm_period_lattice_bound f (2 * v ^ 2) x hf (by positivity) hx
    (by
      have e : (2 * (2 * v ^ 2)) ^ f = (2 * v) ^ (2 * f) := by
        rw [pow_mul]; congr 1; ring
      rw [e]; exact hprod)
  have e : (f : ℝ) / (2 * v) ^ 2 = ((f : ℝ) / (2 * v ^ 2)) / 2 := by
    field_simp
  rw [e]
  linarith

theorem concavity_equidistribution : ConcavityEquidistribution := by
  intro ι σ _ _ _ _ π c y B hfib hy hB
  classical
  have hcardσ : (Fintype.card σ : ℝ) = c * Fintype.card ι := by
    have h := Finset.card_eq_sum_card_fiberwise (f := π) (s := (univ : Finset σ))
      (t := (univ : Finset ι)) (fun _ _ => Finset.mem_coe.2 (mem_univ _))
    simp only [hfib, sum_const, smul_eq_mul, card_univ] at h
    rw [h]; push_cast; ring
  have hσpos : (0 : ℝ) < Fintype.card σ := by exact_mod_cast Fintype.card_pos
  have hc : (0 : ℝ) < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h] at hcardσ; simp at hcardσ
    · exact_mod_cast h
  have hι : (0 : ℝ) < Fintype.card ι := by
    have : (0 : ℝ) < c * Fintype.card ι := hcardσ ▸ hσpos
    exact (pos_iff_pos_of_mul_pos this).1 hc
  have hsum : ∑ s, Real.log (y (π s)) = c * ∑ τ, Real.log (y τ) := by
    have h := Finset.sum_fiberwise (s := (univ : Finset σ)) (g := π)
      (f := fun s => Real.log (y (π s)))
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => Real.log (y τ))
      (fun s hs => by rw [(mem_filter.1 hs).2])]
    rw [sum_const, hfib, nsmul_eq_mul]
  have hw : ∑ _τ : ι, (Fintype.card ι : ℝ)⁻¹ = 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul]; field_simp
  have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := (univ : Finset ι))
    (w := fun _ => (Fintype.card ι : ℝ)⁻¹) (p := y) (fun _ _ => by positivity) hw
    (fun τ _ => hy τ)
  simp only [smul_eq_mul, ← Finset.mul_sum] at hj
  have hSpos : 0 < ∑ τ, y τ := by
    have : Nonempty ι := ⟨π (Classical.arbitrary σ)⟩
    exact Finset.sum_pos (fun τ _ => hy τ) univ_nonempty
  unfold mean
  rw [hsum, hcardσ]
  calc (c * ∑ τ, Real.log (y τ)) / (c * Fintype.card ι)
      = (Fintype.card ι : ℝ)⁻¹ * ∑ τ, Real.log (y τ) := by field_simp
    _ ≤ Real.log ((Fintype.card ι : ℝ)⁻¹ * ∑ τ, y τ) := hj
    _ ≤ Real.log (B / Fintype.card ι) := by
        apply Real.log_le_log (by positivity)
        rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left hB (by positivity)

private lemma one_le_det_one_add {r : ℕ} (R : Matrix (Fin r) (Fin r) ℂ) (hR : R.PosSemidef) :
    1 ≤ (1 + R).det.re := by
  have hH := hR.isHermitian
  have e : (1 + R).det = ((∏ i, (1 + hH.eigenvalues i) : ℝ) : ℂ) := by
    have h1 : 1 + R = Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
        (1 + diagonal (RCLike.ofReal ∘ hH.eigenvalues)) := by
      rw [map_add, map_one, ← hH.spectral_theorem]
    rw [h1, Unitary.conjStarAlgAut_apply, det_mul_comm, ← mul_assoc]
    have h2 : (1 : Matrix (Fin r) (Fin r) ℂ) + diagonal (RCLike.ofReal ∘ hH.eigenvalues)
        = diagonal (fun i => (1 : ℂ) + (hH.eigenvalues i : ℂ)) := by
      rw [← diagonal_one, diagonal_add]; rfl
    rw [h2]
    simp [det_diagonal]
  rw [e, Complex.ofReal_re]
  have : ∀ i ∈ (univ : Finset (Fin r)), (1 : ℝ) ≤ 1 + hH.eigenvalues i := fun i _ => by
    have := hR.eigenvalues_nonneg i
    linarith
  calc (1 : ℝ) = ∏ _i : Fin r, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) this

private lemma minor_le_gram {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℂ) (e : Fin r → Fin n)
    (he : Function.Injective e) :
    ‖(A.submatrix id e).det‖ ^ 2 ≤ (A * A.conjTranspose).det.re := by
  classical
  set B := A.submatrix id e with hB
  have hpsd : (A * A.conjTranspose).PosSemidef := posSemidef_self_mul_conjTranspose A
  by_cases hdet : B.det = 0
  · rw [hdet]
    have := (Complex.le_def.1 hpsd.det_nonneg).1
    simpa using this
  set Q : Matrix (Fin r) (Fin r) ℂ :=
    A * diagonal (fun j => if j ∈ Set.range e then (0 : ℂ) else 1) * A.conjTranspose with hQ
  have hQpsd : Q.PosSemidef := by
    apply PosSemidef.mul_mul_conjTranspose_same
    apply PosSemidef.diagonal
    intro j
    dsimp only
    split_ifs <;> simp
  have hsplit : A * A.conjTranspose = B * B.conjTranspose + Q := by
    ext i k
    rw [hQ, hB, Matrix.add_apply, mul_apply, mul_apply, mul_apply]
    simp only [mul_diagonal, conjTranspose_apply, submatrix_apply, id]
    have h1 : ∑ l, A i (e l) * star (A k (e l))
        = ∑ j, if j ∈ Set.range e then A i j * star (A k j) else 0 := by
      rw [← Finset.sum_filter]
      have : (univ.filter fun j => j ∈ Set.range e) = univ.image e := by
        ext j; simp [eq_comm]
      rw [this, Finset.sum_image (fun a _ b _ h => he h)]
    rw [h1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hdet
  set R : Matrix (Fin r) (Fin r) ℂ := B⁻¹ * Q * (B⁻¹).conjTranspose with hR
  have hRpsd : R.PosSemidef := hQpsd.mul_mul_conjTranspose_same _
  have hfac : A * A.conjTranspose = B * (1 + R) * B.conjTranspose := by
    rw [hsplit, hR, mul_add, add_mul, mul_one]
    congr 1
    have h1 : B * B⁻¹ = 1 := mul_nonsing_inv B hu
    have h2 : (B⁻¹).conjTranspose * B.conjTranspose = 1 := by
      rw [← conjTranspose_mul, h1, conjTranspose_one]
    calc Q = (B * B⁻¹) * Q * ((B⁻¹).conjTranspose * B.conjTranspose) := by
          rw [h1, h2, one_mul, mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hfac, det_mul, det_mul, det_conjTranspose]
  have h3 := one_le_det_one_add R hRpsd
  have him : (1 + R).det.im = 0 := by
    have := (PosSemidef.one.add hRpsd).det_nonneg
    exact (Complex.le_def.1 this).2.symm
  have h4 : (B.det * (1 + R).det * star B.det).re = ‖B.det‖ ^ 2 * (1 + R).det.re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
      him]
    ring
  rw [h4]
  nlinarith [sq_nonneg ‖B.det‖]

theorem orthogonal_minor_bound : OrthogonalMinorBound := by
  intro r n A d e hd he
  classical
  set S : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => ((Real.sqrt (d i) : ℝ) : ℂ)) with hS
  have hSS : S * S.conjTranspose = diagonal (fun i => (d i : ℂ)) := by
    rw [hS, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    ext i
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hd i).le]
  have hgram : A * diagonal (fun i => (d i : ℂ)) * A.conjTranspose
      = (A * S) * (A * S).conjTranspose := by
    rw [conjTranspose_mul, ← hSS]
    simp only [Matrix.mul_assoc]
  have hsub : (A * S).submatrix id e
      = A.submatrix id e * diagonal (fun i => ((Real.sqrt (d (e i)) : ℝ) : ℂ)) := by
    ext i k
    simp [hS, mul_apply, diagonal_apply]
  have h := minor_le_gram (A * S) e he
  rw [hgram]
  refine le_trans (le_of_eq ?_) h
  rw [hsub, det_mul, det_diagonal, norm_mul, mul_pow]
  congr 1
  rw [norm_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hd _).le]

end Formalism.HermitianLattices.TraceIntegrality
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.SmoothedRemainderRealHasDerivBound
section
open Finset Filter Topology ArithmeticFunction
open scoped ENNReal

namespace Formalism.HermitianLattices.GL2PrimeSums

theorem weighted_sum_tendsto : WeightedSumTendsto := by
  intro a S hS y hy
  set M := ⌊y⌋₊ with hM
  let g : ℕ → ℂ := fun n => a n * ((min 1 (y / (n : ℝ)) : ℝ) : ℂ) - (y : ℂ) * (a n / (n : ℂ))
  have hg0 : ∀ n : ℕ, M < n → g n = 0 := by
    intro n hn
    have hyn : y < n := (Nat.floor_lt (by linarith)).mp hn
    have hn0 : (0:ℝ) < n := by linarith
    have : min 1 (y / (n:ℝ)) = y / n := min_eq_right ((div_le_one hn0).mpr hyn.le)
    simp only [g, this]; push_cast; ring
  have hg1 : ∀ n : ℕ, 1 ≤ n → n ≤ M → g n = - (a n * ((y / (n : ℝ) - 1 : ℝ) : ℂ)) := by
    intro n h1 hn
    have hyn : (n:ℝ) ≤ y := (Nat.le_floor_iff (by linarith)).mp hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast h1
    have : min 1 (y / (n:ℝ)) = 1 := min_eq_left ((one_le_div hn0).mpr hyn)
    simp only [g, this]; push_cast; ring
  have key : ∀ N : ℕ, M ≤ N → ∑ n ∈ Icc 1 N, a n * ((min 1 (y / (n : ℝ)) : ℝ) : ℂ)
      = (∑ n ∈ Icc 1 M, g n) + (y : ℂ) * ∑ n ∈ Icc 1 N, a n / (n : ℂ) := by
    intro N hN
    have h1 : ∑ n ∈ Icc 1 M, g n = ∑ n ∈ Icc 1 N, g n := by
      apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hN)
      intro n hn hn'
      apply hg0
      by_contra hc
      exact hn' (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, not_lt.mp hc⟩)
    rw [h1, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _; simp only [g]; ring
  have hlim : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 M, g n) + (y : ℂ) * ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop
      (𝓝 ((∑ n ∈ Icc 1 M, g n) + (y : ℂ) * S)) := (hS.const_mul _).const_add _
  have hval : -Gchi a S y = (∑ n ∈ Icc 1 M, g n) + (y : ℂ) * S := by
    unfold Gchi
    rw [Finset.sum_congr rfl (fun n hn => hg1 n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2),
      Finset.sum_neg_distrib]
    ring
  rw [hval]
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop M] with N hN
  exact (key N hN).symm

end Formalism.HermitianLattices.GL2PrimeSums
end

