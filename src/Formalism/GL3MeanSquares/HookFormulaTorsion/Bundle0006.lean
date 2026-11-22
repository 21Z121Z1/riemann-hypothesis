import Mathlib
import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.HolderExponentialMoments
section
namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset

private lemma exponential_moment_pos {ι : Type} [Fintype ι] (P y : ι → ℝ) (hP : ∀ j, 0 ≤ P j) (h1 : ∑ j, P j = 1)
    (t : ℝ) : 0 < ∑ j, P j * Real.exp (t * y j) := by
  have hne : ∃ j, 0 < P j := by
    by_contra hc
    push_neg at hc
    have : ∑ j, P j ≤ 0 := sum_nonpos fun j _ => hc j
    linarith
  obtain ⟨j, hj⟩ := hne
  exact lt_of_lt_of_le (mul_pos hj (Real.exp_pos _))
    (single_le_sum (f := fun j => P j * Real.exp (t * y j))
      (fun i _ => mul_nonneg (hP i) (Real.exp_pos _).le) (mem_univ j))

private lemma holder_exponential_moments {ι : Type} [Fintype ι] (P y : ι → ℝ) (hP : ∀ j, 0 ≤ P j)
    (s t a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    ∑ j, P j * Real.exp ((a * s + b * t) * y j) ≤
      (∑ j, P j * Real.exp (s * y j)) ^ a * (∑ j, P j * Real.exp (t * y j)) ^ b := by
  have hzero : ∀ u : ℝ, ∑ j, P j * Real.exp (u * y j) = 0 → ∀ j, P j = 0 := by
    intro u hu j
    have := (sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (hP i) (Real.exp_pos (u * y i)).le)).1 hu j (mem_univ j)
    exact (mul_eq_zero.1 this).resolve_right (Real.exp_pos _).ne'
  have hL0 : (∀ j, P j = 0) → ∑ j, P j * Real.exp ((a * s + b * t) * y j) = 0 := by
    intro h0; simp [h0]
  have hS0 : 0 ≤ ∑ j, P j * Real.exp (s * y j) :=
    sum_nonneg fun j _ => mul_nonneg (hP j) (Real.exp_pos _).le
  have hT0 : 0 ≤ ∑ j, P j * Real.exp (t * y j) :=
    sum_nonneg fun j _ => mul_nonneg (hP j) (Real.exp_pos _).le
  rcases hS0.eq_or_lt with hS | hS
  · rw [hL0 (hzero s hS.symm), ← hS, Real.zero_rpow ha.ne', zero_mul]
  rcases hT0.eq_or_lt with hT | hT
  · rw [hL0 (hzero t hT.symm), ← hT, Real.zero_rpow hb.ne', mul_zero]
  set S := ∑ j, P j * Real.exp (s * y j) with hSdef
  set T := ∑ j, P j * Real.exp (t * y j) with hTdef
  have key : ∀ j, Real.exp ((a * s + b * t) * y j) =
      Real.exp (s * y j) ^ a * Real.exp (t * y j) ^ b := by
    intro j
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have hSa : 0 < S ^ a := Real.rpow_pos_of_pos hS a
  have hTb : 0 < T ^ b := Real.rpow_pos_of_pos hT b
  have pt : ∀ j, P j * Real.exp ((a * s + b * t) * y j) / (S ^ a * T ^ b) ≤
      a * (P j * Real.exp (s * y j) / S) + b * (P j * Real.exp (t * y j) / T) := by
    intro j
    have g := Real.geom_mean_le_arith_mean2_weighted ha.le hb.le
      (div_nonneg (Real.exp_pos (s * y j)).le hS.le)
      (div_nonneg (Real.exp_pos (t * y j)).le hT.le) hab
    rw [Real.div_rpow (Real.exp_pos _).le hS.le, Real.div_rpow (Real.exp_pos _).le hT.le] at g
    rw [key j]
    calc P j * (Real.exp (s * y j) ^ a * Real.exp (t * y j) ^ b) / (S ^ a * T ^ b)
        = P j * (Real.exp (s * y j) ^ a / S ^ a * (Real.exp (t * y j) ^ b / T ^ b)) := by
          field_simp
      _ ≤ P j * (a * (Real.exp (s * y j) / S) + b * (Real.exp (t * y j) / T)) :=
          mul_le_mul_of_nonneg_left g (hP j)
      _ = a * (P j * Real.exp (s * y j) / S) + b * (P j * Real.exp (t * y j) / T) := by ring
  have hsum := sum_le_sum fun j (_ : j ∈ univ) => pt j
  have e1 : ∑ j, (a * (P j * Real.exp (s * y j) / S) + b * (P j * Real.exp (t * y j) / T)) = 1 := by
    simp only [sum_add_distrib, ← mul_sum, ← sum_div]
    rw [← hSdef, ← hTdef, div_self hS.ne', div_self hT.ne', mul_one, mul_one, hab]
  rw [e1, ← sum_div, div_le_one (mul_pos hSa hTb)] at hsum
  exact hsum

theorem log_moment_convexity : LogMomentConvexity := by
  intro ι _ P y hP h1
  have hpos := fun t => exponential_moment_pos P y hP h1 t
  have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => Real.log (∑ j, P j * Real.exp (t * y j))) := by
    refine ⟨convex_univ, ?_⟩
    intro s _ t _ a b ha hb hab
    simp only [smul_eq_mul]
    rcases ha.eq_or_lt with ha0 | ha0
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      simp
    rcases hb.eq_or_lt with hb0 | hb0
    · subst hb0
      have ha1 : a = 1 := by linarith
      subst ha1
      simp
    have hh := holder_exponential_moments P y hP s t a b ha0 hb0 hab
    calc Real.log (∑ j, P j * Real.exp ((a * s + b * t) * y j))
        ≤ Real.log ((∑ j, P j * Real.exp (s * y j)) ^ a * (∑ j, P j * Real.exp (t * y j)) ^ b) :=
          Real.log_le_log (hpos _) hh
      _ = a * Real.log (∑ j, P j * Real.exp (s * y j)) +
            b * Real.log (∑ j, P j * Real.exp (t * y j)) := by
          rw [Real.log_mul (Real.rpow_pos_of_pos (hpos s) a).ne' (Real.rpow_pos_of_pos (hpos t) b).ne',
            Real.log_rpow (hpos s), Real.log_rpow (hpos t)]
  refine ⟨hconv, ?_⟩
  intro t₀ t ht₀ ht
  have htpos : 0 < t := lt_of_lt_of_le ht₀ ht
  have ht0ne : t₀ ≠ 0 := ht₀.ne'
  have htne : t ≠ 0 := htpos.ne'
  have hf0 : Real.log (∑ j, P j * Real.exp (0 * y j)) = 0 := by simp [h1]
  have hc := hconv.2 (Set.mem_univ t) (Set.mem_univ 0) (div_nonneg ht₀.le htpos.le)
    (sub_nonneg.2 ((div_le_one htpos).2 ht)) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, hf0] at hc
  have e : t₀ / t * t = t₀ := by field_simp
  rw [e] at hc
  calc t / t₀ * Real.log (∑ j, P j * Real.exp (t₀ * y j))
      ≤ t / t₀ * (t₀ / t * Real.log (∑ j, P j * Real.exp (t * y j))) :=
        mul_le_mul_of_nonneg_left hc (div_nonneg htpos.le ht₀.le)
    _ = Real.log (∑ j, P j * Real.exp (t * y j)) := by
        rw [← mul_assoc, div_mul_div_comm, mul_comm t t₀, div_self (mul_ne_zero ht0ne htne), one_mul]

private lemma half_le_gamma_succ (x : ℝ) (hx : 1 ≤ x) (h : 1 / 2 ≤ Real.Gamma x) :
    1 / 2 ≤ Real.Gamma (x + 1) := by
  rw [Real.Gamma_add_one (by linarith)]
  nlinarith

private lemma half_le_gamma_half_nat (n : ℕ) (hn : 2 ≤ n) : 1 / 2 ≤ Real.Gamma ((n : ℝ) / 2) := by
  revert hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
    · norm_num [Real.Gamma_one]
    · have e : ((3 : ℕ) : ℝ) / 2 = 1 / 2 + 1 := by norm_num
      rw [e, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
      have : (1 : ℝ) ≤ Real.sqrt Real.pi := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
      linarith
    · have e : (n : ℝ) / 2 = ((n - 2 : ℕ) : ℝ) / 2 + 1 := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      have hx : (2 : ℝ) ≤ ((n - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ n - 2)
      rw [e]
      exact half_le_gamma_succ _ (by linarith) (ih (n - 2) (by omega) (by omega))

theorem tail_negligible : TailNegligible := by
  refine ⟨20, ?_⟩
  intro n Q hn hQ
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hL : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  have hnL : (n : ℝ) * Real.log 2 ≤ n * Real.log n := mul_le_mul_of_nonneg_left hL hn0
  have hnl2 : (0.6931471803 : ℝ) * n ≤ n * Real.log 2 := by nlinarith
  have hQpos : 0 < Q := by nlinarith
  have h2n : (0 : ℝ) < 2 * n := by linarith
  have hlogQ : Real.log Q ≤ Q / (2 * n) - 1 + (Real.log 2 + Real.log n) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hQpos h2n)
    rw [Real.log_div hQpos.ne' h2n.ne', Real.log_mul (by norm_num) (by linarith)] at h1
    linarith
  have hm : (n : ℝ) / 2 * Real.log Q ≤
      Q / 4 - n / 2 + n / 2 * Real.log 2 + n / 2 * Real.log n := by
    have h1 := mul_le_mul_of_nonneg_left hlogQ (by linarith : (0 : ℝ) ≤ n / 2)
    have e : (n : ℝ) / 2 * (Q / (2 * n) - 1 + (Real.log 2 + Real.log n)) =
        Q / 4 - n / 2 + n / 2 * Real.log 2 + n / 2 * Real.log n := by
      have hnne : (n : ℝ) ≠ 0 := by linarith
      first | (field_simp; ring) | field_simp | ring
    linarith
  have hG := half_le_gamma_half_nat n hn
  have hQm : 0 < Q ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos hQpos _
  have h4Qm : 0 < 4 * Q ^ ((n : ℝ) / 2) := by linarith
  have h2Qm : 0 < 2 * Q ^ ((n : ℝ) / 2) := by linarith
  have hE : (3 : ℝ) ≤ -(n : ℝ) + Q / 2 - Real.log Q * ((n : ℝ) / 2) := by nlinarith
  have hexp : Real.exp (-(Q / 2)) * (4 * Q ^ ((n : ℝ) / 2)) ≤ Real.exp (-(n : ℝ)) := by
    rw [Real.rpow_def_of_pos hQpos]
    have h4 : (4 : ℝ) ≤ Real.exp (-(n : ℝ) + Q / 2 - Real.log Q * ((n : ℝ) / 2)) := by
      have := Real.add_one_le_exp (-(n : ℝ) + Q / 2 - Real.log Q * ((n : ℝ) / 2))
      linarith
    calc Real.exp (-(Q / 2)) * (4 * Real.exp (Real.log Q * ((n : ℝ) / 2)))
        ≤ Real.exp (-(Q / 2)) * (Real.exp (-(n : ℝ) + Q / 2 - Real.log Q * ((n : ℝ) / 2)) *
            Real.exp (Real.log Q * ((n : ℝ) / 2))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
      _ = Real.exp (-(n : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
  calc Real.exp (-(Q / 2))
      = Real.exp (-(Q / 2)) * (4 * Q ^ ((n : ℝ) / 2)) / (4 * Q ^ ((n : ℝ) / 2)) := by
        rw [mul_div_assoc, div_self h4Qm.ne', mul_one]
    _ ≤ Real.exp (-(n : ℝ)) / (4 * Q ^ ((n : ℝ) / 2)) := by gcongr
    _ = Real.exp (-(n : ℝ)) * (1 / 2 / (2 * Q ^ ((n : ℝ) / 2))) := by
        rw [div_div, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num, mul_one_div]
    _ ≤ Real.exp (-(n : ℝ)) * (Real.Gamma ((n : ℝ) / 2) / (2 * Q ^ ((n : ℝ) / 2))) := by
        gcongr

private lemma prod_range_factorial_pos (n : ℕ) : 0 < ∏ i ∈ range n, (i.factorial : ℝ) :=
  prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i

theorem grassmannian_volume : GrassmannianVolume := by
  intro p q
  have hF : ∀ n, 0 < ∏ i ∈ range n, (i.factorial : ℝ) := prod_range_factorial_pos
  have hPpos : ∀ n, 0 < ∏ i ∈ range n, Real.pi ^ (i + 1) :=
    fun n => prod_pos fun i _ => pow_pos Real.pi_pos _
  have hA : ∀ n, ∏ i ∈ range n, 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) =
      2 ^ n * (∏ i ∈ range n, Real.pi ^ (i + 1)) / ∏ i ∈ range n, (i.factorial : ℝ) := by
    intro n
    rw [prod_div_distrib, prod_mul_distrib, prod_const, card_range]
  have hP : ∏ i ∈ range (p + q), Real.pi ^ (i + 1) =
      (∏ i ∈ range p, Real.pi ^ (i + 1)) * (∏ i ∈ range q, Real.pi ^ (i + 1)) *
        Real.pi ^ (p * q) := by
    rw [prod_range_add]
    have e : ∀ j ∈ range q, Real.pi ^ (p + j + 1) = Real.pi ^ p * Real.pi ^ (j + 1) := by
      intro j _
      rw [← pow_add]
      congr 1
    rw [prod_congr rfl e, prod_mul_distrib, prod_const, card_range, ← pow_mul]
    ring
  have hFF : (∏ i ∈ range p, (i.factorial : ℝ)) * ∏ i ∈ range q, (i.factorial : ℝ) ≤
      ∏ i ∈ range (p + q), (i.factorial : ℝ) := by
    rw [prod_range_add]
    apply mul_le_mul_of_nonneg_left _ (hF p).le
    apply prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
    exact_mod_cast Nat.factorial_le (by omega)
  have h1 := (hF p).ne'
  have h2 := (hF q).ne'
  have h3 := (hF (p + q)).ne'
  have h4 := (hPpos p).ne'
  have h5 := (hPpos q).ne'
  refine ⟨?_, ?_⟩
  · rw [hA, hA, hA, hP, pow_add]
    field_simp
  · rw [mul_div_assoc]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (hF _)).2 hFF)

end Formalism.HermitianLattices.GenusMassVolumes
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.WeightShiftProduct
section
namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset MeasureTheory

theorem weight_shift_product : OppositeSignRhoDifferenceEqCard := by
  intro N sg rhoN a b hab hs
  have h1 : (univ.filter (fun c => a < c ∧ sg c ≠ sg a)).card =
      (univ.filter (fun e => a < e ∧ e < b ∧ sg e ≠ sg a)).card +
        (univ.filter (fun c => b < c ∧ sg c ≠ sg b)).card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext c
      simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨h, h'⟩
        rcases lt_trichotomy c b with hc | hc | hc
        · exact Or.inl ⟨h, hc, h'⟩
        · exact absurd (hc ▸ hs.symm) h'
        · exact Or.inr ⟨hc, hs ▸ h'⟩
      · rintro (⟨h, _, h'⟩ | ⟨h, h'⟩)
        · exact ⟨h, h'⟩
        · exact ⟨hab.trans h, hs ▸ h'⟩
    · rw [disjoint_left]
      intro c hc hc'
      simp only [mem_filter, mem_univ, true_and] at hc hc'
      exact absurd hc.2.1 (not_lt.mpr hc'.1.le)
  have h2 : (univ.filter (fun c => c < b ∧ sg c ≠ sg b)).card =
      (univ.filter (fun e => a < e ∧ e < b ∧ sg e ≠ sg a)).card +
        (univ.filter (fun c => c < a ∧ sg c ≠ sg a)).card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext c
      simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨h, h'⟩
        rcases lt_trichotomy c a with hc | hc | hc
        · exact Or.inr ⟨hc, hs ▸ h'⟩
        · exact absurd (hc ▸ hs) h'
        · exact Or.inl ⟨hc, h, hs ▸ h'⟩
      · rintro (⟨_, h, h'⟩ | ⟨h, h'⟩)
        · exact ⟨h, hs ▸ h'⟩
        · exact ⟨h.trans hab, hs ▸ h'⟩
    · rw [disjoint_left]
      intro c hc hc'
      simp only [mem_filter, mem_univ, true_and] at hc hc'
      exact absurd hc.1 (not_lt.mpr hc'.1.le)
  simp only [rhoN]
  rw [h1, h2]
  push_cast
  ring

private lemma exp_quadratic_lower_bound {y ε : ℝ} (hε1 : ε ≤ 1) (hy : |y| ≤ ε) :
    1 + y + y ^ 2 / 2 * (1 - 4 * ε / 9) ≤ Real.exp y := by
  have hy1 : |y| ≤ 1 := hy.trans hε1
  have hb := Real.exp_bound hy1 (n := 3) (by norm_num)
  have hsum : ∑ m ∈ range 3, y ^ m / (m.factorial : ℝ) = 1 + y + y ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hb
  have hc : |y| ^ 3 * (((3 : ℕ).succ : ℝ) / (((3 : ℕ).factorial : ℝ) * (3 : ℕ))) = |y| ^ 3 * (2 / 9) := by
    norm_num [Nat.factorial]
  rw [hc] at hb
  have h3 : |y| ^ 3 ≤ y ^ 2 * ε := by
    have : |y| ^ 3 = y ^ 2 * |y| := by rw [← sq_abs y]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hy (sq_nonneg y)
  have := (abs_le.mp hb).1
  nlinarith

theorem cumulant_expansion : CumulantLowerBound := by
  intro ι _ P y ε hP hP1 hmean hε0 hε1 hy
  set V : ℝ := ∑ j, P j * y j ^ 2 with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun j _ => mul_nonneg (hP j) (sq_nonneg _)
  have hVε : V ≤ ε ^ 2 := by
    calc V ≤ ∑ j, P j * ε ^ 2 := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hP j)
          exact sq_le_sq' (by linarith [(abs_le.mp (hy j)).1]) (abs_le.mp (hy j)).2
      _ = ε ^ 2 := by rw [← Finset.sum_mul, hP1, one_mul]
  set z : ℝ := V / 2 * (1 - 4 * ε / 9) with hz
  have hS : 1 + z ≤ ∑ j, P j * Real.exp (y j) := by
    calc 1 + z = ∑ j, P j * (1 + y j + y j ^ 2 / 2 * (1 - 4 * ε / 9)) := by
          have : ∀ j, P j * (1 + y j + y j ^ 2 / 2 * (1 - 4 * ε / 9)) =
              P j + P j * y j + (P j * y j ^ 2) * ((1 - 4 * ε / 9) / 2) := fun j => by ring
          simp only [this]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hP1, hmean, ← hV, hz]
          ring
      _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (exp_quadratic_lower_bound hε1 (hy j)) (hP j)
  have hc0 : 0 ≤ 1 - 4 * ε / 9 := by linarith
  have hz0 : 0 ≤ z := mul_nonneg (by linarith) hc0
  have h1z : 0 < 1 + z := by linarith
  have hlog : Real.log (1 + z) ≤ Real.log (∑ j, P j * Real.exp (y j)) := Real.log_le_log h1z hS
  have hinv := Real.one_sub_inv_le_log_of_pos h1z
  have hzz : z * (1 - z) ≤ 1 - (1 + z)⁻¹ := by
    have : 1 - (1 + z)⁻¹ = z / (1 + z) := by field_simp; ring
    rw [this, le_div_iff₀ h1z]
    nlinarith [mul_nonneg hz0 (mul_nonneg hz0 hz0)]
  have hzV : z ≤ ε / 2 := by
    have h1 : z ≤ V / 2 := by
      rw [hz]; nlinarith
    have h2 : ε ^ 2 ≤ ε := by nlinarith
    linarith
  have hfin : V / 2 * (1 - ε) ≤ z * (1 - z) := by
    have h1 : z * (1 - ε / 2) ≤ z * (1 - z) := mul_le_mul_of_nonneg_left (by linarith) hz0
    have h2 : V / 2 * (1 - ε) ≤ z * (1 - ε / 2) := by
      rw [hz, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      nlinarith [mul_nonneg hε0 hε0]
    linarith
  linarith

private lemma matrix_rank_add_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank ℂ (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank ℂ ((LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin :
          Submodule ℂ (Fin n → ℂ))) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

theorem rank_formula : RankLeTwiceMin := by
  intro N sg X hX
  classical
  set Dp : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun a => if sg a = true then 1 else 0) with hDp
  set Dm : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun a => if sg a = false then 1 else 0) with hDm
  have hrp : Dp.rank = (univ.filter (fun a => sg a = true)).card := by
    rw [hDp, Matrix.rank_diagonal, Fintype.card_subtype]
    congr 1
    ext a
    simp
  have hrm : Dm.rank = (univ.filter (fun a => sg a = false)).card := by
    rw [hDm, Matrix.rank_diagonal, Fintype.card_subtype]
    congr 1
    ext a
    simp
  have hdec : X = Dp * X * Dm + Dm * X * Dp := by
    ext a b
    rw [Matrix.add_apply, hDp, hDm, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.diagonal_mul]
    by_cases hs : sg a = sg b
    · rw [hX a b hs]; simp
    · cases ha : sg a <;> cases hb : sg b <;> simp_all
  have h1 : (Dp * X * Dm).rank ≤ min Dp.rank Dm.rank := by
    refine le_min ?_ (Matrix.rank_mul_le_right _ _)
    rw [Matrix.mul_assoc]
    exact Matrix.rank_mul_le_left _ _
  have h2 : (Dm * X * Dp).rank ≤ min Dp.rank Dm.rank := by
    refine le_min (Matrix.rank_mul_le_right _ _) ?_
    rw [Matrix.mul_assoc]
    exact Matrix.rank_mul_le_left _ _
  calc X.rank = (Dp * X * Dm + Dm * X * Dp).rank := by rw [← hdec]
    _ ≤ (Dp * X * Dm).rank + (Dm * X * Dp).rank := matrix_rank_add_le _ _
    _ ≤ _ := by rw [hrp, hrm] at h1 h2; omega

private lemma sum_ico_telescoping_plus_one (L : ℕ → ℝ) (b a : ℕ) (h : b ≤ a) :
    ∑ i ∈ Ico b a, (L i - L (i + 1) + 1) = L b - L a + ((a : ℝ) - b) := by
  induction a, h using Nat.le_induction with
  | base => simp
  | succ a h ih =>
    rw [Finset.sum_Ico_succ_top h, ih]
    push_cast
    ring

theorem weighted_sum_eq_quadratic_form : WeightedSumEqQuadraticForm := by
  intro N lam sg X hX P V
  have hent : ∀ (i : ℕ) (a b : Fin N), ((1 - P i) * X * P i) a b =
      if i ≤ a.val ∧ b.val < i then X a b else 0 := by
    intro i a b
    have h1 : (1 - P i) = Matrix.diagonal (fun a : Fin N => if a.val < i then (0 : ℂ) else 1) := by
      ext c d
      by_cases hcd : c = d
      · subst hcd
        by_cases hc : c.val < i <;> simp [P, hc]
      · simp [P, hcd]
    rw [h1]
    simp only [P]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases ha : a.val < i <;> by_cases hb : b.val < i <;> simp [ha, hb, not_le.mpr, not_lt.mp]
  have hV : ∀ i, V i = ∑ a, ∑ b, if i ≤ a.val ∧ b.val < i then ‖X a b‖ ^ 2 else 0 := by
    intro i
    simp only [V]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hent]
    split_ifs <;> simp
  set L : ℕ → ℝ := fun n => if h : n < N then lam ⟨n, h⟩ else 0 with hL
  have hLv : ∀ a : Fin N, L a.val = lam a := fun a => by simp [hL]
  have hterm : ∀ i : Fin N,
      (if h : i.val + 1 < N then (lam i - lam ⟨i.val + 1, h⟩ + 1) * V (i.val + 1) else 0) =
      ∑ a : Fin N, ∑ b : Fin N, (if i.val ∈ Ico b.val a.val then (L i.val - L (i.val + 1) + 1) else 0)
        * ‖X a b‖ ^ 2 := by
    intro i
    split_ifs with h
    · rw [hV, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have e1 : L (i.val + 1) = lam ⟨i.val + 1, h⟩ := by simp [hL, h]
      rw [hLv, e1]
      by_cases hc : i.val + 1 ≤ a.val ∧ b.val < i.val + 1
      · have : i.val ∈ Ico b.val a.val := by rw [mem_Ico]; omega
        rw [if_pos hc, if_pos this]
      · have : i.val ∉ Ico b.val a.val := by rw [mem_Ico]; omega
        rw [if_neg hc, if_neg this]; ring
    · symm
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      have : i.val ∉ Ico b.val a.val := by
        rw [mem_Ico]; have := a.isLt; omega
      rw [if_neg this, zero_mul]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ i : Fin N, (if i.val ∈ Ico b.val a.val then (L i.val - L (i.val + 1) + 1) else 0) =
      ∑ i ∈ Ico b.val a.val, (L i - L (i + 1) + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i ∈ Ico b.val a.val then (L i - L (i + 1) + 1) else 0) N,
      ← Finset.sum_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    have := a.isLt
    omega
  rw [hsum]
  by_cases hba : b < a
  · rw [sum_ico_telescoping_plus_one L _ _ (Fin.le_def.mp hba.le), hLv, hLv]
    by_cases hs : sg a = sg b
    · rw [hX a b hs]; simp [hs]
    · rw [if_pos ⟨hba, hs⟩]
  · have : Ico b.val a.val = ∅ := Finset.Ico_eq_empty (fun h => hba (Fin.lt_def.mpr h))
    rw [this, if_neg (fun h => hba h.1)]
    simp

end Formalism.HermitianLattices.GenusMassVolumes
end

