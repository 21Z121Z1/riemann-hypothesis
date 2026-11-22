import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PDeltaIntSeries
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries Filter Topology Finset
open scoped Real

noncomputable section

theorem norm_intSeries_term (F : PowerSeries ℤ) (z : ℂ) (n : ℕ) :
    ‖((coeff n F : ℤ) : ℂ) * z ^ n‖ = |((coeff n F : ℤ) : ℝ)| * ‖z‖ ^ n := by
  rw [norm_mul, norm_pow, Complex.norm_intCast]

theorem intSeriesConv_mul {F G : PowerSeries ℤ} {r : ℝ} (hr : 0 ≤ r) (hF : IntSeriesConv F r)
    (hG : IntSeriesConv G r) : IntSeriesConv (F * G) r := by
  have hF' : Summable fun n ↦ ‖|((coeff n F : ℤ) : ℝ)| * r ^ n‖ := by
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_pow, abs_of_nonneg hr]; exact hF
  have hG' : Summable fun n ↦ ‖|((coeff n G : ℤ) : ℝ)| * r ^ n‖ := by
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_pow, abs_of_nonneg hr]; exact hG
  refine (summable_norm_sum_mul_antidiagonal_of_summable_norm hF' hG').of_nonneg_of_le
    (fun n ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hr _)) fun n ↦ ?_
  rw [coeff_mul, Int.cast_sum, Real.norm_eq_abs]
  refine ((mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) (pow_nonneg hr _)).trans_eq ?_).trans
    (le_abs_self _)
  rw [sum_mul]
  refine sum_congr rfl fun ij hij ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hij
  rw [← hij, pow_add, Int.cast_mul, abs_mul]
  ring

theorem intSeriesEval_mul {F G : PowerSeries ℤ} {z : ℂ} (hF : IntSeriesConv F ‖z‖)
    (hG : IntSeriesConv G ‖z‖) : intSeriesEval (F * G) z = intSeriesEval F z * intSeriesEval G z := by
  have hF' : Summable fun n ↦ ‖((coeff n F : ℤ) : ℂ) * z ^ n‖ := by
    simp only [norm_intSeries_term]; exact hF
  have hG' : Summable fun n ↦ ‖((coeff n G : ℤ) : ℂ) * z ^ n‖ := by
    simp only [norm_intSeries_term]; exact hG
  rw [intSeriesEval, intSeriesEval, intSeriesEval,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hF' hG']
  refine tsum_congr fun n ↦ ?_
  rw [coeff_mul, Int.cast_sum, sum_mul]
  refine sum_congr rfl fun ij hij ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hij
  rw [← hij, pow_add, Int.cast_mul]
  ring

theorem intSeriesConv_one {r : ℝ} : IntSeriesConv 1 r := by
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn
  simp [coeff_one, show n ≠ 0 by simpa using hn]

theorem intSeriesEval_one (z : ℂ) : intSeriesEval 1 z = 1 := by
  rw [intSeriesEval, tsum_eq_single 0 fun n hn ↦ by simp [coeff_one, hn]]
  simp

theorem intSeriesConv_pow {F : PowerSeries ℤ} {r : ℝ} (hr : 0 ≤ r) (hF : IntSeriesConv F r)
    (m : ℕ) : IntSeriesConv (F ^ m) r := by
  induction m with
  | zero => simpa using intSeriesConv_one
  | succ m ih => rw [pow_succ]; exact intSeriesConv_mul hr ih hF

theorem intSeriesEval_pow {F : PowerSeries ℤ} {z : ℂ} (hF : IntSeriesConv F ‖z‖) (m : ℕ) :
    intSeriesEval (F ^ m) z = intSeriesEval F z ^ m := by
  induction m with
  | zero => simpa using intSeriesEval_one z
  | succ m ih =>
    rw [pow_succ, intSeriesEval_mul (intSeriesConv_pow (norm_nonneg z) hF m) hF, ih, pow_succ]

theorem abs_coeff_pentagonalSeries_le (n : ℕ) :
    |((coeff n (pentagonalSeries ℤ) : ℤ) : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs, ← Int.cast_one (R := ℝ), Int.cast_le]
  simp only [pentagonalSeries, coeff_mk]
  split_ifs with h
  · rcases Int.units_eq_one_or (Int.negOnePow h.choose) with h' | h' <;> simp [h']
  · simp

theorem intSeriesConv_pentagonalSeries {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    IntSeriesConv (pentagonalSeries ℤ) r :=
  (summable_geometric_of_lt_one hr hr1).of_nonneg_of_le (fun n ↦ by positivity)
    fun n ↦ (mul_le_of_le_one_left (pow_nonneg hr _) (abs_coeff_pentagonalSeries_le n))

theorem norm_prod_one_sub_pow_le {x : ℂ} (hx : ‖x‖ < 1) (k n : ℕ) :
    ‖∏ i ∈ range (n + 1), (1 - x ^ (k + i + 1))‖ ≤ Real.exp (1 - ‖x‖)⁻¹ := by
  rw [norm_prod]
  calc ∏ i ∈ range (n + 1), ‖1 - x ^ (k + i + 1)‖
      ≤ ∏ i ∈ range (n + 1), Real.exp (‖x‖ ^ i) := by
        refine prod_le_prod (fun _ _ ↦ norm_nonneg _) fun i _ ↦ ?_
        calc ‖1 - x ^ (k + i + 1)‖ ≤ ‖(1 : ℂ)‖ + ‖x ^ (k + i + 1)‖ := norm_sub_le _ _
          _ = ‖x‖ ^ (k + i + 1) + 1 := by rw [norm_one, norm_pow, add_comm]
          _ ≤ ‖x‖ ^ i + 1 := by
            linarith [pow_le_pow_of_le_one (norm_nonneg x) hx.le (by omega : i ≤ k + i + 1)]
          _ ≤ Real.exp (‖x‖ ^ i) := Real.add_one_le_exp _
    _ = Real.exp (∑ i ∈ range (n + 1), ‖x‖ ^ i) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (1 - ‖x‖)⁻¹ := by
        gcongr
        rw [← tsum_geometric_of_lt_one (norm_nonneg _) hx]
        exact (summable_geometric_of_lt_one (norm_nonneg _) hx).sum_le_tsum _
          (fun _ _ ↦ by positivity)

theorem tprod_one_sub_pow_eq_intSeriesEval {x : ℂ} (hx : ‖x‖ < 1) :
    ∏' n, (1 - x ^ (n + 1)) = intSeriesEval (pentagonalSeries ℤ) x := by
  set M := Real.exp (1 - ‖x‖)⁻¹
  have hgeo := summable_geometric_of_lt_one (norm_nonneg x) hx
  have hterm (k n : ℕ) :
      ‖x ^ ((k + 1) * n) * ∏ i ∈ range (n + 1), (1 - x ^ (k + i + 1))‖ ≤ ‖x‖ ^ n * M := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) hx.le (by nlinarith : n ≤ (k + 1) * n))
      (norm_prod_one_sub_pow_le hx k n) (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
  have hsum (k : ℕ) : Summable
      (fun n ↦ x ^ ((k + 1) * n) * ∏ i ∈ range (n + 1), (1 - x ^ (k + i + 1))) :=
    (hgeo.mul_right M).of_norm_bounded (hterm k)
  have hlhs (k : ℕ) : Multipliable (fun n ↦ 1 - x ^ (n + k + 1)) := by
    apply multipliable_one_add_of_summable (f := fun n ↦ -x ^ (n + k + 1))
    simpa [add_assoc] using (summable_nat_add_iff (k + 1)).mpr hgeo
  have htail : Tendsto (fun k ↦ (-1) ^ (k + 1) * x ^ ((k + 1) * (3 * k + 4) / 2) *
      ∑' (n : ℕ), x ^ ((k + 1) * n) * ∏ i ∈ range (n + 1), (1 - x ^ (k + i + 1)))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun k ↦ ‖x‖ ^ k * ∑' n, ‖x‖ ^ n * M) (fun k ↦ ?_) ?_
    · rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
      refine mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) hx.le ?_) ?_ (norm_nonneg _)
        (pow_nonneg (norm_nonneg _) _)
      · rw [Nat.le_div_iff_mul_le two_pos]; nlinarith
      · exact (norm_tsum_le_tsum_norm ((hgeo.mul_right M).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
          (hterm k))).trans ((hgeo.mul_right M).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
          (hterm k) |>.tsum_le_tsum (hterm k) (hgeo.mul_right M))
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg x) hx).mul_const
        (∑' n, ‖x‖ ^ n * M)

  have hP : HasSum (fun n ↦ ((coeff n (pentagonalSeries ℤ) : ℤ) : ℂ) * x ^ n)
      (intSeriesEval (pentagonalSeries ℤ) x) := by
    refine (Summable.of_norm ?_).hasSum
    simp only [norm_intSeries_term]
    exact intSeriesConv_pentagonalSeries (norm_nonneg x) hx
  rw [← pentagonal_injective.hasSum_iff fun n hn ↦ by
    simp [coeff_pentagonalSeries_eq_zero ℤ hn]] at hP
  rw [← neg_injective.hasSum_iff (fun y hy ↦ by absurd hy; use -y; simp)] at hP
  have hN := hP.nat_add_neg_add_one
  have hN' : HasSum (fun k : ℕ ↦ (-1) ^ k * (x ^ pentagonal (-k) - x ^ pentagonal (k + 1)))
      (intSeriesEval (pentagonalSeries ℤ) x) := by
    convert hN using 1
    ext k
    simp_rw [Function.comp_apply, neg_neg, coeff_pentagonalSeries_pentagonal, Int.negOnePow_add]
    simp
    ring
  rw [Pentagonal.tprod_one_sub_pow (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx) hsum hlhs
    hN'.summable htail, hN'.tsum_eq]

theorem DeltaIntSeries.proof : DeltaIntSeries.Statement := by
  refine ⟨pentagonalSeries ℤ ^ 24, ?_, fun r hr hr1 ↦
    intSeriesConv_pow hr (intSeriesConv_pentagonalSeries hr hr1) 24, fun τ ↦ ?_⟩
  · have h0 : coeff 0 (pentagonalSeries ℤ) = 1 := by
      have h := coeff_pentagonalSeries_pentagonal ℤ 0
      rwa [show pentagonal 0 = 0 by simp [pentagonal_def], Int.negOnePow_zero, Units.val_one] at h
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply, h0,
      one_pow]
  · have hq : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 := by
      simpa using τ.norm_qParam_lt_one 1
    rw [ModularForm.discriminant_eq_q_prod]
    simp only [ModularForm.eta_q]
    rw [(ModularForm.multipliable_one_sub_pow hq).tprod_pow,
      tprod_one_sub_pow_eq_intSeriesEval hq,
      intSeriesEval_pow (intSeriesConv_pentagonalSeries (norm_nonneg _) hq)]

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PIntSeriesInv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries Finset

noncomputable section

theorem IntSeriesInv.proof : IntSeriesInv.Statement := by
  intro F r hr hF h0
  set G : PowerSeries ℤ := invOfUnit F 1 with hGdef
  have hFG : F * G = 1 := mul_invOfUnit F 1 (by rw [← coeff_zero_eq_constantCoeff_apply, h0]; rfl)

  set B : ℝ := ∑' n, |((coeff n F : ℤ) : ℝ)| * r ^ n
  have hB : ∀ n, |((coeff n F : ℤ) : ℝ)| * r ^ n ≤ B := fun n ↦
    hF.le_tsum n (fun j _ ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hr.le _))
  set C : ℝ := max B 1
  have hC1 : 1 ≤ C := le_max_right _ _
  set L : ℝ := C / r
  have hL : 0 < L := div_pos (by linarith) hr
  have hf : ∀ n, 1 ≤ n → |((coeff n F : ℤ) : ℝ)| ≤ L ^ n := by
    intro n hn
    have hrn : 0 < r ^ n := pow_pos hr n
    rw [div_pow, le_div_iff₀ hrn]
    calc |((coeff n F : ℤ) : ℝ)| * r ^ n ≤ C := (hB n).trans (le_max_left _ _)
      _ ≤ C ^ n := le_self_pow₀ hC1 (by omega)

  have hg0 : coeff 0 G = 1 := by
    have := congrArg (coeff 0) hFG
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
    simpa [h0] using this
  have hrec : ∀ n, coeff (n + 1) G =
      -∑ i ∈ range (n + 1), coeff (i + 1) F * coeff (n - i) G := by
    intro n
    have := congrArg (coeff (n + 1)) hFG
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ',
      coeff_one, if_neg (Nat.succ_ne_zero n)] at this
    simp only [h0, one_mul, Nat.sub_zero, Nat.add_sub_add_right] at this
    linarith

  have hg : ∀ n, |((coeff n G : ℤ) : ℝ)| ≤ (2 * L) ^ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | n
      · simp [hg0]
      · rw [hrec n]
        push_cast
        rw [abs_neg]
        calc |∑ i ∈ range (n + 1), ((coeff (i + 1) F : ℤ) : ℝ) * ((coeff (n - i) G : ℤ) : ℝ)|
            ≤ ∑ i ∈ range (n + 1),
                |((coeff (i + 1) F : ℤ) : ℝ)| * |((coeff (n - i) G : ℤ) : ℝ)| := by
              refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
              simp [abs_mul]
          _ ≤ ∑ i ∈ range (n + 1), (2 * L) ^ (n + 1) * (1 / 2) ^ (i + 1) := by
              refine sum_le_sum fun i hi ↦ ?_
              have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
              have e : (2 * L) ^ (n + 1) * (1 / 2) ^ (i + 1) = L ^ (i + 1) * (2 * L) ^ (n - i) := by
                have : n + 1 = (i + 1) + (n - i) := by omega
                rw [this, pow_add]
                rw [mul_pow 2 L (i + 1)]
                have h2 : (2 : ℝ) ^ (i + 1) * (1 / 2) ^ (i + 1) = 1 := by
                  rw [← mul_pow]; norm_num
                linear_combination (L ^ (i + 1) * (2 * L) ^ (n - i)) * h2
              rw [e]
              exact mul_le_mul (hf (i + 1) (by omega)) (ih (n - i) (by omega)) (abs_nonneg _)
                (pow_nonneg hL.le _)
          _ = (2 * L) ^ (n + 1) * ((1 / 2) * ∑ i ∈ range (n + 1), (1 / 2 : ℝ) ^ i) := by
              rw [mul_sum, mul_sum]
              refine sum_congr rfl fun i _ ↦ ?_
              ring
          _ ≤ (2 * L) ^ (n + 1) * 1 := by
              gcongr
              have := sum_geometric_two_le (n + 1)
              linarith
          _ = (2 * L) ^ (n + 1) := mul_one _

  refine ⟨G, 1 / (4 * L), by positivity, ?_, hFG⟩
  refine Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (abs_nonneg _) (by positivity))
    (fun n ↦ ?_) summable_geometric_two
  calc |((coeff n G : ℤ) : ℝ)| * (1 / (4 * L)) ^ n ≤ (2 * L) ^ n * (1 / (4 * L)) ^ n :=
        mul_le_mul_of_nonneg_right (hg n) (by positivity)
    _ = (1 / 2) ^ n := by
        rw [← mul_pow]
        congr 1
        field_simp
        ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PIntSeriesNorm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries
open scoped Real

noncomputable section

namespace IntSeriesNorm

theorem intSeriesEval_one (z : ℂ) : intSeriesEval 1 z = 1 := by
  rw [intSeriesEval, tsum_eq_single 0]
  · simp
  · intro n hn; simp [coeff_one, hn]

theorem intSeriesEval_X (z : ℂ) : intSeriesEval X z = z := by
  rw [intSeriesEval, tsum_eq_single 1]
  · simp
  · intro n hn; simp [coeff_X, hn]

theorem intSeriesConv_X (r : ℝ) : IntSeriesConv X r := by
  apply summable_of_ne_finset_zero (s := {1})
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [coeff_X, hn]

def residuePart (F : PowerSeries ℤ) (p i : ℕ) : PowerSeries ℤ :=
  mk fun m ↦ coeff (m * p + i) F

theorem residuePart_conv {F : PowerSeries ℤ} {r : ℝ} (hr : 0 < r) (hF : IntSeriesConv F r)
    {p : ℕ} (hp : 0 < p) (i : ℕ) : IntSeriesConv (residuePart F p i) (r ^ p) := by
  unfold IntSeriesConv at *
  have hinj : Function.Injective fun m : ℕ ↦ m * p + i := fun a b h ↦
    Nat.eq_of_mul_eq_mul_right hp (Nat.add_right_cancel h)
  have h1 := (hF.comp_injective hinj).mul_left ((r ^ i)⁻¹)
  refine h1.congr fun m ↦ ?_
  have hri : r ^ i ≠ 0 := pow_ne_zero _ hr.ne'
  simp only [Function.comp_apply, residuePart, coeff_mk]
  rw [pow_add, pow_mul']
  field_simp

theorem intSeriesEval_split (hR : IntSeriesRing.Statement) {F : PowerSeries ℤ} {r : ℝ}
    (hr : 0 < r) (hF : IntSeriesConv F r) {p : ℕ} (hp : 0 < p) (s : ℂ) (hs : ‖s‖ ≤ r) :
    intSeriesEval F s = ∑ i : Fin p, s ^ (i : ℕ) * intSeriesEval (residuePart F p i) (s ^ p) := by
  have : NeZero p := ⟨hp.ne'⟩
  have hq : ‖s ^ p‖ ≤ r ^ p := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hs p
  have hsum := (hR r hr.le).2.2.1 F hF s hs
  have hparts : ∀ i : Fin p, HasSum (fun m : ℕ ↦ ((coeff (m * p + i) F : ℤ) : ℂ) * s ^ (m * p + i))
      (s ^ (i : ℕ) * intSeriesEval (residuePart F p i) (s ^ p)) := by
    intro i
    have h := ((hR (r ^ p) (pow_nonneg hr.le p)).2.2.1 _ (residuePart_conv hr hF hp i) _ hq).mul_left
      (s ^ (i : ℕ))
    have hf : (fun m : ℕ ↦ ((coeff (m * p + i) F : ℤ) : ℂ) * s ^ (m * p + i)) =
        fun m ↦ s ^ (i : ℕ) * (((coeff m (residuePart F p i) : ℤ) : ℂ) * (s ^ p) ^ m) := by
      funext m
      simp only [residuePart, coeff_mk]
      rw [pow_add, pow_mul']
      ring
    rw [hf]
    exact h
  let e : ℕ ≃ Fin p × ℕ := (Nat.divModEquiv p).trans (Equiv.prodComm _ _)
  have hfe : ∀ x : Fin p × ℕ, e.symm x = x.2 * p + x.1 := fun x ↦ rfl
  have htot := (e.symm.hasSum_iff).mpr hsum
  simp only [Function.comp_def, hfe] at htot
  exact (htot.prod_fiberwise hparts).unique (hasSum_fintype _)

def evalHom (S : Subring (PowerSeries ℤ)) (z : ℂ)
    (hmul : ∀ F G : S, intSeriesEval ((F : PowerSeries ℤ) * G) z =
      intSeriesEval F z * intSeriesEval G z)
    (hhas : ∀ F : S, HasSum (fun n ↦ ((coeff n (F : PowerSeries ℤ) : ℤ) : ℂ) * z ^ n)
      (intSeriesEval F z)) : S →+* ℂ where
  toFun f := intSeriesEval f z
  map_one' := by simp only [Subring.coe_one, intSeriesEval_one]
  map_mul' F G := by simp only [Subring.coe_mul]; exact hmul F G
  map_zero' := by simp [intSeriesEval]
  map_add' F G := by
    have h := hhas (F + G)
    simp only [Subring.coe_add, map_add, Int.cast_add, add_mul] at h
    exact h.unique ((hhas F).add (hhas G))

def normMatrix (F : PowerSeries ℤ) (p : ℕ) [NeZero p] : Matrix (Fin p) (Fin p) (PowerSeries ℤ) :=
  Matrix.of fun i k ↦ (if i ≤ k then 1 else X) * residuePart F p ((k - i : Fin p) : ℕ)

theorem normMatrix_row (hR : IntSeriesRing.Statement) {F : PowerSeries ℤ} {r : ℝ} (hr : 0 < r)
    (hF : IntSeriesConv F r) {p : ℕ} [NeZero p] (s : ℂ) (hs : ‖s‖ ≤ r) (i : Fin p) :
    ∑ k : Fin p, intSeriesEval (normMatrix F p i k) (s ^ p) * s ^ (k : ℕ) =
      s ^ (i : ℕ) * intSeriesEval F s := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  obtain ⟨-, hmul, -, -, -⟩ := hR (r ^ p) (pow_nonneg hr.le p)
  have hq : ‖s ^ p‖ ≤ r ^ p := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hs p
  have hentry : ∀ k : Fin p, intSeriesEval (normMatrix F p i k) (s ^ p) =
      (if i ≤ k then 1 else s ^ p) * intSeriesEval (residuePart F p ((k - i : Fin p) : ℕ)) (s ^ p) := by
    intro k
    simp only [normMatrix, Matrix.of_apply]
    split_ifs
    · rw [one_mul, one_mul]
    · rw [hmul _ _ (intSeriesConv_X _) (residuePart_conv hr hF hp _) _ hq, intSeriesEval_X]
  rw [intSeriesEval_split hR hr hF hp s hs, Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (Equiv.addLeft i)
  intro k
  simp only [Equiv.coe_addLeft]
  rw [hentry, add_sub_cancel_left]
  have hi := i.is_lt
  have hk := k.is_lt
  by_cases h : (i : ℕ) + k < p
  · have hv : ((i + k : Fin p) : ℕ) = i + k := by rw [Fin.val_add, Nat.mod_eq_of_lt h]
    have hle : i ≤ i + k := by rw [Fin.le_iff_val_le_val, hv]; omega
    rw [if_pos hle, hv, pow_add]
    ring
  · have hv : ((i + k : Fin p) : ℕ) = i + k - p := by
      rw [Fin.val_add, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hnle : ¬ i ≤ i + k := by rw [Fin.le_iff_val_le_val, hv]; omega
    rw [if_neg hnle, hv]
    have hpow : s ^ ((i : ℕ) + k) = s ^ p * s ^ ((i : ℕ) + k - p) := by
      rw [← pow_add]; congr 1; omega
    generalize intSeriesEval (residuePart F p k) (s ^ p) = G
    calc s ^ (i : ℕ) * (s ^ (k : ℕ) * G) = s ^ ((i : ℕ) + k) * G := by rw [pow_add]; ring
      _ = _ := by rw [hpow]; ring

theorem proof (hR : IntSeriesRing.Statement) : IntSeriesNorm.Statement := by
  intro F r hr hF p hp j
  have : NeZero p := ⟨hp.ne'⟩
  obtain ⟨⟨S, hS⟩, hmul, hhas, -, -⟩ := hR (r ^ p) (pow_nonneg hr.le p)
  by_cases hj : p < j
  · refine ⟨0, ?_, fun t _ _ ↦ ?_⟩
    · simp [IntSeriesConv]
    · rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simpa using hj)]
      simp [intSeriesEval]
  push Not at hj
  have hmem : ∀ i k, normMatrix F p i k ∈ S := by
    intro i k
    simp only [normMatrix, Matrix.of_apply]
    split_ifs
    · rw [one_mul, hS]; exact residuePart_conv hr hF hp _
    · exact S.mul_mem ((hS _).2 (intSeriesConv_X _)) ((hS _).2 (residuePart_conv hr hF hp _))
  let M : Matrix (Fin p) (Fin p) S := Matrix.of fun i k ↦ ⟨normMatrix F p i k, hmem i k⟩
  let e : S := (-1) ^ j * M.charpoly.coeff (p - j)
  refine ⟨e, (hS _).1 e.2, fun t ht htr ↦ ?_⟩
  have hq : ‖t ^ p‖ ≤ r ^ p := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) htr p
  let φ : S →+* ℂ := evalHom S (t ^ p)
    (fun F G ↦ hmul F G ((hS _).1 F.2) ((hS _).1 G.2) _ hq) (fun F ↦ hhas F ((hS _).1 F.2) _ hq)
  have hφ : ∀ f : S, φ f = intSeriesEval f (t ^ p) := fun _ ↦ rfl
  set ζ := Complex.exp (2 * π * Complex.I / p) with hζdef
  have hζ : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p hp.ne'
  have hexp : ∀ a : ℕ, Complex.exp (2 * π * Complex.I * a / p) = ζ ^ a := by
    intro a; rw [hζdef, ← Complex.exp_nat_mul]; congr 1; ring
  let v : Fin p → ℂ := fun a ↦ ζ ^ (a : ℕ) * t
  have hvnorm : ∀ a, ‖v a‖ ≤ r := by
    intro a; simpa [v, norm_pow, hζ.norm'_eq_one hp.ne'] using htr
  have hvpow : ∀ a, v a ^ p = t ^ p := by
    intro a
    simp only [v]
    rw [mul_pow, ← pow_mul, mul_comm (a : ℕ) p, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hvinj : Function.Injective v := by
    intro a b hab
    exact Fin.ext (hζ.pow_inj a.is_lt b.is_lt (mul_right_cancel₀ ht hab))
  let d : Fin p → ℂ := fun a ↦ intSeriesEval F (v a)
  let A := M.map φ
  have hA : ∀ i k, A i k = intSeriesEval (normMatrix F p i k) (t ^ p) := fun _ _ ↦ rfl
  let V := (Matrix.vandermonde v).transpose
  have hAV : A * V = V * Matrix.diagonal d := by
    ext i a
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    simp only [V, Matrix.transpose_apply, Matrix.vandermonde_apply, hA]
    rw [← hvpow a]
    exact normMatrix_row hR hr hF (v a) (hvnorm a) i
  have hdet : IsUnit V.det := by
    rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hvinj
  have hchar : A.charpoly = (Matrix.diagonal d).charpoly := by
    have hconj : A = V * Matrix.diagonal d * V⁻¹ := by
      rw [← hAV, mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
    rw [hconj, Matrix.charpoly_mul_comm, ← mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul]
  have hmset : (Multiset.range p).map (fun a : ℕ ↦
      intSeriesEval F (Complex.exp (2 * π * Complex.I * a / p) * t)) =
      (Multiset.range p).map (fun a : ℕ ↦ intSeriesEval F (ζ ^ a * t)) :=
    Multiset.map_congr rfl fun a _ ↦ by rw [hexp]
  rw [hmset]
  set m := (Multiset.range p).map (fun a : ℕ ↦ intSeriesEval F (ζ ^ a * t)) with hm
  have hcard : Multiset.card m = p := by simp [hm]
  have hprod : (m.map fun x ↦ Polynomial.X - Polynomial.C x).prod = A.charpoly := by
    rw [hchar, Matrix.charpoly_diagonal]
    refine (((Fin.prod_univ_eq_prod_range
      (fun a : ℕ ↦ Polynomial.X - Polynomial.C (intSeriesEval F (ζ ^ a * t))) p)).trans ?_).symm
    rw [hm, Multiset.map_map]
    rfl
  have hcoef := Multiset.prod_X_sub_C_coeff m (k := p - j) (by omega)
  rw [hcard, Nat.sub_sub_self hj, hprod] at hcoef
  have heval : intSeriesEval (e : PowerSeries ℤ) (t ^ p) = (-1) ^ j * A.charpoly.coeff (p - j) := by
    rw [← hφ]
    show φ ((-1) ^ j * M.charpoly.coeff (p - j)) = _
    rw [map_mul, map_pow, map_neg, map_one, ← Polynomial.coeff_map, ← Matrix.charpoly_map]
  rw [heval, hcoef, ← mul_assoc, ← mul_pow]
  simp

end IntSeriesNorm

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

