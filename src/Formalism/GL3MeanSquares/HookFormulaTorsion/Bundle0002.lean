import Mathlib
import Formalism.GL3MeanSquares.ConcavityEquidistribution
import Formalism.LogVandermondeBounds.LogVandermondeProofs.GammaIntegralPolynomialBound
import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.SeparatedSetPackingBound
section
namespace Formalism.HermitianLattices.TraceIntegrality

open MeasureTheory Set Metric

open scoped Function ENNReal in
theorem separated_set_packing_bound : SeparatedSetPackingBound := by
  intro E _ _ _ s r δ hδ hr hs h
  borelize E
  let μ : Measure E := Measure.addHaar
  have δpos : 0 < δ / 2 := by positivity
  have ρpos : 0 < r + δ / 2 := by positivity
  set A := ⋃ c ∈ s, ball (c : E) (δ / 2) with hA
  have D : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) (δ / 2)) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have := h c hc d hd hcd
    linarith
  have A_subset : A ⊆ ball (0 : E) (r + δ / 2) := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    have := hs x hx
    linarith
  have I :
    (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ Module.finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((r + δ / 2) ^ Module.finrank ℝ E) * μ (ball 0 1) :=
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ Module.finrank ℝ E) * μ (ball 0 1) = μ A := by
        rw [hA, measure_biUnion_finset D fun c _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ δpos]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) (r + δ / 2)) := measure_mono A_subset
      _ = ENNReal.ofReal ((r + δ / 2) ^ Module.finrank ℝ E) * μ (ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ ρpos]
  have J : (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ Module.finrank ℝ E) ≤
      ENNReal.ofReal ((r + δ / 2) ^ Module.finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) * (δ / 2) ^ Module.finrank ℝ E ≤ (r + δ / 2) ^ Module.finrank ℝ E := by
    have := ENNReal.toReal_le_of_le_ofReal (pow_nonneg ρpos.le _) J
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg δpos.le _)] at this
  have e : 1 + 2 * r / δ = (r + δ / 2) / (δ / 2) := by
    field_simp
    ring
  rw [e, div_pow, le_div_iff₀ (pow_pos δpos _)]
  exact K

theorem layer_cake_bound : LayerCakeSumBound := by
  intro Y h g v hv hh hc
  obtain ⟨hint, hle⟩ := Formalism.LogVandermondeBounds.flipTwoThree.gamma_integral_polynomial_bound v g hv
  have hpi := Real.pi_pos
  set w : ℝ → ℝ := fun u => Real.pi * Real.exp (-Real.pi * u) with hw
  have hwpos : ∀ u, 0 ≤ w u := fun u => by positivity
  have hwint : IntegrableOn w (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -Real.pi) (by linarith) 0).const_mul _
  have key : ∀ F : Finset Y,
      ∑ y ∈ F, Real.exp (-Real.pi * h y) ≤ 2 ^ g * (1 + 4 * g * v / Real.pi) ^ g := by
    intro F
    have h1 : ∀ y, Real.exp (-Real.pi * h y) = ∫ u in Ioi 0, (Ioi (h y)).indicator w u := by
      intro y
      rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right (hh y)]
      simp only [hw]
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith)]
      field_simp
    have hi : ∀ y, IntegrableOn ((Ioi (h y)).indicator w) (Ioi 0) := fun y =>
      hwint.indicator measurableSet_Ioi
    have hpt : ∀ u ∈ Ioi (0 : ℝ), ∑ y ∈ F, (Ioi (h y)).indicator w u ≤
        2 ^ g * (Real.pi * Real.exp (-Real.pi * u) * (1 + 4 * u * v) ^ g) := by
      intro u hu
      have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
      obtain ⟨hfin, hcard⟩ := hc u hu0
      have e1 : ∑ y ∈ F, (Ioi (h y)).indicator w u = ((F.filter (fun y => h y < u)).card : ℝ) * w u := by
        simp only [Set.indicator_apply, mem_Ioi]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have e2 : (F.filter (fun y => h y < u)).card ≤ {y | h y ≤ u}.ncard := by
        rw [← Set.ncard_coe_finset]
        apply Set.ncard_le_ncard _ hfin
        intro y hy
        simp only [Finset.coe_filter, mem_ofPred_eq] at hy
        exact le_of_lt hy.2
      have e3 : ((F.filter (fun y => h y < u)).card : ℝ) ≤ 2 ^ g * (1 + 4 * u * v) ^ g :=
        le_trans (by exact_mod_cast e2) hcard
      rw [e1]
      calc ((F.filter (fun y => h y < u)).card : ℝ) * w u
          ≤ (2 ^ g * (1 + 4 * u * v) ^ g) * w u := mul_le_mul_of_nonneg_right e3 (hwpos u)
        _ = _ := by simp only [hw]; ring
    calc ∑ y ∈ F, Real.exp (-Real.pi * h y)
        = ∑ y ∈ F, ∫ u in Ioi 0, (Ioi (h y)).indicator w u := Finset.sum_congr rfl fun y _ => h1 y
      _ = ∫ u in Ioi 0, ∑ y ∈ F, (Ioi (h y)).indicator w u :=
          (integral_finsetSum F fun y _ => hi y).symm
      _ ≤ ∫ u in Ioi (0 : ℝ), 2 ^ g * (Real.pi * Real.exp (-Real.pi * u) * (1 + 4 * u * v) ^ g) :=
          setIntegral_mono_on (integrable_finsetSum F fun y _ => hi y) (hint.const_mul _)
            measurableSet_Ioi hpt
      _ = 2 ^ g * ∫ u in Ioi (0 : ℝ), Real.pi * Real.exp (-Real.pi * u) * (1 + 4 * u * v) ^ g :=
          integral_const_mul _ _
      _ ≤ 2 ^ g * (1 + 4 * g * v / Real.pi) ^ g := mul_le_mul_of_nonneg_left hle (by positivity)
  have hnn : (0 : Y → ℝ) ≤ fun y => Real.exp (-Real.pi * h y) := fun y => (Real.exp_pos _).le
  have hsum := Real.tsum_le_of_sum_le hnn key
  refine ⟨summable_of_sum_le hnn key, hsum, ?_⟩
  have hb : 1 + 4 * (g : ℝ) * v / Real.pi ≤ 2 + 8 * g * v := by
    have h3 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hgv : 0 ≤ 4 * (g : ℝ) * v := by positivity
    have : 4 * (g : ℝ) * v / Real.pi ≤ 4 * (g : ℝ) * v := div_le_self hgv h3
    linarith
  have hb0 : 0 ≤ 1 + 4 * (g : ℝ) * v / Real.pi := by positivity
  calc (2 : ℝ) ^ g * ∑' y, Real.exp (-Real.pi * h y)
      ≤ 2 ^ g * (2 ^ g * (1 + 4 * g * v / Real.pi) ^ g) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 ^ g * (1 + 4 * g * v / Real.pi) ^ g := by
        rw [← mul_assoc, ← mul_pow]; norm_num
    _ ≤ 4 ^ g * (2 + 8 * g * v) ^ g :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hb g) (by positivity)

end Formalism.HermitianLattices.TraceIntegrality
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.SmoothedRemainderRealIntegralFormula
section
open Finset Filter Topology MeasureTheory

namespace Formalism.HermitianLattices.GL2PrimeSums

section abel

variable {𝕜 : Type*} [RCLike 𝕜]

private lemma hasDerivAt_inv_coe (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ => ((u : 𝕜))⁻¹) (-((t : 𝕜) ^ 2)⁻¹) t := by
  have h := (RCLike.ofRealCLM (K := 𝕜)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_inv ht)
  have hfun : (fun u : ℝ => ((u : 𝕜))⁻¹) = (RCLike.ofRealCLM (K := 𝕜)) ∘ fun y : ℝ => y⁻¹ := by
    funext u
    simp
  rw [hfun]
  exact h.congr_deriv (by simp)

private lemma Icc_one_eq_Ioc_zero (N : ℕ) : Icc 1 N = Ioc 0 N := by
  ext k
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

private theorem continuousOn_inv_sq_Icc_of_pos {y U : ℝ} (hy : 0 < y) :
    ContinuousOn (fun t : ℝ => ((t : 𝕜) ^ 2)⁻¹) (Set.Icc y U) := by
  refine ContinuousOn.inv₀ ((RCLike.continuous_ofReal (K := 𝕜)).pow 2).continuousOn ?_
  intro t ht
  have : (t : 𝕜) ≠ 0 := by
    rw [Ne, RCLike.ofReal_eq_zero]
    exact (show (0 : ℝ) < t by linarith [ht.1]).ne'
  exact pow_ne_zero 2 this

private lemma integrableOn_partial_sum_div_sq (c : ℕ → 𝕜) {y U : ℝ} (hy : 1 ≤ y) :
    IntegrableOn (fun u : ℝ => (∑ n ∈ Icc 1 ⌊u⌋₊, c n) / (u : 𝕜) ^ 2) (Set.Icc y U) := by
  have hg : IntegrableOn (fun t : ℝ => ((t : 𝕜) ^ 2)⁻¹) (Set.Icc y U) :=
    (continuousOn_inv_sq_Icc_of_pos (by linarith)).integrableOn_Icc
  have := integrableOn_mul_sum_Icc c (m := 1) (by linarith : (0 : ℝ) ≤ y) hg
  refine this.congr_fun (fun t _ => ?_) measurableSet_Icc
  simp only [div_eq_inv_mul]

private theorem sum_Icc_zero_ite_eq_sum_Icc_one (c : ℕ → 𝕜) (N : ℕ) :
    ∑ k ∈ Icc 0 N, (if k = 0 then (0 : 𝕜) else c k) = ∑ k ∈ Icc 1 N, c k := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons, Icc_one_eq_Ioc_zero]
  simp only [↓reduceIte, zero_add]
  exact Finset.sum_congr rfl fun k hk => if_neg (Finset.mem_Ioc.mp hk).1.ne'

private lemma integral_partial_sum_div_sq (c : ℕ → 𝕜) {y U : ℝ} (hy : 1 ≤ y) (hU : y ≤ U) :
    ∫ u in y..U, (∑ n ∈ Icc 1 ⌊u⌋₊, c n) / (u : 𝕜) ^ 2 =
      (∑ n ∈ Icc 1 ⌊U⌋₊, c n / (n : 𝕜)) - (∑ n ∈ Icc 1 ⌊y⌋₊, c n / (n : 𝕜))
        - (∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (U : 𝕜) + (∑ n ∈ Icc 1 ⌊y⌋₊, c n) / (y : 𝕜) := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hne : ∀ t ∈ Set.Icc y U, t ≠ 0 := fun t ht => (show (0 : ℝ) < t by linarith [ht.1]).ne'
  have hf_diff : ∀ t ∈ Set.Icc y U, DifferentiableAt ℝ (fun u : ℝ => ((u : 𝕜))⁻¹) t :=
    fun t ht => (hasDerivAt_inv_coe t (hne t ht)).differentiableAt
  have hf_int : IntegrableOn (deriv (fun u : ℝ => ((u : 𝕜))⁻¹)) (Set.Icc y U) := by
    refine ((continuousOn_inv_sq_Icc_of_pos (𝕜 := 𝕜) (U := U) (by linarith)).neg.integrableOn_Icc).congr_fun
      (fun t ht => ?_) measurableSet_Icc
    exact ((hasDerivAt_inv_coe t (hne t ht)).deriv).symm
  have key : ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, ((k : ℝ) : 𝕜)⁻¹ * (if k = 0 then (0 : 𝕜) else c k) =
      ((U : 𝕜))⁻¹ * (∑ k ∈ Icc 0 ⌊U⌋₊, (if k = 0 then (0 : 𝕜) else c k))
        - ((y : 𝕜))⁻¹ * (∑ k ∈ Icc 0 ⌊y⌋₊, (if k = 0 then (0 : 𝕜) else c k))
        - ∫ t in Set.Ioc y U, deriv (fun u : ℝ => ((u : 𝕜))⁻¹) t *
            ∑ k ∈ Icc 0 ⌊t⌋₊, (if k = 0 then (0 : 𝕜) else c k) :=
    sum_mul_eq_sub_sub_integral_mul (fun n => if n = 0 then (0 : 𝕜) else c n) hy0 hU hf_diff hf_int
  have hL : ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, ((k : ℝ) : 𝕜)⁻¹ * (if k = 0 then (0 : 𝕜) else c k) =
      (∑ n ∈ Icc 1 ⌊U⌋₊, c n / (n : 𝕜)) - (∑ n ∈ Icc 1 ⌊y⌋₊, c n / (n : 𝕜)) := by
    calc ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, ((k : ℝ) : 𝕜)⁻¹ * (if k = 0 then (0 : 𝕜) else c k)
        = ∑ k ∈ Ioc ⌊y⌋₊ ⌊U⌋₊, c k / (k : 𝕜) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk0 : k ≠ 0 := (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hk).1).ne'
          rw [if_neg hk0, RCLike.ofReal_natCast]
          ring
      _ = _ := by
          rw [Icc_one_eq_Ioc_zero, Icc_one_eq_Ioc_zero]
          exact eq_sub_of_add_eq' (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_le_floor hU))
  have hint_r : ∫ t in Set.Ioc y U, deriv (fun u : ℝ => ((u : 𝕜))⁻¹) t *
        ∑ k ∈ Icc 0 ⌊t⌋₊, (if k = 0 then (0 : 𝕜) else c k) =
      -∫ t in Set.Ioc y U, (∑ n ∈ Icc 1 ⌊t⌋₊, c n) / (t : 𝕜) ^ 2 := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht0 : t ≠ 0 := (show (0 : ℝ) < t by linarith [ht.1]).ne'
    simp only [(hasDerivAt_inv_coe (𝕜 := 𝕜) t ht0).deriv, sum_Icc_zero_ite_eq_sum_Icc_one]
    ring
  rw [intervalIntegral.integral_of_le hU]
  linear_combination -key + hL + hint_r - ((U : 𝕜))⁻¹ * sum_Icc_zero_ite_eq_sum_Icc_one c ⌊U⌋₊
    + ((y : 𝕜))⁻¹ * sum_Icc_zero_ite_eq_sum_Icc_one c ⌊y⌋₊

end abel

private theorem sum_Icc_eq_mul_sum_div_sub_sum_partial (c : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, c n = (N : ℂ) * (∑ n ∈ Icc 1 N, c n / (n : ℂ))
      - ∑ k ∈ range N, ∑ n ∈ Icc 1 k, c n / (n : ℂ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 N), Finset.sum_Icc_succ_top (Nat.le_add_left 1 N),
      Finset.sum_range_succ, ih]
    have hN : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    have e : ((N : ℂ) + 1) * (c (N + 1) / ((N : ℂ) + 1)) = c (N + 1) := by field_simp
    push_cast
    linear_combination -e

private lemma kronecker_tendsto_zero (c : ℕ → ℂ) (S : ℂ)
    (h : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, c n / (n : ℂ)) atTop (𝓝 S)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, c n) / (N : ℂ)) atTop (𝓝 0) := by
  have hc := h.cesaro_smul
  have hd := h.sub hc
  rw [sub_self] at hd
  refine hd.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [sum_Icc_eq_mul_sum_div_sub_sum_partial c N, Complex.real_smul]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have e : (N : ℂ) * (∑ n ∈ Icc 1 N, c n / (n : ℂ)) / (N : ℂ) = ∑ n ∈ Icc 1 N, c n / (n : ℂ) := by
    field_simp
  push_cast
  linear_combination -e

private lemma kronecker_tendsto_zero_real (c : ℕ → ℂ) (S : ℂ)
    (h : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, c n / (n : ℂ)) atTop (𝓝 S)) :
    Tendsto (fun U : ℝ => (∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (U : ℂ)) atTop (𝓝 0) := by
  have h0 := (kronecker_tendsto_zero c S h).comp (tendsto_nat_floor_atTop (α := ℝ))
  have h1 : Tendsto (fun U : ℝ => ((⌊U⌋₊ : ℝ) / U : ℝ)) atTop (𝓝 1) := tendsto_nat_floor_div_atTop
  have h2 : Tendsto (fun U : ℝ => ((((⌊U⌋₊ : ℝ) / U : ℝ)) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp h1
  have h3 := h0.mul h2
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with U hU
  show (∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (⌊U⌋₊ : ℂ) * ((((⌊U⌋₊ : ℝ) / U : ℝ)) : ℂ) =
    (∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (U : ℂ)
  have hf1 : 1 ≤ ⌊U⌋₊ := (Nat.one_le_floor_iff U).mpr hU
  have hf : (⌊U⌋₊ : ℂ) ≠ 0 := by exact_mod_cast (show ⌊U⌋₊ ≠ 0 by omega)
  have e : (⌊U⌋₊ : ℂ) * ((⌊U⌋₊ : ℂ))⁻¹ = 1 := mul_inv_cancel₀ hf
  push_cast
  linear_combination ((∑ n ∈ Icc 1 ⌊U⌋₊, c n) / (U : ℂ)) * e

theorem smoothedRemainderIntegralFormula : SmoothedRemainderIntegralFormula := by
  intro a S h y hy
  refine ⟨S - ∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ) + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / (y : ℂ), ?_, ?_⟩
  · have hlim : Tendsto (fun U : ℝ => (∑ n ∈ Icc 1 ⌊U⌋₊, a n / (n : ℂ))
          - ∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ) - (∑ n ∈ Icc 1 ⌊U⌋₊, a n) / (U : ℂ)
          + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / (y : ℂ)) atTop
        (𝓝 (S - ∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ) - 0 + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / (y : ℂ))) :=
      (((h.comp (tendsto_nat_floor_atTop (α := ℝ))).sub_const _).sub
        (kronecker_tendsto_zero_real a S h)).add_const _
    rw [sub_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop y] with U hU
    exact (integral_partial_sum_div_sq a hy hU).symm
  · have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (show (0 : ℝ) < y by linarith).ne'
    have hsum : ∑ n ∈ Icc 1 ⌊y⌋₊, a n * ((y / (n : ℝ) - 1 : ℝ) : ℂ) =
        (y : ℂ) * (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℂ)) - ∑ n ∈ Icc 1 ⌊y⌋₊, a n := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      push_cast
      ring
    have e : (y : ℂ) * ((∑ n ∈ Icc 1 ⌊y⌋₊, a n) / (y : ℂ)) = ∑ n ∈ Icc 1 ⌊y⌋₊, a n := by
      field_simp
    unfold Gchi
    rw [hsum]
    linear_combination e

private theorem integral_psumR_sub_div_sq_eq_partial_sums (a : ℕ → ℝ) {y U : ℝ} (hy : 1 ≤ y) (hU : y ≤ U) :
    ∫ u in y..U, (psumR a u - u) / u ^ 2 =
      (∑ n ∈ Icc 1 ⌊U⌋₊, a n / (n : ℝ)) - (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ))
        - (∑ n ∈ Icc 1 ⌊U⌋₊, a n) / U + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y
        - (Real.log U - Real.log y) := by
  have hy0 : 0 < y := by linarith
  have hU0 : 0 < U := by linarith
  have hsplit : (fun u : ℝ => (psumR a u - u) / u ^ 2) =
      fun u : ℝ => (∑ n ∈ Icc 1 ⌊u⌋₊, a n) / u ^ 2 - u⁻¹ := by
    funext u
    rw [sub_div, psumR]
    congr 1
    rcases eq_or_ne u 0 with h | h
    · simp [h]
    · rw [pow_two, div_mul_eq_div_div, div_self h, one_div]
  have hA : IntervalIntegrable (fun u : ℝ => (∑ n ∈ Icc 1 ⌊u⌋₊, a n) / u ^ 2) volume y U :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hU).mpr
      (integrableOn_partial_sum_div_sq (𝕜 := ℝ) a hy)
  have hinv : IntervalIntegrable (fun u : ℝ => u⁻¹) volume y U := by
    refine ContinuousOn.intervalIntegrable (continuousOn_inv₀.mono fun x hx => ?_)
    rw [Set.uIcc_of_le hU] at hx
    exact (show (0 : ℝ) < x by linarith [hx.1]).ne'
  have hA_eq : ∫ u in y..U, (∑ n ∈ Icc 1 ⌊u⌋₊, a n) / u ^ 2 =
      (∑ n ∈ Icc 1 ⌊U⌋₊, a n / (n : ℝ)) - (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ))
        - (∑ n ∈ Icc 1 ⌊U⌋₊, a n) / U + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y :=
    integral_partial_sum_div_sq (𝕜 := ℝ) a hy hU
  rw [hsplit, intervalIntegral.integral_sub hA hinv, integral_inv_of_pos hy0 hU0,
    Real.log_div hU0.ne' hy0.ne', hA_eq]

theorem smoothedRemainderRealIntegralFormula : SmoothedRemainderRealIntegralFormula := by
  intro a h y hy
  refine ⟨-1 - Real.eulerMascheroniConstant + (-(∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ))
    + (∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y + Real.log y), (h.add_const _).congr' ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop y] with U hU
    rw [integral_psumR_sub_div_sq_eq_partial_sums a hy hU, integral_psumR_sub_div_sq_eq_partial_sums a le_rfl (hy.trans hU)]
    simp only [Nat.floor_one, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, div_one,
      Real.log_one]
    ring
  · have hy0 : y ≠ 0 := (show (0 : ℝ) < y by linarith).ne'
    have hsum : ∑ n ∈ Icc 1 ⌊y⌋₊, a n * (y / (n : ℝ) - 1) =
        y * (∑ n ∈ Icc 1 ⌊y⌋₊, a n / (n : ℝ)) - ∑ n ∈ Icc 1 ⌊y⌋₊, a n := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    have e : y * ((∑ n ∈ Icc 1 ⌊y⌋₊, a n) / y) = ∑ n ∈ Icc 1 ⌊y⌋₊, a n := by
      field_simp
    unfold Gone
    rw [hsum]
    linear_combination e

end Formalism.HermitianLattices.GL2PrimeSums
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.SquareMomentFromBound
section
namespace Formalism.HermitianLattices.TraceIntegrality

open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)

theorem moduli_index_formula : Ms_index := by
  intro f N y R2 hf h0 hs
  have hy : ∀ c τ, y c τ ≤ R2 := fun c τ =>
    le_trans (Finset.single_le_sum (fun i _ => h0 c i) (Finset.mem_univ τ)) (hs c)
  have hP : ∏ τ, ∏ c, y c τ ≤ ∏ _τ : Fin f, ∏ _c : Fin N, R2 :=
    Finset.prod_le_prod (fun τ _ => Finset.prod_nonneg fun c _ => h0 c τ)
      (fun τ _ => Finset.prod_le_prod (fun c _ => h0 c τ) (fun c _ => hy c τ))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hP
  have hP0 : 0 ≤ ∏ τ, ∏ c, y c τ := Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun c _ => h0 c τ
  calc (∏ τ, ∏ c, y c τ) ^ 2 ≤ ((R2 ^ N) ^ f) ^ 2 := pow_le_pow_left₀ hP0 hP 2
    _ = R2 ^ (2 * f * N) := by rw [← pow_mul, ← pow_mul]; ring_nf

theorem column_top_entry : LastColumnBound := by
  intro κ lam A bt S hbt hS h0 hl hmid
  have hsucc : ∀ j : Fin (κ + 1), lam j.succ ≤ S := by
    intro j
    by_cases hj : j.succ = Fin.last (κ + 1)
    · rw [hj, hl]; linarith
    · exact (hmid j.succ (Fin.succ_ne_zero j) hj).2
  have hsum : ∑ j : Fin (κ + 1), lam j.succ ≤ (κ + 1) * S := by
    calc ∑ j : Fin (κ + 1), lam j.succ ≤ ∑ _j : Fin (κ + 1), S := Finset.sum_le_sum fun j _ => hsucc j
      _ = (κ + 1) * S := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  constructor
  · unfold wt
    rw [Fin.sum_univ_succ, h0]
    nlinarith
  · unfold wt plus
    rw [Fin.sum_univ_succ, h0, hl]
    have e : ∑ j : Fin (κ + 1), (lam j.succ - -bt) = ∑ j : Fin (κ + 1), lam j.succ + (κ + 1) * bt := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    rw [e]
    nlinarith

theorem weight_change_formula : Weight_change := by
  intro X X' V V' _ _ _ _ K u u' D B hD hB hu hu'
  have hDpos : 0 < D := by linarith
  have A1 : ∀ (Y : Type) [Fintype Y] (w : Y → ℝ) (a : Y → ℝ), (∀ y, 1 / D ≤ w y ∧ w y ≤ 1) →
      (∀ y, 0 ≤ a y) → ∑ y, w y * a y ≤ ∑ y, a y ∧ ∑ y, a y ≤ D * ∑ y, w y * a y := by
    intro Y _ w a hw ha
    constructor
    · exact Finset.sum_le_sum fun y _ => by
        have := (hw y).2
        nlinarith [ha y]
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun y _ => by
        have h1 := (hw y).1
        rw [div_le_iff₀ hDpos] at h1
        nlinarith [ha y]
  refine ⟨fun hK φ => ?_, fun hK φ => ?_⟩
  · obtain ⟨h1, _⟩ := A1 X' u' (fun x => ‖K φ x‖ ^ 2) hu' (fun x => by positivity)
    obtain ⟨_, h2⟩ := A1 X u (fun x => ‖φ x‖ ^ 2) hu (fun x => by positivity)
    calc ∑ x, u' x * ‖K φ x‖ ^ 2 ≤ ∑ x, ‖K φ x‖ ^ 2 := h1
      _ ≤ B * ∑ x, ‖φ x‖ ^ 2 := hK φ
      _ ≤ B * (D * ∑ x, u x * ‖φ x‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hB
      _ = (B * D) * ∑ x, u x * ‖φ x‖ ^ 2 := by ring
  · obtain ⟨_, h1⟩ := A1 X' u' (fun x => ‖K φ x‖ ^ 2) hu' (fun x => by positivity)
    obtain ⟨h2, _⟩ := A1 X u (fun x => ‖φ x‖ ^ 2) hu (fun x => by positivity)
    calc ∑ x, ‖K φ x‖ ^ 2 ≤ D * ∑ x, u' x * ‖K φ x‖ ^ 2 := h1
      _ ≤ D * (B * ∑ x, u x * ‖φ x‖ ^ 2) := mul_le_mul_of_nonneg_left (hK φ) hDpos.le
      _ ≤ D * (B * ∑ x, ‖φ x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hB) hDpos.le
      _ = (B * D) * ∑ x, ‖φ x‖ ^ 2 := by ring

theorem first_zeta_count : PackingCountBound := by
  intro f g u v hf hv hu
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hfv : 0 < (f : ℝ) / v := div_pos (by linarith) hv
  set t := 2 * Real.sqrt u / Real.sqrt (f / v) with ht
  have ht2 : t ^ 2 = 4 * u * v / f := by
    rw [ht, div_pow, mul_pow, Real.sq_sqrt hu, Real.sq_sqrt hfv.le]
    field_simp
    ring
  have huv : 0 ≤ 4 * u * v := by positivity
  have ht2' : t ^ 2 ≤ 4 * u * v := by
    rw [ht2]; exact div_le_self huv hfR
  have key : (1 + t) ^ 2 ≤ 2 * (1 + 4 * u * v) := by nlinarith [sq_nonneg (1 - t)]
  calc (1 + t) ^ (2 * g) = ((1 + t) ^ 2) ^ g := pow_mul _ _ _
    _ ≤ (2 * (1 + 4 * u * v)) ^ g := pow_le_pow_left₀ (sq_nonneg _) key g
    _ = 2 ^ g * (1 + 4 * u * v) ^ g := mul_pow _ _ _

theorem third_zeta_degree_bound : DegreeEqHeadMinusBalance := by
  intro n lam nu
  unfold degZ Formalism.LogVandermondeBounds.flipTwoThree.B0
  rw [Fin.sum_univ_succ, Finset.sum_sub_distrib]
  ring

theorem third_zeta_position_count : CoordinatesBoundedByBalance := by
  intro n lam nu X _
  rw [← Finset.sum_add_sum_compl X (fun i => min (len lam i) (B0 lam nu))]
  have h1 : ∑ i ∈ X, min (len lam i) (B0 lam nu) ≤ X.card * B0 lam nu := by
    calc ∑ i ∈ X, min (len lam i) (B0 lam nu) ≤ ∑ _i ∈ X, B0 lam nu :=
          Finset.sum_le_sum fun i _ => min_le_right _ _
      _ = X.card * B0 lam nu := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ i ∈ Xᶜ, min (len lam i) (B0 lam nu) ≤ ∑ i ∈ Xᶜ, len lam i :=
    Finset.sum_le_sum fun i _ => min_le_left _ _
  linarith

theorem fifth_zeta_transference : LastMinimumSqBoundOfProductBound := by
  intro f k v l1 ln hf hv hl1 hln h hl
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hv2 : 0 < (2 * v) ^ 2 := by positivity
  have h1 : (ln * l1) ^ 2 ≤ (2 * f * k) ^ 2 := pow_le_pow_left₀ (mul_nonneg hln hl1) h 2
  have h2 : ln ^ 2 * ((f : ℝ) / (2 * v) ^ 2) ≤ ln ^ 2 * l1 ^ 2 := mul_le_mul_of_nonneg_left hl (sq_nonneg _)
  have h3 : ln ^ 2 * (f : ℝ) / (2 * v) ^ 2 ≤ 4 * f ^ 2 * k ^ 2 := by
    rw [mul_div_assoc]
    calc ln ^ 2 * ((f : ℝ) / (2 * v) ^ 2) ≤ ln ^ 2 * l1 ^ 2 := h2
      _ = (ln * l1) ^ 2 := by ring
      _ ≤ (2 * f * k) ^ 2 := h1
      _ = 4 * f ^ 2 * k ^ 2 := by ring
  rw [div_le_iff₀ hv2] at h3
  have hf0 : (0 : ℝ) < f := by linarith
  refine le_of_mul_le_mul_right ?_ hf0
  calc ln ^ 2 * (f : ℝ) ≤ 4 * f ^ 2 * k ^ 2 * (2 * v) ^ 2 := h3
    _ = 16 * f * (k : ℝ) ^ 2 * v ^ 2 * f := by ring

theorem square_moment_from_bound : Sqm_from := by
  intro C₀ L logT logg b' m N hC hL hm hT hg hb
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL0 : 0 ≤ L := by linarith
  have h1 : L ≤ m * L := by nlinarith
  have h2 : C₀ * L ≤ C₀ * m * L := by nlinarith [mul_nonneg hC hL0]
  have hs : L + logT + logg ≤ (1 + 2 * C₀) * m * L := by nlinarith
  have hmN : 0 ≤ (m : ℝ) ^ 2 * (N : ℝ) ^ 2 := by positivity
  have hNL : 0 ≤ (N : ℝ) * L := by positivity
  calc (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg) ≤ (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * ((1 + 2 * C₀) * m * L) :=
        mul_le_mul_of_nonneg_left hs hmN
    _ = (N * L) * ((1 + 2 * C₀) * (m : ℝ) ^ 3 * N) := by ring
    _ ≤ (N * L) * b' := mul_le_mul_of_nonneg_left hb hNL
    _ = N * b' * L := by ring

end Formalism.HermitianLattices.TraceIntegrality
end

