import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0159
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0181
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0168

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumModerateMeasurabl
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.LatBd

theorem continuous_eisensteinLatticeTermWeightS_exponent {j : ℕ} (hj : 1 ≤ j) (z : ℂ) : Continuous fun s : ℝ => trm j s z := by
  by_cases hz : z = 0
  · subst hz
    have : ∀ s : ℝ, trm j s 0 = 0 := fun s => by
      simp [trm, zero_pow (by omega : j ≠ 0)]
    simp only [this]; exact continuous_const
  · unfold trm
    refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
    exact continuous_const.rpow (continuous_const.mul continuous_id) fun _ => Or.inl (norm_ne_zero_iff.2 hz)

theorem lin_ne_zero (x : ℤ × ℤ) (hx : x ≠ 0) (τ : ℍ) : (x.1 : ℂ) * (τ : ℂ) + x.2 ≠ 0 := by
  intro h
  have him : (x.1 : ℝ) * τ.im = 0 := by
    have := congrArg Complex.im h
    simpa using this
  have h1 : x.1 = 0 := by
    rcases mul_eq_zero.1 him with h' | h'
    · exact_mod_cast h'
    · exact absurd h' τ.im_pos.ne'
  have h2 : x.2 = 0 := by
    have := congrArg Complex.re h
    simp [h1] at this
    exact_mod_cast this
  exact hx (Prod.ext h1 h2)

theorem trm_cont_tau {j : ℕ} (hj : 1 ≤ j) (s : ℝ) (x : ℤ × ℤ) :
    Continuous fun τ : ℍ => trm j s ((x.1 : ℂ) * τ + x.2) := by
  by_cases hx : x = 0
  · subst hx
    have : ∀ τ : ℍ, trm j s (((0 : ℤ × ℤ).1 : ℂ) * τ + (0 : ℤ × ℤ).2) = 0 := fun τ => by
      simp [trm, zero_pow (by omega : j ≠ 0)]
    simp only [this]; exact continuous_const
  · have hc : Continuous fun τ : ℍ => (x.1 : ℂ) * (τ : ℂ) + x.2 :=
      (continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const
    unfold trm
    refine ((hc.pow j).inv₀ fun τ => pow_ne_zero _ (lin_ne_zero x hx τ)).mul
      (Complex.continuous_ofReal.comp ((continuous_norm.comp hc).rpow_const fun τ => Or.inl ?_))
    exact norm_ne_zero_iff.2 (lin_ne_zero x hx τ)

theorem dif_cont {α : Type*} [TopologicalSpace α] (L : ℕ) (v : ℤ × ℤ) (F : α → ℤ × ℤ → ℂ)
    (h : ∀ x, Continuous fun a => F a x) (x : ℤ × ℤ) : Continuous fun a => dif L v (F a) x := by
  unfold dif
  exact (h x).sub (continuous_const.mul (continuous_finset_sum _ fun r _ => h _))

theorem difdif_le (L : ℕ) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) (u : ℤ × ℤ → ℝ) (h : ∀ x, ‖dif L v F x‖ ≤ u x)
    (x : ℤ × ℤ) : ‖dif L v (dif L v F) x‖ ≤ u x + (L : ℝ)⁻¹ * ∑ r ∈ Finset.range L, u (x + (r : ℤ) • v) := by
  show ‖dif L v F x - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, dif L v F (x + (r : ℤ) • v)‖ ≤ _
  refine (norm_sub_le _ _).trans (add_le_add (h x) ?_)
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => h _))
    (inv_nonneg.2 (Nat.cast_nonneg L))

theorem hasSum_dom (L : ℕ) (hL : 0 < L) (v : ℤ × ℤ) (u : ℤ × ℤ → ℝ) {S : ℝ} (hu : HasSum u S) :
    HasSum (fun x => u x + (L : ℝ)⁻¹ * ∑ r ∈ Finset.range L, u (x + (r : ℤ) • v)) (2 * S) := by
  have h1 : ∀ r : ℕ, HasSum (fun x => u (x + (r : ℤ) • v)) S := fun r =>
    (Equiv.addRight ((r : ℤ) • v)).hasSum_iff.2 hu
  have h2 := hasSum_sum (s := Finset.range L) fun r _ => h1 r
  have h3 := hu.add (h2.mul_left ((L : ℝ)⁻¹))
  convert h3 using 1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp; ring

theorem measurable_tsum_any {X I : Type} [MeasurableSpace X] [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (g : X → I → ℂ) (hg : ∀ i, Measurable fun x => g x i) :
    Measurable fun x => ∑' i, g x i := by
  have e : ∀ x, ∑' i, g x i = ∫ i, g x i ∂(Measure.count : Measure I) := fun x => by
    by_cases hf : Summable (g x)
    · have hi : Integrable (g x) (Measure.count : Measure I) := by
        rw [integrable_count_iff]; exact summable_norm_iff.mpr hf
      rw [integral_countable hi]; simp [measureReal_def]
    · rw [tsum_eq_zero_of_not_summable hf, integral_undef]
      intro hi; rw [integrable_count_iff] at hi; exact hf (summable_norm_iff.mp hi)
  simp only [e]
  have hm : Measurable fun p : X × I => g p.1 p.2 := measurable_from_prod_countable_left hg
  exact (StronglyMeasurable.integral_prod_right' (ν := (Measure.count : Measure I))
    hm.stronglyMeasurable).measurable

end GlobalTheory.EisM.LatBd

namespace GlobalTheory.EisM.LatBd

theorem lat_mod_meas_tendsto : ∀ (j L : ℕ) (Φ : ℤ × ℤ → ℂ), 2 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) →
    (∃ (C : ℝ) (A : ℕ), ∀ (s : ℝ) (τ : ℍ), 0 ≤ s → s ≤ 1 → ‖lat j s L (0, 1) Φ τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹)) ∧
    (∀ s : ℝ, Measurable (lat j s L (0, 1) Φ)) ∧
    ∀ τ : ℍ, Tendsto (fun s : ℝ => lat j s L (0, 1) Φ τ) (𝓝[>] 0) (𝓝 (lat j 0 L (0, 1) Φ τ)) := by
  intro j L Φ hj hL ⟨B, hB⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hj1 : 1 ≤ j := by omega
  obtain ⟨C, A, hrow⟩ := GlobalTheory.T.eisensteinLattice_rowDifference_summable_bound j L hj hL

  have dom : ∀ τ : ℍ, ∃ U : ℤ × ℤ → ℝ, ∃ S : ℝ, HasSum U (2 * S) ∧ S ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x, ‖Φ x * dif L (0, 1) (dif L (0, 1)
        fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x‖ ≤ B * U x := by
    intro τ
    obtain ⟨u, hus, hule, hu⟩ := hrow τ
    refine ⟨_, _, hasSum_dom L hL (0, 1) u hus.hasSum, hule, fun s hs0 hs1 x => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hB x) (difdif_le L (0, 1) _ u (fun x => hu s x hs0 hs1) x) (norm_nonneg _) hB0
  refine ⟨⟨2 * B * C, A, fun s τ hs0 hs1 => ?_⟩, fun s => ?_, fun τ => ?_⟩
  · obtain ⟨U, S, hU, hS, hb⟩ := dom τ
    have h := tsum_of_norm_bounded (hU.mul_left B) (hb s hs0 hs1)
    have hpos : 0 ≤ B * 2 := by positivity
    calc ‖lat j s L (0, 1) Φ τ‖ ≤ B * (2 * S) := h
      _ = (B * 2) * S := by ring
      _ ≤ (B * 2) * (C * (τ.im ^ A + (τ.im ^ A)⁻¹)) := mul_le_mul_of_nonneg_left hS hpos
      _ = 2 * B * C * (τ.im ^ A + (τ.im ^ A)⁻¹) := by ring
  · unfold lat
    refine measurable_tsum_any (fun (τ : ℍ) x => Φ x * dif L (0, 1) (dif L (0, 1)
      fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x) fun x => ?_
    exact (continuous_const.mul (dif_cont L (0, 1) _
      (dif_cont L (0, 1) _ (fun y => trm_cont_tau hj1 s y)) x)).measurable
  · obtain ⟨U, S, hU, -, hb⟩ := dom τ
    unfold lat
    refine tendsto_tsum_of_dominated_convergence (bound := fun x => B * U x) (hU.mul_left B).summable
      (fun x => ?_) ?_
    · have hc : Continuous fun s : ℝ => Φ x * dif L (0, 1) (dif L (0, 1)
          fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x :=
        continuous_const.mul (dif_cont L (0, 1) _ (dif_cont L (0, 1) _ (fun y => continuous_eisensteinLatticeTermWeightS_exponent hj1 _)) x)
      exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
      exact hb s hs.1.le hs.2.le

end GlobalTheory.EisM.LatBd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumQExpansion
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section
namespace GlobalTheory.LatQ

theorem hat_bounded (L : ℕ) (φ : ZMod L → ℂ) : ∃ C : ℝ, ∀ x, ‖hat φ x‖ ≤ C := by
  refine ⟨∑ y ∈ Finset.range L, ‖φ (y : ZMod L)‖, fun x => ?_⟩
  unfold hat
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [norm_mul]
  have : ‖cexp (2 * π * Complex.I * ((y : ℂ) * (x : ℂ)) / (L : ℂ))‖ = 1 := by
    have h : (2 * π * Complex.I * ((y : ℂ) * (x : ℂ)) / (L : ℂ)) = ((2 * π * y * x / L : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  rw [this, mul_one]

theorem trm_zero_eq (j : ℕ) (w : ℂ) : trm j 0 w = (w ^ j)⁻¹ := by
  simp [trm]

theorem trm_neg (j : ℕ) (w : ℂ) : trm j 0 (-w) = (-1) ^ j * trm j 0 w := by
  rw [trm_zero_eq, trm_zero_eq, neg_pow, mul_inv, ← inv_pow, inv_neg, inv_one]

theorem trm_tendsto (j : ℕ) (hj : 1 ≤ j) (z : ℂ) :
    Tendsto (fun d : ℤ => trm j 0 (z + d)) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun d : ℤ => |(d : ℝ)|) cofinite atTop :=
    (tendsto_norm_cocompact_atTop.comp Int.tendsto_coe_cofinite)
  have h2 : Tendsto (fun d : ℤ => ‖z + d‖) cofinite atTop := by
    refine tendsto_atTop_mono (fun d => ?_) (tendsto_atTop_add_const_right _ (-‖z‖) h1)
    have := norm_sub_norm_le ((d : ℂ)) (-z)
    simp only [Complex.norm_intCast, norm_neg, sub_neg_eq_add] at this
    linarith [show ‖(d : ℂ) + z‖ = ‖z + d‖ by rw [add_comm]]
  have h3 : Tendsto (fun d : ℤ => ‖z + d‖ ^ j) cofinite atTop :=
    (tendsto_pow_atTop (by omega)).comp h2
  refine h3.inv_tendsto_atTop.congr (fun d => ?_)
  simp [trm_zero_eq, norm_inv, norm_pow]

theorem sum_range_eq_univ (L : ℕ) (hL : 0 < L) (φ : ZMod L → ℂ) (f : ℕ → ZMod L)
    (hf : Set.InjOn f (Finset.range L)) :
    haveI : NeZero L := ⟨hL.ne'⟩
    ∑ r ∈ Finset.range L, φ (f r) = ∑ y, φ y := by
  haveI : NeZero L := ⟨hL.ne'⟩
  rw [← Finset.sum_image (fun x hx y hy h => hf hx hy h)]
  congr 1
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn hf, Finset.card_range, ZMod.card]

theorem kills (L : ℕ) (hL : 0 < L) (φ : ZMod L → ℂ) (d : ℤ) :
    ∑ r ∈ Finset.range L, φ ((d - r : ℤ) : ZMod L) = hat φ 0 := by
  have h1 : hat φ 0 = ∑ y ∈ Finset.range L, φ (y : ZMod L) := by simp [hat]
  rw [h1, sum_range_eq_univ L hL φ, sum_range_eq_univ L hL φ]
  · intro a ha b hb h
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have := congrArg ZMod.val h
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact this
  · intro a ha b hb h
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
    have h2 : (d - (b : ℤ)) - (d - (a : ℤ)) = (a : ℤ) - b := by ring
    rw [h2] at h
    have h3 := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega

theorem phi_bounded (L : ℕ) (hL : 0 < L) (φ : ZMod L → ℂ) : ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C := by
  haveI : NeZero L := ⟨hL.ne'⟩
  exact ⟨∑ y, ‖φ y‖, fun y => Finset.single_le_sum (f := fun y => ‖φ y‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ y)⟩

theorem latF_mul (L : ℕ) (hL : 0 < L) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (k d : ℤ) :
    latF L b φ (k * L, d) = b k * φ (d : ZMod L) := by
  have : (L : ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  simp [latF, Int.mul_ediv_cancel _ this]

theorem latF_ndvd (L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (x : ℤ × ℤ) (h : ¬ (L : ℤ) ∣ x.1) :
    latF L b φ x = 0 := by
  simp [latF, h]

theorem row_summable (j L : ℕ) (hj : 1 ≤ j) (hL : 0 < L) (A : ℤ → ℂ) (hA : ∃ C : ℝ, ∀ d, ‖A d‖ ≤ C) (τ : ℍ) (c : ℤ) :
    Summable fun d : ℤ => A d * dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (c, d) := by
  obtain ⟨C, hC⟩ := hA
  have hs := (GlobalTheory.T.summable_regularizedEisensteinLatticeTerm j L (0, 1) τ hj hL).prod_factor c
  refine (hs.mul_left C).of_norm_bounded (fun d => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC d) (norm_nonneg _)

theorem row_lim (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (hj : 1 ≤ j) (hL : 0 < L) (h0 : hat φ 0 = 0)
    (τ : ℍ) (k : ℤ) :
    Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, b k * φ (d : ZMod L) * trm j 0 (((k * L : ℤ) : ℂ) * τ + d))
      atTop (𝓝 (∑' d : ℤ, latF L b φ (k * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (k * L, d))) := by
  simp_rw [latF_mul L hL b φ k]
  obtain ⟨C, hC⟩ := phi_bounded L hL φ
  have hA : ∃ C : ℝ, ∀ d : ℤ, ‖b k * φ (d : ZMod L)‖ ≤ C :=
    ⟨‖b k‖ * C, fun d => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)⟩
  have hK : ∀ d : ℤ, ∑ r ∈ Finset.range L, b k * φ (((d - r : ℤ)) : ZMod L) = 0 := by
    intro d; rw [← Finset.mul_sum, kills L hL φ d, h0, mul_zero]
  exact GlobalTheory.RowLim.rowlim L (fun d => b k * φ (d : ZMod L)) (fun d => trm j 0 (((k * L : ℤ) : ℂ) * τ + d))
    (fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (k * L) hL hA hK (fun d => rfl)
    (trm_tendsto j hj _) (row_summable j L hj hL _ hA τ _)

theorem lip_all (j L : ℕ) (φ : ZMod L → ℂ) (z : ℂ) (hj : 1 ≤ j) (hL : 0 < L) (hz : 0 < z.im) (h0 : hat φ 0 = 0) :
    Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, φ (d : ZMod L) * trm j 0 (z + d)) atTop
      (𝓝 ((-2 * π * Complex.I / L) ^ j / (j - 1).factorial *
        ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (j - 1) * hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L))) := by
  rcases (show j = 1 ∨ 2 ≤ j by omega) with rfl | hj2
  · convert GlobalTheory.T.lipschitz_weight_one_periodic_mean_zero L φ z hL hz h0 using 2
    simp
  · exact GlobalTheory.T.lipschitz_formula_periodic_weight j L φ z hj2 hL hz

theorem row_pos (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (hj : 1 ≤ j) (hL : 0 < L) (h0 : hat φ 0 = 0)
    (τ : ℍ) (n : ℕ) :
    ∑' d : ℤ, latF L b φ (((n + 1 : ℕ) : ℤ) * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (((n + 1 : ℕ) : ℤ) * L, d) =
      (-2 * π * Complex.I / L) ^ j / (j - 1).factorial *
        (b (n + 1 : ℕ) * ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (j - 1) * hat φ (m + 1 : ℕ) *
          cexp (2 * π * Complex.I * (m + 1 : ℕ) * ((n + 1 : ℕ) * τ))) := by
  have hlim := row_lim j L b φ hj hL h0 τ ((n + 1 : ℕ) : ℤ)
  have hz : 0 < ((((((n + 1 : ℕ) : ℤ) * L : ℤ)) : ℂ) * (τ : ℂ)).im := by
    have : (((((n + 1 : ℕ) : ℤ) * L : ℤ)) : ℂ) = (((n + 1 : ℕ) * L : ℕ) : ℝ) := by push_cast; ring
    rw [this, Complex.im_ofReal_mul]
    exact mul_pos (by exact_mod_cast Nat.mul_pos (Nat.succ_pos n) hL) τ.im_pos
  have h2 := (lip_all j L φ _ hj hL hz h0).const_mul (b ((n + 1 : ℕ) : ℤ))
  have h3 : (fun R : ℕ => b ((n + 1 : ℕ) : ℤ) * ∑ d ∈ Finset.Icc (-(R : ℤ)) R,
      φ (d : ZMod L) * trm j 0 (((((n + 1 : ℕ) : ℤ) * L : ℤ) : ℂ) * τ + d)) =
      (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R,
        b ((n + 1 : ℕ) : ℤ) * φ (d : ZMod L) * trm j 0 (((((n + 1 : ℕ) : ℤ) * L : ℤ) : ℂ) * τ + d)) := by
    funext R; rw [Finset.mul_sum]; simp_rw [mul_assoc]
  rw [h3] at h2
  rw [tendsto_nhds_unique hlim h2]
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have h4 : ∀ m : ℕ, cexp (2 * π * Complex.I * ((m + 1 : ℕ) : ℂ) * ((((((n + 1 : ℕ) : ℤ) * L : ℤ)) : ℂ) * τ) / L) =
      cexp (2 * π * Complex.I * ((m + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) * τ)) := by
    intro m; congr 1; push_cast; field_simp
  simp_rw [h4]
  ring

theorem row_neg (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (hj : 1 ≤ j) (hL : 0 < L) (h0 : hat φ 0 = 0)
    (hpar : ∀ x y : ℤ, b (-x) * φ (-(y : ZMod L)) = (-1) ^ j * (b x * φ y)) (τ : ℍ) (k : ℤ) :
    ∑' d : ℤ, latF L b φ ((-k) * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) ((-k) * L, d) =
    ∑' d : ℤ, latF L b φ (k * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (k * L, d) := by
  refine tendsto_nhds_unique (row_lim j L b φ hj hL h0 τ (-k)) ?_
  refine (row_lim j L b φ hj hL h0 τ k).congr (fun R => ?_)
  refine Finset.sum_nbij' (fun d => -d) (fun d => -d) ?_ ?_ ?_ ?_ ?_
  · intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega
  · intro d hd; simp only [Finset.mem_Icc] at hd ⊢; omega
  · intro d _; simp
  · intro d _; simp
  · intro d _
    have e1 : (((-k) * L : ℤ) : ℂ) * τ + ((-d : ℤ) : ℂ) = -(((k * L : ℤ) : ℂ) * τ + (d : ℂ)) := by push_cast; ring
    have e2 := hpar k d
    rw [e1, trm_neg, show ((-d : ℤ) : ZMod L) = -(d : ZMod L) by push_cast; rfl]
    have : ((-1 : ℂ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-((-1 : ℂ) ^ j * trm j 0 (((k * L : ℤ) : ℂ) * τ + (d : ℂ)))) * e2 -
      (b k * φ (d : ZMod L) * trm j 0 (((k * L : ℤ) : ℂ) * τ + (d : ℂ))) * this

theorem row_zero_indep (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (τ τ' : ℍ) :
    ∑' d : ℤ, latF L b φ ((0 : ℤ) * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) ((0 : ℤ) * L, d) =
    ∑' d : ℤ, latF L b φ ((0 : ℤ) * L, d) *
        dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ' + y.2)) ((0 : ℤ) * L, d) := by
  congr 1; funext d; congr 1
  simp [dif]

theorem latF_bounded (L : ℕ) (hL : 0 < L) (b : ℤ → ℂ) (φ : ZMod L → ℂ) (hb : ∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) :
    ∃ C : ℝ, ∀ x, ‖latF L b φ x‖ ≤ C := by
  obtain ⟨Cb, hCb⟩ := hb
  obtain ⟨Cφ, hCφ⟩ := phi_bounded L hL φ
  have hb0 : 0 ≤ Cb := (norm_nonneg _).trans (hCb 0)
  have hφ0 : 0 ≤ Cφ := (norm_nonneg _).trans (hCφ 0)
  refine ⟨Cb * Cφ, fun x => ?_⟩
  unfold latF; split_ifs
  · rw [norm_mul]; exact mul_le_mul (hCb _) (hCφ _) (norm_nonneg _) hb0
  · simp only [norm_zero]; positivity

theorem tsum_rows (L : ℕ) (hL : 0 < L) (F : ℤ → ℂ) (κ S : ℂ) (T : ℕ → ℂ) (hFs : Summable F)
    (hz : ∀ k, ¬ (L : ℤ) ∣ k → F k = 0) (hneg : ∀ k : ℤ, F ((-k) * L) = F (k * L))
    (hpos : ∀ n : ℕ, F (((n + 1 : ℕ) : ℤ) * L) = κ * T n) (hT : HasSum T S) :
    ∑' k, F k = F ((0 : ℤ) * L) + 2 * κ * S := by
  have hinj : Function.Injective (fun n : ℤ => n * (L : ℤ)) :=
    fun x y h => mul_right_cancel₀ (by exact_mod_cast hL.ne' : (L : ℤ) ≠ 0) h
  have hsupp : Function.support F ⊆ Set.range (fun n : ℤ => n * (L : ℤ)) := by
    intro k hk
    by_contra hn
    exact hk (hz k fun ⟨n, hn'⟩ => hn ⟨n, by rw [hn', mul_comm]⟩)
  rw [← hinj.tsum_eq hsupp]
  have hg : Summable fun n : ℤ => F (n * L) := hFs.comp_injective hinj
  have hsucc : Function.Injective (fun n : ℕ => (n : ℤ) + 1) := fun x y h => by simpa using h
  have hnsucc : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := fun x y h => by simpa using h
  rw [tsum_of_add_one_of_neg_add_one (f := fun n : ℤ => F (n * L)) (hg.comp_injective hsucc) (hg.comp_injective hnsucc)]
  have hpos' : ∀ n : ℕ, F (((n : ℤ) + 1) * L) = κ * T n := fun n => by rw [← hpos n, Nat.cast_succ]
  simp only [hneg, hpos', tsum_mul_left, hT.tsum_eq]
  ring

theorem lat_qexp : ∀ (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ), 1 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) →
    hat φ 0 = 0 → (∀ x y : ℤ, b (-x) * φ (-(y : ZMod L)) = (-1) ^ j * (b x * φ y)) →
    ∃ c : ℂ, PolyB (eis j c (hat φ) b) ∧ ∀ τ : ℍ, lat j 0 L (0, 1) (latF L b φ) τ =
      2 * (-2 * π * Complex.I / L) ^ j / (j - 1).factorial * qs (eis j c (hat φ) b) τ := by
  intro j L b φ hj hL hb h0 hpar
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hκ : ((-2 * π * Complex.I / L) ^ j / (j - 1).factorial : ℂ) ≠ 0 := by
    refine div_ne_zero (pow_ne_zero _ (div_ne_zero ?_ hL')) (by exact_mod_cast (Nat.factorial_pos _).ne')
    refine mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  generalize hκdef : ((-2 * π * Complex.I / L) ^ j / (j - 1).factorial : ℂ) = κ at hκ
  obtain ⟨K, hK⟩ : ∃ K : ℂ, ∀ τ : ℍ, ∑' d : ℤ, latF L b φ ((0 : ℤ) * L, d) *
      dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) ((0 : ℤ) * L, d) = K :=
    ⟨_, fun τ => row_zero_indep j L b φ τ UpperHalfPlane.I⟩
  refine ⟨K / (2 * κ), (GlobalTheory.T.coeffEisensteinSeriesTwisted_qExpansion_double j _ (hat φ) b (hat_bounded L φ) hb).1, fun τ => ?_⟩
  have hq := (GlobalTheory.T.coeffEisensteinSeriesTwisted_qExpansion_double j (K / (2 * κ)) (hat φ) b (hat_bounded L φ) hb).2.2 τ
  obtain ⟨CΦ, hCΦ⟩ := latF_bounded L hL b φ hb
  have hs : Summable fun x : ℤ × ℤ => latF L b φ x *
      dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) x := by
    refine ((GlobalTheory.T.summable_regularizedEisensteinLatticeTerm j L (0, 1) τ hj hL).mul_left CΦ).of_norm_bounded (fun x => ?_)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hCΦ x) (norm_nonneg _)
  have hrows := tsum_rows L hL (fun k => ∑' d : ℤ, latF L b φ (k, d) *
      dif L (0, 1) (dif L (0, 1) fun y : ℤ × ℤ => trm j 0 ((y.1 : ℂ) * τ + y.2)) (k, d)) κ _ _ hs.prod
    (fun k hk => by simp only [latF_ndvd L b φ (k, _) hk, zero_mul, tsum_zero])
    (fun k => row_neg j L b φ hj hL h0 hpar τ k)
    (fun n => by rw [← hκdef]; exact row_pos j L b φ hj hL h0 τ n) hq
  have e : (2 * (-2 * π * Complex.I / L) ^ j / (j - 1).factorial : ℂ) = 2 * κ := by rw [← hκdef]; ring
  rw [e, lat, hs.tsum_prod, hrows]
  beta_reduce
  rw [hK τ]
  field_simp
  ring

end GlobalTheory.LatQ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmallTracesSubgroupGaloisTowerTop
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

theorem small_traces_subgroup : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (H : Subgroup (Gal p Ω)), H ≤ ⨅ n, Gn T n →
    ∀ (S : Finset Ω) (j : ℕ), 1 ≤ j → ∃ (y : Ω) (E : Finset (Gal p Ω)), IsInt p y ∧
      (∀ g ∈ E, g ∈ H) ∧ (∀ h ∈ H, ∃! g, g ∈ E ∧ h y = g y ∧ ∀ s ∈ S, h s = g s) ∧
      ∑ g ∈ E, g y = T.ζ j - 1 := by
  intro p _ Ω _ _ hp2 hclo T H hH S j hj
  classical
  obtain ⟨v, hvint, hvgal, -, hv1, hsep⟩ := GlobalTheory.T.exists_valuation_almostEtale_towerFixer p Ω hp2 hclo T
  obtain ⟨U, -, hUfin, hUS, hUsep⟩ := hsep S
  let K : Subgroup (Gal p Ω) := ⨅ n, Gn T n
  let H' : Subgroup ↥K := H.subgroupOf K
  let U' : Subgroup ↥H' := U.subgroupOf H'
  haveI : U'.FiniteIndex := inferInstance
  haveI : Finite (↥H' ⧸ U') := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (↥H' ⧸ U') := Fintype.ofFinite _
  have hU'sep : AlmostSep v U' := GlobalTheory.T.fixedFieldAlmostEtale_subgroupOf Ω v ↥K U H' hUsep
  have hsmul : ∀ (h : ↥H') (x : Ω), h • x = ((h : ↥K) : Gal p Ω) x := fun _ _ => rfl
  have hinv : ∀ (h : ↥H') (x : Ω), v (h • x) = v x := fun h x => by rw [hsmul]; exact hvgal _ x
  have hfixζ : ∀ h : ↥H', h • (T.ζ j - 1) = T.ζ j - 1 := by
    intro h
    have hm : ((h : ↥K) : Gal p Ω) ∈ Gn T j := (Subgroup.mem_iInf.mp (h : ↥K).2) j
    have h1 : ((h : ↥K) : Gal p Ω) (T.ζ j) = T.ζ j := ((Basic.mem_gn T j _).mp hm).1
    rw [hsmul, map_sub, map_one, h1]
  have hve : v (T.ζ j - 1) < 1 := (GlobalTheory.T.valuation_tower_zeta_sub_one p Ω hp2 T v hv1 j hj).1
  obtain ⟨y₀, hy₀, hy₀le, htr⟩ := GlobalTheory.T.exists_integer_cosetRepresentativeTrace_eq_of_lt_one Ω v ↥H' hinv U' hU'sep (T.ζ j - 1) hfixζ hve
  have hS : ∀ s ∈ S, s ∈ Fix Ω U' := fun s hs g =>
    hUS s hs ⟨((g : ↥H') : ↥K), Subgroup.mem_subgroupOf.mp g.2⟩
  obtain ⟨y, D, E', hy, huniq, hsum⟩ := GlobalTheory.T.exists_reps_of_cosetRepresentativeTrace Ω ↥H' U' S hS y₀ hy₀
  let ι : ↥H' ↪ Gal p Ω := ⟨fun h => ((h : ↥K) : Gal p Ω), fun a b hab => Subtype.ext (Subtype.ext hab)⟩
  have hιH : ∀ h : ↥H', ι h ∈ H := fun h => Subgroup.mem_subgroupOf.mp h.2
  have hιs : ∀ (h : ↥H') (x : Ω), ι h x = h • x := fun _ _ => rfl
  have hy₀int : IsInt p y₀ := (hvint y₀).mp hy₀le
  refine ⟨y, E'.map ι, ?_, ?_, ?_, ?_⟩
  · rw [hy]
    exact IsIntegral.sum _ fun d _ => by rw [← hιs]; exact Basic.isInt_gal _ hy₀int
  · intro g hg
    obtain ⟨g', -, rfl⟩ := Finset.mem_map.mp hg
    exact hιH g'
  · intro h hh
    let h' : ↥H' := ⟨⟨h, hH hh⟩, Subgroup.mem_subgroupOf.mpr hh⟩
    obtain ⟨g', ⟨hg'E, hg'y, hg'S⟩, hg'u⟩ := huniq h'
    refine ⟨ι g', ⟨Finset.mem_map_of_mem ι hg'E, ?_, ?_⟩, ?_⟩
    · rw [hιs]; exact hg'y
    · intro s hs; rw [hιs]; exact hg'S s hs
    · rintro g ⟨hgE, hgy, hgS⟩
      obtain ⟨g'', hg''E, rfl⟩ := Finset.mem_map.mp hgE
      congr 1
      refine hg'u g'' ⟨hg''E, ?_, ?_⟩
      · rw [← hιs]; exact hgy
      · intro s hs; rw [← hιs]; exact hgS s hs
  · rw [Finset.sum_map]
    exact (Finset.sum_congr rfl fun g _ => hιs g y).trans (hsum.trans htr)

end GlobalTheory.K5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TrivialEigenvalueCongruenceVanishesStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_eigenvalue_congruence_vanishes : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ (E : Type) [Field E] [Algebra ℤ_[l] E], Function.Injective (algebraMap ℤ_[l] E) → ∀ (w : ℕ) (Γ : Subgroup SL(2, ℤ)) (M₀ : ℕ), 0 < M₀ → CongruenceSubgroup.Gamma M₀ ≤ Γ → ∀ p ∈ abelian₂ X l E, p.2 ∈ Triv E w Γ → p.1 = 0 := by
  first | exact @GlobalTheory.KZ.H3.lam_fst_eq_zero_of_triv | exact GlobalTheory.KZ.H3.lam_fst_eq_zero_of_triv | (intros; apply GlobalTheory.KZ.H3.lam_fst_eq_zero_of_triv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZmodCocycleEqCoboundaryOfUnitTwistedCocycleStatement
section
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locallyConstant_zmod_coboundary_of_mu_cocycle : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (c : (Ω ≃ₐ[K] Ω) → (Ω ≃ₐ[K] Ω) → ZMod N) (v : (Ω ≃ₐ[K] Ω) → Ωˣ), IsLocallyConstant v →
  (∀ g h, (v g : Ω) * g (v h) = ζ ^ (c g h).val * v (g * h)) →
  ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧ ∀ g h, c g h = η h - η (g * h) + η g := by
  first | exact @GlobalTheory.Hilbert90CupCoboundary.zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle | exact GlobalTheory.Hilbert90CupCoboundary.zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle | (intros; apply GlobalTheory.Hilbert90CupCoboundary.zmod_cocycle_eq_coboundary_of_unit_twisted_cocycle <;> assumption)
end

