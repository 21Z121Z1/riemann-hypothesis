import Mathlib
import Formalism.GL3MeanSquares.RankMulPowThreeHalvesLeFourthPower

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.CardUnitsZmodPrimeSq
section
namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset MeasureTheory

theorem hecke_spectral_gap : SW_hecke_gap := by
  intro q M hq hM
  have hq0 : (0 : ℝ) < q := by linarith
  have h1 : q ^ 3 ≤ q ^ M := pow_le_pow_right₀ (by linarith) hM
  have h2 : 0 < q ^ (2 - (M : ℤ)) := zpow_pos hq0 _
  have h3 : q ^ 2 + 1 < q ^ 3 := by nlinarith [sq_nonneg q, mul_pos hq0 hq0]
  have hgap : q ^ 2 + q < q ^ M + q - 1 + q ^ (2 - (M : ℤ)) := by linarith
  refine ⟨hgap, ?_⟩
  intro S hS hle
  by_contra hne
  have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hne)
  have := mul_lt_mul_of_pos_right hgap hSpos
  linarith

private lemma card_units_zmod_prime_sq (p : ℕ) (hp : p.Prime) [NeZero (p ^ 2)] :
    (Finset.univ.filter (fun a : ZMod (p ^ 2) => IsUnit a)).card = p * (p - 1) := by
  classical
  have h1 : Finset.univ.filter (fun a : ZMod (p ^ 2) => IsUnit a)
      = (Finset.univ : Finset (ZMod (p ^ 2))ˣ).map ⟨Units.val, Units.val_injective⟩ := by
    ext a
    constructor
    · intro ha
      obtain ⟨u, hu⟩ := (Finset.mem_filter.mp ha).2
      exact Finset.mem_map.mpr ⟨u, Finset.mem_univ _, hu⟩
    · intro ha
      obtain ⟨u, _, hu⟩ := Finset.mem_map.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨u, hu⟩⟩
  rw [h1, Finset.card_map, Finset.card_univ, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow hp (by norm_num)]
  simp

theorem hecke_operator_terms : SW_hecke_terms := by
  classical
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hp1 : 1 ≤ p := hp.one_lt.le
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  constructor
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card, ZMod.card_units_eq_totient,
      Nat.totient_prime hp]
    simp
    ring
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow hp (by norm_num), Fintype.card_subtype]
    have hU := card_units_zmod_prime_sq (k + 1) hp
    have hN : (Finset.univ.filter (fun a : ZMod ((k + 1) ^ 2) => ¬ IsUnit a)).card = k + 1 := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod ((k + 1) ^ 2))))
        (fun a => IsUnit a)
      rw [hU, Finset.card_univ, ZMod.card] at this
      simp at this
      nlinarith
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (ZMod ((k + 1) ^ 2) × ZMod ((k + 1) ^ 2))))
      (fun v => IsUnit v.1 ∨ IsUnit v.2)
    have hcompl : (Finset.univ.filter
        (fun v : ZMod ((k + 1) ^ 2) × ZMod ((k + 1) ^ 2) => ¬ (IsUnit v.1 ∨ IsUnit v.2)))
        = (Finset.univ.filter (fun a : ZMod ((k + 1) ^ 2) => ¬ IsUnit a)) ×ˢ
          (Finset.univ.filter (fun a : ZMod ((k + 1) ^ 2) => ¬ IsUnit a)) := by
      ext v
      simp [not_or]
    rw [hcompl, Finset.card_product, hN, Finset.card_univ, Fintype.card_prod, ZMod.card] at hsplit
    simp
    nlinarith

theorem height_integral_formula : SW_height_integral := by
  intro M f c R hM hc hR
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 3 := ⟨M - 3, by omega⟩
  have hA : 0 < c * R ^ (2 * f) := by positivity
  have hcongr : ∫ t in (0 : ℝ)..(c * R ^ (2 * f)), (R ^ (2 * f) / t) * t ^ (k + 3 - 1) / t
      = ∫ t in (0 : ℝ)..(c * R ^ (2 * f)), R ^ (2 * f) * t ^ k := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro t ht
    rw [Set.uIoc_of_le hA.le] at ht
    have ht0 : t ≠ 0 := ht.1.ne'
    have : k + 3 - 1 = k + 2 := by omega
    rw [this]
    field_simp
    ring
  rw [hcongr, intervalIntegral.integral_const_mul, integral_pow]
  have e1 : k + 3 - 2 = k + 1 := by omega
  have e2 : 2 * f * (k + 3 - 1) = 2 * f + 2 * f * (k + 1) := by
    have : k + 3 - 1 = 1 + (k + 1) := by omega
    rw [this]; ring
  rw [e1, e2, pow_add R, pow_mul R (2 * f) (k + 1), mul_pow]
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hk' : (((k + 3 : ℕ) : ℝ) - 2) = (k : ℝ) + 1 := by push_cast; ring
  rw [hk']
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow, sub_zero]
  field_simp

theorem real_gaussian_integral : SW_real_gaussian := by
  intro M τ b hτ
  have hne : τ + 2 * (b : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  set β : ℂ := -(Real.pi * Complex.I * (τ + 2 * (b : ℂ))) with hβ
  have hre : 0 < β.re := by
    simp [hβ]
    exact mul_pos Real.pi_pos hτ
  have hint := GaussianFourier.integral_cexp_neg_mul_sq_norm
    (V := EuclideanSpace ℝ (Fin (2 * M))) hre
  have hcongr : (∫ x : EuclideanSpace ℝ (Fin (2 * M)),
        Complex.exp (Real.pi * Complex.I * τ * ((‖x‖ ^ 2 : ℝ) : ℂ)
          + 2 * Real.pi * Complex.I * b * ((‖x‖ ^ 2 : ℝ) : ℂ)))
      = ∫ x : EuclideanSpace ℝ (Fin (2 * M)), Complex.exp (-β * (‖x‖ : ℂ) ^ 2) := by
    congr 1
    ext x
    congr 1
    rw [hβ]
    push_cast
    ring
  rw [hcongr, hint]
  have hfin : ((Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * M))) : ℂ) / 2) = (M : ℂ) := by
    simp
  rw [hfin, Complex.cpow_natCast, ← mul_pow]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hβ]
  field_simp
  ring_nf
  simp

theorem real_place_decay : SW_real_decay := by
  intro M b
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  have hmax : (0 : ℝ) < max 1 |b| := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hz : 2 * max 1 |b| ≤ ‖2 * Complex.I + 2 * (b : ℂ)‖ := by
    have h1 := Complex.abs_im_le_norm (2 * Complex.I + 2 * (b : ℂ))
    have h2 := Complex.abs_re_le_norm (2 * Complex.I + 2 * (b : ℂ))
    simp at h1 h2
    rcases max_cases 1 |b| with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  rw [norm_div]
  have h2 : ‖(2 * Complex.I : ℂ)‖ = 2 := by simp
  rw [h2, div_le_iff₀ (lt_of_lt_of_le (by positivity) hz)]
  calc (2 : ℝ) = (max 1 |b|)⁻¹ * (2 * max 1 |b|) := by field_simp
    _ ≤ (max 1 |b|)⁻¹ * ‖2 * Complex.I + 2 * (b : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hmax.le)

end Formalism.HermitianLattices.GenusMassVolumes
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.FourierTransformScaledInner
section
namespace Formalism.HermitianLattices.GenusMassVolumes

open MeasureTheory Module
open scoped FourierTransform

private lemma sublevel_set_eq_closed_ball (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    {x : EuclideanSpace ℝ (Fin N) | ‖x‖ ^ 2 ≤ t} = Metric.closedBall 0 (Real.sqrt t) := by
  ext x
  simp only [Set.mem_ofPred_eq, mem_closedBall_zero_iff]
  rw [Real.le_sqrt (norm_nonneg x) ht]

theorem volume_euclidean_ball : ball_volume := by
  intro n t ht
  rw [sublevel_set_eq_closed_ball _ t ht]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (2 * 0))) (Real.sqrt t) = Set.univ := by
      ext x
      have : x = 0 := by ext i; exact absurd i.2 (by simp)
      simp [this, Real.sqrt_nonneg]
    rw [hs]
    have hv : volume (Set.univ : Set (EuclideanSpace ℝ (Fin (2 * 0)))) = 1 := by
      have h1 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (2 * 0))
      have := h1.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
      rw [Set.preimage_univ] at this
      rw [this]
      have hpi : (Set.univ : Set (Fin (2 * 0) → ℝ)) = Set.pi Set.univ (fun _ => Set.univ) := by simp
      rw [hpi, volume_pi_pi]
      simp
    rw [hv]
    simp
  · have : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
    have : Nontrivial (EuclideanSpace ℝ (Fin (2 * n))) := by
      apply Module.nontrivial_of_finrank_pos (R := ℝ)
      simp; omega
    have hk : finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) = 2 * n := by simp
    rw [InnerProductSpace.volume_closedBall_of_dim_even hk, hk, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.sqrt_nonneg t),
      ENNReal.toReal_ofReal (by positivity), pow_mul, Real.sq_sqrt ht]
    ring

theorem sphere_surface_volume : SphereVolumeDerivative := by
  intro M hM
  have hev : (fun t : ℝ => (2 : ℝ) ^ M *
      (volume {x : EuclideanSpace ℝ (Fin (2 * M)) | ‖x‖ ^ 2 ≤ t}).toReal) =ᶠ[nhds 1]
      fun t : ℝ => (2 : ℝ) ^ M * (Real.pi ^ M * t ^ M / (M.factorial : ℝ)) := by
    filter_upwards [lt_mem_nhds (zero_lt_one' ℝ)] with t ht
    rw [volume_euclidean_ball M t ht.le]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h1 : HasDerivAt (fun t : ℝ => t ^ M) ((M : ℝ) * 1 ^ (M - 1)) 1 := hasDerivAt_pow M 1
  have h2 := ((h1.const_mul (Real.pi ^ M)).div_const (M.factorial : ℝ)).const_mul ((2 : ℝ) ^ M)
  have he : (2 * Real.pi) ^ M / ((M - 1).factorial : ℝ) =
      2 ^ M * (Real.pi ^ M * ((M : ℝ) * 1 ^ (M - 1)) / (M.factorial : ℝ)) := by
    clear h2 h1 hev
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    have hk : ((k.factorial : ℝ)) ≠ 0 := by positivity
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      one_pow, mul_one]
    rw [mul_pow]
    field_simp
  rw [he]
  exact h2

private lemma fourier_transform_scaled_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (g : V → ℂ) (ξ : V) :
    (∫ x, Complex.exp (-(2 * Real.pi * Complex.I * ((2 * inner ℝ x ξ : ℝ) : ℂ))) * g x) =
      𝓕 g ((2 : ℝ) • ξ) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, inner_smul_right]
  congr 2
  push_cast
  ring

theorem self_dual_lattice_measure : SelfDualMeasure := by
  intro M φ FT x
  have hFT : ∀ g ξ, FT g ξ = (2 : ℂ) ^ M * 𝓕 g ((2 : ℝ) • ξ) := by
    intro g ξ
    simp only [FT]
    rw [fourier_transform_scaled_inner]
  rw [hFT]
  have h1 : FT (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) =
      fun ξ => (2 : ℂ) ^ M * 𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) ((2 : ℝ) • ξ) :=
    funext (hFT _)
  rw [h1, Real.fourier_eq]
  have h2 : (∫ v : EuclideanSpace ℝ (Fin (2 * M)), Real.fourierChar (-inner ℝ v ((2 : ℝ) • x)) •
        ((2 : ℂ) ^ M * 𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) ((2 : ℝ) • v))) =
      ∫ v : EuclideanSpace ℝ (Fin (2 * M)),
        (fun w => Real.fourierChar (-inner ℝ w x) •
          ((2 : ℂ) ^ M * 𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) w)) ((2 : ℝ) • v) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [inner_smul_left, inner_smul_right]
    simp
  rw [h2, Measure.integral_comp_smul volume (fun w => Real.fourierChar (-inner ℝ w x) •
          ((2 : ℂ) ^ M * 𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) w)) (2 : ℝ)]
  have h3 : (∫ w : EuclideanSpace ℝ (Fin (2 * M)), Real.fourierChar (-inner ℝ w x) •
        ((2 : ℂ) ^ M * 𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ) w)) =
      (2 : ℂ) ^ M * 𝓕 (𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ)) x := by
    rw [Real.fourier_eq, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [Circle.smul_def, smul_eq_mul]
    ring
  rw [h3]
  have h4 : 𝓕 (𝓕 (φ : EuclideanSpace ℝ (Fin (2 * M)) → ℂ)) x = φ (-x) := by
    have := φ.continuous.fourierInv_fourier_eq φ.integrable (𝓕 φ).integrable
    have h5 := congrFun this (-x)
    rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h5
    exact h5
  rw [h4]
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin (2 * M))) = 2 * M := by simp
  rw [hfr, abs_of_pos (by positivity), Complex.real_smul]
  push_cast
  have h2M : ((2 : ℂ) ^ M) ≠ 0 := pow_ne_zero _ two_ne_zero
  have h22 : ((2 : ℂ) ^ (2 * M)) = 2 ^ M * 2 ^ M := by rw [two_mul, pow_add]
  generalize φ (-x) = c
  rw [h22]
  field_simp

end Formalism.HermitianLattices.GenusMassVolumes
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.OneAddInvPowLeExpOne
section
namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset
open Formalism.LogVandermondeBounds.StandardLattice

private lemma sum_Ico_cast_eq_mul_add_triangular (k j : ℕ) :
    ∑ M ∈ Ico (k + 1) (k + j + 1), (M : ℝ) = (j : ℝ) * k + ((j : ℝ) + 1) * j / 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show k + (j + 1) + 1 = k + j + 1 + 1 by ring, Finset.sum_Ico_succ_top (by omega), ih]
    push_cast
    ring

theorem mass_coefficients : BracketCoefficients := by
  intro k m hk hm
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hI : k - 1 + (j + 1) + 1 = k + j + 1 := by omega
  rw [hI, sum_Ico_cast_eq_mul_add_triangular]
  push_cast
  constructor
  · field_simp <;> ring
  · field_simp <;> ring

theorem log_mass_formula : LogMassFormula := by
  intro f m k vE massk massr Lval hf hm hk hvE hmk hL hmass
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hI : k - 1 + (j + 1) + 1 = k + j + 1 := by omega
  rw [hI] at hL hmass ⊢
  have hf' : (0:ℝ) < f := Nat.cast_pos.mpr hf
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hpi : 0 < vE / Real.pi := div_pos hvE Real.pi_pos
  have h2v : 0 < 2 * vE := by linarith
  have hs : 0 < Real.sqrt ((2 * vE) ^ f) := Real.sqrt_pos.2 (pow_pos h2v f)
  have hA : ∀ M : ℕ, 0 < (((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M := fun M =>
    mul_pos (by exact_mod_cast Nat.factorial_pos _) (pow_pos hpi M)
  have hpos : ∀ M ∈ Finset.Ico (k + 1) (k + j + 1),
      0 < ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M :=
    fun M hM => mul_pos (div_pos (pow_pos (hA M) f) hs) (hL M hM)
  have hterm : ∀ M ∈ Finset.Ico (k + 1) (k + j + 1),
      Real.log (((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M) =
        f * Real.log (((M - 1).factorial : ℕ) : ℝ) + f * Real.log (vE / Real.pi) * (M : ℝ)
          - f / 2 * Real.log (2 * vE) + Real.log (Lval M) := by
    intro M hM
    have hfac : (0:ℝ) < (((M - 1).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [Real.log_mul (div_pos (pow_pos (hA M) f) hs).ne' (hL M hM).ne',
      Real.log_div (pow_pos (hA M) f).ne' hs.ne', Real.log_pow, Real.log_mul hfac.ne' (pow_pos hpi M).ne',
      Real.log_pow, Real.log_sqrt (pow_pos h2v f).le, Real.log_pow]
    ring
  have hprod : massr / massk = ∏ M ∈ Finset.Ico (k + 1) (k + j + 1),
      ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M := by
    rw [hmass, mul_div_cancel_left₀ _ hmk.ne']
  have hc : (Finset.Ico (k + 1) (k + j + 1)).card = j := by rw [Nat.card_Ico]; omega
  rw [hprod, Real.log_prod (fun M hM => (hpos M hM).ne'), Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_const, hc, nsmul_eq_mul, sum_Ico_cast_eq_mul_add_triangular]
  push_cast
  field_simp
  ring

private lemma one_add_inv_pow_le_exp_one (N : ℕ) (hN : 1 ≤ N) :
    (1 + 1 / (N : ℝ)) ^ N ≤ Real.exp 1 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  calc (1 + 1 / (N : ℝ)) ^ N ≤ (Real.exp (1 / N)) ^ N := by
        gcongr
        linarith [Real.add_one_le_exp (1 / (N : ℝ))]
    _ = Real.exp 1 := by rw [← Real.exp_nat_mul, mul_one_div_cancel hN']

theorem mass_corollary : PowerProductTwoSidedBounds := by
  intro f k T X Γ Dstar dstar dM lo hi hf hk hfk2 hT hX hΓ hD hd hXD hlow hup hdM hlo hhi
  have hf' : (0:ℝ) < f := Nat.cast_pos.mpr hf
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hN : (0:ℝ) < f * k := mul_pos hf' hk'
  have hN1 : 1 ≤ f * k := by simpa using Nat.mul_le_mul hf hk
  have hΓ0 : 0 < Γ := by linarith
  have hT0 : 0 < T := by linarith
  set r : ℝ := -(2:ℝ) / ((f:ℝ) * k) with hr
  set Y : ℝ := X * Γ ^ r with hY
  have hYpos : 0 < Y := mul_pos hX (Real.rpow_pos_of_pos hΓ0 r)
  have hrN : r * ((f * k : ℕ) : ℝ) = -2 := by rw [hr, Nat.cast_mul, div_mul_cancel₀ _ hN.ne']
  have hYN : Y ^ (f * k) = Dstar * (Γ⁻¹) ^ 2 / dstar := by
    rw [hY, mul_pow, hXD, ← Real.rpow_natCast (Γ ^ r), ← Real.rpow_mul hΓ0.le, hrN, Real.rpow_neg hΓ0.le,
      Real.rpow_two, inv_pow]
    ring
  have hdY : dstar * Y ^ (f * k) = Dstar * (Γ⁻¹) ^ 2 := by rw [hYN]; field_simp
  have hTk : 1 ≤ T ^ k := one_le_pow₀ (by linarith)
  have hTkpos : 0 < T ^ k := lt_of_lt_of_le one_pos hTk
  have hB : (T ^ k - 1) ^ f ≤ Y ^ (f * k) * Real.exp 1 := by
    calc (T ^ k - 1) ^ f ≤ (T ^ k) ^ f := by gcongr <;> linarith
      _ = T ^ (f * k) := by rw [← pow_mul, mul_comm]
      _ ≤ (Y * (1 + 1 / ((f:ℝ) * k))) ^ (f * k) := by gcongr <;> linarith
      _ = Y ^ (f * k) * (1 + 1 / ((f * k : ℕ) : ℝ)) ^ (f * k) := by rw [mul_pow, Nat.cast_mul]
      _ ≤ Y ^ (f * k) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left (one_add_inv_pow_le_exp_one _ hN1) (pow_nonneg hYpos.le _)
  have hq : (f:ℝ) * (1 / T ^ k) ≤ 1 / 2 := by
    have h2k : (2:ℝ) ^ k ≤ T ^ k := by gcongr
    have h2f : (2 * f : ℝ) ≤ 2 ^ k := by exact_mod_cast hfk2
    rw [mul_one_div, div_le_iff₀ hTkpos]
    linarith
  have hle1 : 1 / T ^ k ≤ 1 := (div_le_one hTkpos).2 hTk
  have hBer : 1 + (f:ℝ) * (-(1 / T ^ k)) ≤ (1 + -(1 / T ^ k)) ^ f := one_add_mul_le_pow (by linarith) f
  have hfac : T ^ k - 1 = T ^ k * (1 + -(1 / T ^ k)) := by
    rw [mul_add, mul_one, mul_neg, mul_one_div_cancel hTkpos.ne']
    ring
  have hA : Y ^ (f * k) / 2 ≤ (T ^ k - 1) ^ f := by
    have h1 : Y ^ (f * k) ≤ (T ^ k) ^ f := by
      rw [← pow_mul, mul_comm k f]
      exact pow_le_pow_left₀ hYpos.le hlow _
    have h2 : 1 / 2 ≤ (1 + -(1 / T ^ k)) ^ f := by linarith
    have h3 : 0 ≤ (T ^ k) ^ f := pow_nonneg hTkpos.le _
    have h4 := mul_le_mul_of_nonneg_left h2 h3
    calc Y ^ (f * k) / 2 = Y ^ (f * k) * (1 / 2) := by ring
      _ ≤ (T ^ k) ^ f * (1 / 2) := mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ ≤ (T ^ k) ^ f * (1 + -(1 / T ^ k)) ^ f := h4
      _ = (T ^ k - 1) ^ f := by rw [hfac, mul_pow]
  have hΓr : Γ ^ r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hΓ (by
    rw [hr]; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hN.le)
  have hYX : Y ≤ X := mul_le_of_le_one_right hX.le hΓr
  have hinv : 1 / ((f:ℝ) * k) ≤ 1 := (div_le_one hN).2 (by exact_mod_cast hN1)
  have hT2X : T ≤ 2 * X := by nlinarith
  have hlogY : Real.log Y = Real.log X + r * Real.log Γ := by
    rw [hY, Real.log_mul hX.ne' (Real.rpow_pos_of_pos hΓ0 r).ne', Real.log_rpow hΓ0]
  have hr2 : r * Real.log Γ = -(2 * Real.log Γ / ((f:ℝ) * k)) := by rw [hr]; ring
  have hYT : Real.log Y ≤ Real.log T := Real.log_le_log hYpos hlow
  have hT2 : Real.log T ≤ Real.log 2 + Real.log X := by
    rw [← Real.log_mul two_ne_zero hX.ne']
    exact Real.log_le_log hT0 hT2X
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdM, ← hdY]
    calc dstar * Y ^ (f * k) / 2 = dstar * (Y ^ (f * k) / 2) := by ring
      _ ≤ dstar * (T ^ k - 1) ^ f := mul_le_mul_of_nonneg_left hA hd.le
  · rw [hdM, ← hdY]
    calc dstar * (T ^ k - 1) ^ f ≤ dstar * (Y ^ (f * k) * Real.exp 1) := mul_le_mul_of_nonneg_left hB hd.le
      _ = Real.exp 1 * (dstar * Y ^ (f * k)) := by ring
  · linarith
  · linarith

theorem corollary_needs_degree : MeanSquareRequiresDegreeBound := by
  intro c hc
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc (by norm_num : (1 / 2 : ℝ) < 1)
  have h1 : ((1:ℝ) / 2) ^ (n + 1) < c :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)) hn
  have h2 : ((1:ℝ) / 2) ^ (n + 1) * 2 ^ (n + 1) = 1 := by rw [← mul_pow]; norm_num
  have h3 := mul_lt_mul_of_pos_right h1 (pow_pos (by norm_num : (0:ℝ) < 2) (n + 1))
  rw [h2] at h3
  have h4 : (0:ℝ) ≤ 1 / (((n + 1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ)) := by positivity
  refine ⟨n + 1, 1, 2, 2, 1, 2 ^ (n + 1), 1, by omega, le_rfl, le_rfl, by norm_num, le_rfl, by positivity,
    one_pos, by simp, by simp, ?_, ?_⟩
  · rw [Real.one_rpow, mul_one]
    linarith
  · norm_num
    linarith

theorem joint_variation_bound : NormalizedLogRatioVandermondeVariation := by
  intro f k Dstar massk Ipi V u u' hf hk hD hm hI hV
  have hf' : (0:ℝ) < f := Nat.cast_pos.mpr hf
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hfac : (0:ℝ) < ∏ i ∈ range k, ((i.factorial : ℕ) : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  have hF : ∀ x : ℕ → ℝ, 0 < vandN x k → 0 < dimVN x k := fun x hx => by
    unfold dimVN
    exact div_pos hx hfac
  have hlog : ∀ x : ℕ → ℝ, 0 < vandN x k →
      Real.log (dimVN x k) = Real.log (vandN x k) - Real.log (∏ i ∈ range k, ((i.factorial : ℕ) : ℝ)) :=
    fun x hx => by
      unfold dimVN
      rw [Real.log_div hx.ne' hfac.ne']
  have hP : ∀ w : ℕ → ℕ → ℝ, (∀ ρ, ρ < f → 0 < vandN (w ρ) k) →
      Real.log (Dstar / (massk * Ipi * ∏ ρ ∈ range f, dimVN (w ρ) k)) =
        Real.log Dstar - Real.log (massk * Ipi) - ∑ ρ ∈ range f, Real.log (dimVN (w ρ) k) := by
    intro w hw
    have hpos : ∀ ρ ∈ range f, 0 < dimVN (w ρ) k := fun ρ hρ => hF _ (hw ρ (Finset.mem_range.1 hρ))
    rw [Real.log_div hD.ne' (mul_pos (mul_pos hm hI) (Finset.prod_pos hpos)).ne',
      Real.log_mul (mul_pos hm hI).ne' (Finset.prod_pos hpos).ne',
      Real.log_prod (fun ρ hρ => (hpos ρ hρ).ne')]
    ring
  rw [hP u (fun ρ hρ => (hV ρ hρ).1), hP u' (fun ρ hρ => (hV ρ hρ).2.1)]
  have hsum : |∑ ρ ∈ range f, Real.log (dimVN (u ρ) k) - ∑ ρ ∈ range f, Real.log (dimVN (u' ρ) k)| ≤ f * V := by
    rw [← Finset.sum_sub_distrib]
    calc |∑ ρ ∈ range f, (Real.log (dimVN (u ρ) k) - Real.log (dimVN (u' ρ) k))|
        ≤ ∑ ρ ∈ range f, |Real.log (dimVN (u ρ) k) - Real.log (dimVN (u' ρ) k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ρ ∈ range f, V := by
        apply Finset.sum_le_sum
        intro ρ hρ
        have h := hV ρ (Finset.mem_range.1 hρ)
        rw [hlog _ h.1, hlog _ h.2.1]
        have e : Real.log (vandN (u ρ) k) - Real.log (∏ i ∈ range k, ((i.factorial : ℕ) : ℝ)) -
            (Real.log (vandN (u' ρ) k) - Real.log (∏ i ∈ range k, ((i.factorial : ℕ) : ℝ))) =
            Real.log (vandN (u ρ) k) - Real.log (vandN (u' ρ) k) := by ring
        rw [e]
        exact h.2.2
      _ = f * V := by simp
  have hN : (0:ℝ) < 1 / ((f:ℝ) * k) := by positivity
  have e : 1 / ((f:ℝ) * k) * (Real.log Dstar - Real.log (massk * Ipi) - ∑ ρ ∈ range f, Real.log (dimVN (u ρ) k)) -
      1 / ((f:ℝ) * k) * (Real.log Dstar - Real.log (massk * Ipi) - ∑ ρ ∈ range f, Real.log (dimVN (u' ρ) k)) =
      1 / ((f:ℝ) * k) * -(∑ ρ ∈ range f, Real.log (dimVN (u ρ) k) - ∑ ρ ∈ range f, Real.log (dimVN (u' ρ) k)) := by
    ring
  rw [e, abs_mul, abs_neg, abs_of_pos hN]
  calc 1 / ((f:ℝ) * k) * |∑ ρ ∈ range f, Real.log (dimVN (u ρ) k) - ∑ ρ ∈ range f, Real.log (dimVN (u' ρ) k)|
      ≤ 1 / ((f:ℝ) * k) * (f * V) := mul_le_mul_of_nonneg_left hsum hN.le
    _ = V / k := by field_simp

end Formalism.HermitianLattices.GenusMassVolumes
end

