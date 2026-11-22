import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle0004

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActUniq
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]

private theorem exTest (z : ℂ) (v : V) (R : ℝ) :
    ∃ x : L V, ∀ᵐ y : ℝ, y ∈ Set.Icc (-R) R → x y = Complex.exp (z * y) • v := by
  have hc : Continuous fun y : ℝ => Complex.exp (z * y) • v := by fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hc.continuousOn
  have hm : MemLp ((Set.Icc (-R) R).indicator fun y : ℝ => Complex.exp (z * y) • v) 2 volume := by
    rw [memLp_indicator_iff_restrict measurableSet_Icc]
    exact MemLp.of_bound hc.aestronglyMeasurable C (ae_restrict_of_forall_mem measurableSet_Icc hC)
  refine ⟨hm.toLp _, ?_⟩
  filter_upwards [hm.coeFn_toLp] with y hy hm'
  rw [hy, Set.indicator_of_mem hm']

private theorem sumAe (S : Finset ℝ) (c : ℝ → V →L[ℂ] V) (x : L V) :
    ∀ᵐ y : ℝ, (∑ t ∈ S, (c t).compLpL 2 volume (sh V t x) : L V) y = ∑ t ∈ S, c t (x (y + t)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero V 2 (volume : Measure ℝ)] with y hy
    simpa using hy
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [ih, Lp.coeFn_add ((c a).compLpL 2 volume (sh V a x)) (∑ t ∈ S, (c t).compLpL 2 volume (sh V t x) : L V),
      (c a).coeFn_compLpL (sh V a x), sh_ae V a x] with y h1 h2 h3 h4
    rw [h2, Pi.add_apply, h1, h3, h4, Finset.sum_insert ha]

private theorem actTest (u : ℝ →₀ (V →L[ℂ] V)) (κ : ℝ → V →L[ℂ] V) (hk : Ker κ) (z : ℂ) (v : V) :
    ∃ R₀ : ℝ, ∀ R, R₀ ≤ R → ∀ x : L V, (∀ᵐ y : ℝ, y ∈ Set.Icc (-R) R → x y = Complex.exp (z * y) • v) →
      ∀ᵐ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 →
        ((u.sum fun t c => c.compLpL 2 volume (sh V t x)) + conv κ x : L V) y =
          Complex.exp (z * y) • ((u.sum fun t c => Complex.exp (z * t) • c) + symb κ z) v := by
  obtain ⟨r, hr⟩ := (u.support.finite_toSet.isCompact.union hk.2.isCompact).isBounded.subset_closedBall (0 : ℝ)
  refine ⟨r + 1, fun R hR x hx => ?_⟩
  have hmem : ∀ t ∈ (u.support : Set ℝ) ∪ tsupport κ, ∀ y ∈ Set.Icc (0 : ℝ) 1, y + t ∈ Set.Icc (-R) R := by
    intro t ht y hy
    have := hr ht
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_le] at this
    constructor <;> linarith [this.1, this.2, hy.1, hy.2]
  have hs : ∀ᵐ y : ℝ, ∀ t ∈ u.support, y + t ∈ Set.Icc (-R) R → x (y + t) = Complex.exp (z * (y + t : ℝ)) • v := by
    rw [Filter.eventually_all_finset]
    intro t _
    exact (measurePreserving_add_right volume t).quasiMeasurePreserving.ae hx
  have hint : Integrable fun t : ℝ => Complex.exp (z * t) • κ t := by
    have h1 : Continuous fun t : ℝ => Complex.exp (z * t) := by fun_prop
    exact (h1.smul hk.1).integrable_of_hasCompactSupport (hk.2.smul_left (f := fun t : ℝ => Complex.exp (z * t)))
  filter_upwards [hs, sumAe u.support u x, (convSpec κ hk x).1,
    Lp.coeFn_add (u.sum fun t c => c.compLpL 2 volume (sh V t x) : L V) (conv κ x)] with y h1 h2 h3 h4 hy
  rw [h4, Pi.add_apply, h3, ContinuousLinearMap.add_apply, smul_add]
  congr 1
  · rw [Finsupp.sum, h2, Finsupp.sum, ContinuousLinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [h1 t ht (hmem t (Or.inl ht) y hy), map_smul, ContinuousLinearMap.smul_apply, smul_smul, ← Complex.exp_add]
    push_cast
    rw [mul_add]
  · rw [symb, ContinuousLinearMap.integral_apply hint, ← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [(measurePreserving_add_left volume y).quasiMeasurePreserving.ae hx] with t ht
    by_cases h : t ∈ tsupport κ
    · rw [ht (hmem t (Or.inr h) y hy), map_smul, ContinuousLinearMap.smul_apply, smul_smul, ← Complex.exp_add]
      push_cast
      rw [mul_add]
    · simp [image_eq_zero_of_notMem_tsupport h]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.actUniq :
    ∀ {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (J : L V →ₗᵢ[ℂ] H) (Y : H →L[ℂ] H) (s s' : ℂ → V →L[ℂ] V), Act J Y s → Act J Y s' → s = s' := by
  rintro H V _ _ _ _ _ _ _ J Y s s' ⟨u, κ, hk, hY, hs⟩ ⟨u', κ', hk', hY', hs'⟩
  funext z
  ext1 v
  obtain ⟨R, hR⟩ := actTest u κ hk z v
  obtain ⟨R', hR'⟩ := actTest u' κ' hk' z v
  obtain ⟨x, hx⟩ := exTest z v (max R R')
  have e := J.injective ((hY x).symm.trans (hY' x))
  have h1 := hR _ (le_max_left R R') x hx
  have h2 := hR' _ (le_max_right R R') x hx
  rw [← hs] at h1
  rw [← hs', ← e] at h2
  by_contra hne
  have h3 : ∀ᵐ y : ℝ, y ∉ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [h1, h2] with y a b hy
    exact hne (smul_right_injective V (Complex.exp_ne_zero (z * y)) ((a hy).symm.trans (b hy)))
  have h4 : volume (Set.Icc (0 : ℝ) 1) = 0 := measure_eq_zero_iff_ae_notMem.2 h3
  simp at h4
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ChebSB
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem chebyshev_image_norm_le {A B : Type} [CommRing A] [Algebra ℂ A] [NormedRing B] (φ : A →+* B)
    (h1 : ‖(1 : B)‖ ≤ 1) (y : A) (r : ℝ) (hr : ‖φ y‖ ≤ r) (m : ℕ) :
    ‖φ (Polynomial.aeval y (Polynomial.Chebyshev.T ℂ (m : ℤ)))‖ ≤ (2 * r + 1) ^ m := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hr
  induction m using Nat.twoStepInduction with
  | zero => simpa using h1
  | one =>
    have : ‖φ y‖ ≤ 2 * r + 1 := by linarith
    simpa using this
  | more m ih0 ih1 =>
    have e : Polynomial.Chebyshev.T ℂ ((m + 2 : ℕ) : ℤ) =
        Polynomial.X * Polynomial.Chebyshev.T ℂ ((m + 1 : ℕ) : ℤ) +
          Polynomial.X * Polynomial.Chebyshev.T ℂ ((m + 1 : ℕ) : ℤ) - Polynomial.Chebyshev.T ℂ (m : ℤ) := by
      push_cast
      rw [Polynomial.Chebyshev.T_add_two]
      ring
    rw [e, map_sub, map_add, map_mul, Polynomial.aeval_X, map_sub, map_add, map_mul]
    set u := φ (Polynomial.aeval y (Polynomial.Chebyshev.T ℂ ((m + 1 : ℕ) : ℤ)))
    set v := φ (Polynomial.aeval y (Polynomial.Chebyshev.T ℂ (m : ℤ)))
    have hp : ‖φ y * u‖ ≤ r * (2 * r + 1) ^ (m + 1) :=
      (norm_mul_le _ _).trans (mul_le_mul hr ih1 (norm_nonneg _) hr0)
    have hq : (2 * r + 1) ^ m ≤ (2 * r + 1) ^ (m + 1) :=
      pow_le_pow_right₀ (by linarith) (Nat.le_succ m)
    have h2 := norm_sub_le (φ y * u + φ y * u) v
    have h3 := norm_add_le (φ y * u) (φ y * u)
    have h4 : (2 * r + 1) ^ (m + 2) = (2 * r + 1) * (2 * r + 1) ^ (m + 1) := by ring
    rw [h4]
    linarith

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.chebSB :
    ∀ {K : Type} [Field K] [NumberField K] {n d : ℕ} (evz : ℂ → PR K n →+* (Eu d →L[ℂ] Eu d)), (∀ z (c : ℂ), evz z (C (C c)) = c • 1) → ∀ M₀, SB (fun z => evz z (C (X none))) M₀ →
      ∃ M₁ : ℝ, 4 ≤ M₁ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ m : ℕ, SB (fun z => evz z (chebP η m)) ((M₁ / η) ^ m) := by
  intro K _ _ n d evz hc M₀ hM
  have hM0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM 0 (by simp))
  refine ⟨4 * M₀ + 4, by linarith, fun η hη hη1 m z hz => ?_⟩
  have h1 : ‖(1 : Eu d →L[ℂ] Eu d)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hX : ‖evz z (C (X none))‖ ≤ M₀ := hM z hz
  have h2η : 0 ≤ 2 / η := by positivity
  have hy : ‖((evz z).comp C) (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ)‖
      ≤ 2 / η * M₀ + 1 := by
    rw [map_sub, map_mul, map_one, RingHom.comp_apply, RingHom.comp_apply, hc, smul_mul_assoc, one_mul]
    refine (norm_sub_le _ _).trans (add_le_add ?_ h1)
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg h2η]
    exact mul_le_mul_of_nonneg_left hX h2η
  have := chebyshev_image_norm_le ((evz z).comp C) h1 _ _ hy m
  refine this.trans (pow_le_pow_left₀ (by positivity) ?_ m)
  have h4 : 4 ≤ 4 / η := by rw [le_div_iff₀ hη]; linarith
  have e : (4 * M₀ + 4) / η = 2 * (2 / η * M₀) + 4 / η := by ring
  rw [e]
  linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.Exponents3
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

open private pow_le_exp_eventually err_bound2 solve_bound2 from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PowLeExpEventually

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.exponents3 :
    ∀ (d : ℕ → ℕ), Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0) → (∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) →
      ∀ (p : ℕ), 0 < p → ∀ (cq a₀ : ℝ), 0 < a₀ → a₀ ≤ 1 → ∃ N : ℝ, ∀ c₁ : ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < a₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ (I : Type) [Fintype I] (a : I → ℝ) (ζ : I → ℂ), (∀ i, η < a i) → (∀ i, ζ i ≠ 0) →
      Function.Injective (fun i => (a i, ζ i)) → ∀ (c : ℕ → I → ℂ) (c' : I → ℂ), (∀ i, Tendsto (fun j => c j i) atTop (𝓝 (c' i))) →
      (∀ s₀ : ℕ, ∃ K : ℝ, ∀ᶠ j : ℕ in atTop, ∀ s ≤ s₀, ∀ s' ≤ s₀,
        ‖∑ i, c j i * (a i : ℂ) ^ d j * (cheb η (j / p + s) (a i) : ℂ) * ζ i ^ (j + s')‖ ≤
        K ^ (d j + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) →
      ∀ i, a₀ ≤ a i → Real.exp (-cq) ≤ ‖ζ i‖ → c' i = 0 := by
  intro d hd hfac p hp cq a₀ h0 h1
  refine ⟨cq + 2 + Real.log (4 / a₀), ?_⟩
  intro c₁
  obtain ⟨A, hA⟩ : ∃ A, A = |c₁ + cq + 1| + 1 := ⟨_, rfl⟩
  have hη₀a : a₀ * Real.exp (-(p * A)) < a₀ := by
    have hA0 : 0 < A := by rw [hA]; positivity
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have : Real.exp (-(p * A)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [mul_pos hp' hA0])
    nlinarith
  refine ⟨a₀ * Real.exp (-(p * A)), by positivity, hη₀a, ?_⟩
  intro η hηp hη
  have hηa : η < a₀ := hη.trans_lt hη₀a
  intro I _ a ζ ha hζ0 hinj c c' hc hbd i hi hζ
  obtain ⟨s₀, K₁, hsep⟩ := UpperTheory.ConvolutionTheory.FX.separate0 η hηp I a ζ ha hζ0 hinj
  obtain ⟨K, hK⟩ := hbd s₀
  have hev : ∀ᶠ j : ℕ in atTop, ‖c j i‖ ≤ (Real.exp (p * A) + 2) * Real.exp (-j) := by
    filter_upwards [hK, hfac (c₁ + cq + 2 + Real.log (4 / a₀)),
      pow_le_exp_eventually d hd ((|K₁| + 1) * |K| / a₀ + 1) (by positivity)] with j hj hF hL
    have h := hsep (j / p) j (fun i => c j i * (a i : ℂ) ^ d j) _ hj i
    have hai : 0 ≤ a i := by linarith
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hai] at h
    exact (solve_bound2 _ _ _ η a₀ cq K₁ K _ _ _ _ (norm_nonneg _) hηp hηa h1 hi hζ
      (by positivity) hL h).trans (err_bound2 p hp c₁ cq a₀ h0 h1 A η hA hηp hη j _ hF)
  have hlim : Tendsto (fun j : ℕ => (Real.exp (p * A) + 2) * Real.exp (-j)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul
      (Real.exp (p * A) + 2)
    simpa using this
  exact tendsto_nhds_unique (hc i) (squeeze_zero_norm' hev hlim)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.PosSymb
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
open scoped InnerProductSpace ComplexOrder

section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

private noncomputable def box (r : ℝ) (e : V) : L V :=
  indicatorConstLp 2 (measurableSet_Ioc (a := (0 : ℝ)) (b := r)) (by simp) e

private theorem box_ae (r : ℝ) (e : V) : ∀ᵐ x : ℝ, box r e x = (Set.Ioc (0 : ℝ) r).indicator (fun _ => e) x :=
  indicatorConstLp_coeFn

private noncomputable def ov (r t : ℝ) : ℝ := max (min r (r - t) - max 0 (-t)) 0

private theorem box_inner (r t : ℝ) (c : V →L[ℂ] V) (e' e : V) :
    ⟪box r e', c.compLpL 2 volume (sh V t (box r e))⟫_ℂ = (ov r t : ℂ) * ⟪e', c e⟫_ℂ := by
  rw [L2.inner_def]
  have h : ∀ᵐ x : ℝ, ⟪box r e' x, c.compLpL 2 volume (sh V t (box r e)) x⟫_ℂ =
      (Set.Ioc (max 0 (-t)) (min r (r - t))).indicator (fun _ => ⟪e', c e⟫_ℂ) x := by
    filter_upwards [box_ae r e', c.coeFn_compLpL (sh V t (box r e)), sh_ae V t (box r e),
      (measurePreserving_add_right volume t).quasiMeasurePreserving.ae (box_ae r e)] with x h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    by_cases a : x ∈ Set.Ioc (0 : ℝ) r
    · by_cases b : x + t ∈ Set.Ioc (0 : ℝ) r
      · rw [Set.indicator_of_mem a, Set.indicator_of_mem b, Set.indicator_of_mem]
        exact ⟨max_lt a.1 (by linarith [b.1]), le_min a.2 (by linarith [b.2])⟩
      · rw [Set.indicator_of_notMem b, map_zero, inner_zero_right, Set.indicator_of_notMem]
        intro h
        exact b ⟨by linarith [(max_lt_iff.1 h.1).2], by linarith [(le_min_iff.1 h.2).2]⟩
    · rw [Set.indicator_of_notMem a, inner_zero_left, Set.indicator_of_notMem]
      intro h
      exact a ⟨(max_lt_iff.1 h.1).1, (le_min_iff.1 h.2).1⟩
  rw [integral_congr_ae h, integral_indicator_const _ measurableSet_Ioc, Real.volume_real_Ioc, Complex.real_smul, ov]

private theorem box_norm (r : ℝ) (hr : 0 ≤ r) (e : V) : ‖box r e‖ = ‖e‖ * Real.sqrt r := by
  rw [box, norm_indicatorConstLp (by simp) (by simp), Real.volume_real_Ioc, sub_zero, max_eq_left hr, Real.sqrt_eq_rpow]
  simp

private theorem ov_le (r t : ℝ) (hr : 0 < r) : |r⁻¹ * ov r t| ≤ 1 := by
  have h0 : 0 ≤ ov r t := le_max_right _ _
  have h1 : ov r t ≤ r := max_le (by linarith [min_le_left r (r - t), le_max_left 0 (-t)]) hr.le
  rw [abs_of_nonneg (by positivity), inv_mul_le_iff₀ hr]
  linarith

private theorem ov_lim (t : ℝ) : Tendsto (fun r : ℝ => r⁻¹ * ov r t) atTop (𝓝 1) := by
  have h : Tendsto (fun r : ℝ => 1 - |t| * r⁻¹) atTop (𝓝 (1 - |t| * 0)) :=
    tendsto_const_nhds.sub (tendsto_inv_atTop_zero.const_mul _)
  rw [mul_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop |t|] with r hr
  have hr0 : 0 < r := (abs_nonneg t).trans_lt hr
  have : ov r t = r - |t| := by
    unfold ov
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h] at hr ⊢
      rw [min_eq_right (by linarith), max_eq_left (by linarith : -t ≤ 0), max_eq_left (by linarith), sub_zero]
    · rw [abs_of_nonpos h] at hr ⊢
      rw [min_eq_left (by linarith), max_eq_right (by linarith : 0 ≤ -t), max_eq_left (by linarith)]
  rw [this]
  field_simp

private theorem conv_lim [FiniteDimensional ℂ V] [CompleteSpace V] (β : ℝ → V →L[ℂ] V) (hk : Ker β) (e' e : V) :
    Tendsto (fun r : ℝ => ((r⁻¹ : ℝ) : ℂ) * ⟪box r e', conv β (box r e)⟫_ℂ) atTop (𝓝 ⟪e', symb β 0 e⟫_ℂ) := by
  have hk1 : Integrable β := hk.1.integrable_of_hasCompactSupport hk.2
  have hk2 : Integrable fun t => β t e := hk1.apply_continuousLinearMap e
  have hk3 : Integrable fun t => ⟪e', β t e⟫_ℂ := hk2.const_inner e'
  have hs : ⟪e', symb β 0 e⟫_ℂ = ∫ t, ((1 : ℝ) : ℂ) * ⟪e', β t e⟫_ℂ := by
    simp only [symb, zero_mul, Complex.exp_zero, one_smul, Complex.ofReal_one, one_mul]
    rw [ContinuousLinearMap.integral_apply hk1, integral_inner hk2]
  have he : ∀ r : ℝ, ((r⁻¹ : ℝ) : ℂ) * ⟪box r e', conv β (box r e)⟫_ℂ =
      ∫ t, ((r⁻¹ * ov r t : ℝ) : ℂ) * ⟪e', β t e⟫_ℂ := fun r => by
    obtain ⟨-, h2, h3⟩ := convSpec β hk (box r e)
    rw [h3, ← integral_inner h2, ← integral_const_mul]
    simp only [box_inner, Complex.ofReal_mul, mul_assoc]
  rw [hs]
  simp only [he]
  refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖⟪e', β t e⟫_ℂ‖) ?_ ?_ hk3.norm ?_
  · refine Eventually.of_forall fun r => AEStronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_) hk3.1
    unfold ov
    fun_prop
  · filter_upwards [eventually_gt_atTop 0] with r hr
    refine Eventually.of_forall fun t => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (ov_le r t hr)
  · exact Eventually.of_forall fun t => ((Complex.continuous_ofReal.tendsto 1).comp (ov_lim t)).mul_const _

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.posSymb :
    ∀ {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (J : L V →ₗᵢ[ℂ] H) (Y : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V), Ker β → Conv J J Y β → 0 ≤ Y → ‖Y‖ ≤ 1 → 0 ≤ symb β 0 ∧ ‖symb β 0‖ ≤ 1 := by
  intro H V _ _ _ _ _ _ _ J Y β hk hc h0 h1
  have hY : ∀ u' u : L V, ⟪u', conv β u⟫_ℂ = ⟪J u', Y (J u)⟫_ℂ := fun u' u => by
    rw [hc u _ (convSpec β hk u).1, J.inner_map_map]
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive Y).1 h0
  constructor
  · have key : ∀ e, 0 ≤ ⟪e, symb β 0 e⟫_ℂ := fun e => by
      refine ge_of_tendsto (conv_lim β hk e e) ?_
      filter_upwards [eventually_gt_atTop 0] with r hr
      rw [hY]
      exact mul_nonneg (Complex.zero_le_real.2 (by positivity)) (hp.inner_nonneg_right _)
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
    intro e
    have h : 0 ≤ ⟪symb β 0 e, e⟫_ℂ := by
      rw [← inner_conj_symm]
      exact star_nonneg_iff.2 (key e)
    obtain ⟨a, b⟩ := Complex.nonneg_iff.1 h
    exact ⟨Complex.ext (by simp) (by simp [← b]), a⟩
  · have key : ∀ e' e, ‖⟪e', symb β 0 e⟫_ℂ‖ ≤ ‖e'‖ * ‖e‖ := fun e' e => by
      refine le_of_tendsto (conv_lim β hk e' e).norm ?_
      filter_upwards [eventually_gt_atTop 0] with r hr
      rw [hY, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_le_iff₀ hr]
      refine (norm_inner_le_norm _ _).trans ?_
      have h2 : ‖Y (J (box r e))‖ ≤ ‖box r e‖ := by
        refine (Y.le_opNorm _).trans ?_
        rw [J.norm_map]
        exact mul_le_of_le_one_left (norm_nonneg _) h1
      rw [J.norm_map]
      refine (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)).trans (le_of_eq ?_)
      rw [box_norm r hr.le, box_norm r hr.le, mul_mul_mul_comm, Real.mul_self_sqrt hr.le, mul_comm]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun e => ?_
    have h := key (symb β 0 e) e
    rw [inner_self_eq_norm_sq_to_K] at h
    simp only [norm_pow, Complex.coe_algebraMap, Complex.norm_real, norm_norm] at h
    rw [one_mul]
    by_contra hh
    push Not at hh
    nlinarith [norm_nonneg e]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.SpecSum
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem specSum_op {d : ℕ} (a Y : Eu d →L[ℂ] Eu d) (y : ℝ → ℂ) (sp : Finset ℝ) (ha : 0 ≤ a) (hc : Commute a Y)
    (hsp : ∀ x, x ∈ sp ↔ 0 < x ∧ Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) (x : ℂ) ≠ ⊥)
    (hY : ∀ x : ℝ, 0 < x → ∀ v ∈ Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) (x : ℂ), Y v = y x • v) (w : Eu d) :
    a (Y w) = ∑ x ∈ sp, ((x : ℂ) * y x) • eigP a x w := by
  have hpos : a.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive a).1 ha
  have hsym : (a : Eu d →ₗ[ℂ] Eu d).IsSymmetric := hpos.isSymmetric
  have htop : (⨆ μ : ℂ, Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) μ) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.1 hsym.orthogonalComplement_iSup_eigenspaces_eq_bot
  have hw : w ∈ (⨆ μ : ℂ, Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) μ) := htop ▸ Submodule.mem_top
  induction hw using Submodule.iSup_induction' with
  | zero => simp
  | add u v _ _ hu hv => simp only [map_add, hu, hv, smul_add, Finset.sum_add_distrib]
  | mem μ v hv =>
    by_cases h0 : v = 0
    · subst h0; simp
    have hav : a v = μ • v := Module.End.mem_eigenspace_iff.1 hv
    have hev : Module.End.HasEigenvalue (a : Eu d →ₗ[ℂ] Eu d) μ :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨hv, h0⟩
    have hre : (starRingEnd ℂ) μ = μ := hsym.conj_eigenvalue_eq_self hev
    obtain ⟨r, rfl⟩ : ∃ r : ℝ, μ = r := ⟨μ.re, (Complex.conj_eq_iff_re.1 hre).symm⟩
    have hr : 0 ≤ r := by
      have h1 := hpos.re_inner_nonneg_right v
      rw [hav, inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
      have h2 : 0 < ‖v‖ ^ 2 := by positivity
      have h3 : RCLike.re ((r : ℂ) * ((‖v‖ : ℂ)) ^ 2) = r * ‖v‖ ^ 2 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]; simp only [RCLike.re_to_complex, Complex.ofReal_re]
      have h4 : 0 ≤ r * ‖v‖ ^ 2 := by rw [← h3]; exact h1
      exact nonneg_of_mul_nonneg_left h4 h2
    have hne : ∀ x : ℝ, x ≠ r → eigP a x v = 0 := by
      intro x hx
      unfold eigP
      rw [Submodule.starProjection_apply_eq_zero_iff]
      intro u hu
      have hx' : (x : ℂ) ≠ r := by exact_mod_cast hx
      exact hsym.orthogonalFamily_eigenspaces hx' ⟨u, hu⟩ ⟨v, hv⟩
    have heq : eigP a r v = v := Submodule.starProjection_eq_self_iff.2 hv
    rcases hr.eq_or_lt with h | h
    · have h1 : a (Y v) = Y (a v) := congrArg (fun T : Eu d →L[ℂ] Eu d => T v) hc.eq
      rw [h1, hav, ← h]
      simp only [Complex.ofReal_zero, zero_smul, map_zero]
      refine (Finset.sum_eq_zero fun x hx => ?_).symm
      rw [hne x (h ▸ ((hsp x).1 hx).1.ne'), smul_zero]
    · have hm : r ∈ sp := (hsp r).2 ⟨h, hev⟩
      rw [Finset.sum_eq_single_of_mem r hm fun x _ hx => by rw [hne x hx, smul_zero], heq, hY r h v hv, map_smul, hav,
        smul_smul, mul_comm]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.specSum :
    ∀ {d d' : ℕ} (a Y Z : Eu d' →L[ℂ] Eu d') (N : Eu d' →ₗ[ℂ] Eu d) (s : Eu d →ₗ[ℂ] Eu d') (y : ℝ → ℂ) (sp : Finset ℝ), 0 ≤ a → Commute a Y →
      (∀ x, x ∈ sp ↔ 0 < x ∧ Module.End.eigenspace (a : Eu d' →ₗ[ℂ] Eu d') (x : ℂ) ≠ ⊥) →
      (∀ x : ℝ, 0 < x → ∀ v ∈ Module.End.eigenspace (a : Eu d' →ₗ[ℂ] Eu d') (x : ℂ), Y v = y x • v) →
      LinearMap.trace ℂ (Eu d) (N ∘ₗ ((a ∘L Y ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) =
        ∑ x ∈ sp, x * y x * LinearMap.trace ℂ (Eu d) (N ∘ₗ ((eigP a x ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) := by
  intro d d' a Y Z N s y sp ha hc hsp hY
  have key : (N ∘ₗ ((a ∘L Y ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) =
      ∑ x ∈ sp, ((x : ℂ) * y x) • (N ∘ₗ ((eigP a x ∘L Z : Eu d' →L[ℂ] Eu d') : Eu d' →ₗ[ℂ] Eu d') ∘ₗ s) := by
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.sum_apply]
    change N (a (Y (Z (s w)))) = ∑ x ∈ sp, ((x : ℂ) * y x) • N (eigP a x (Z (s w)))
    rw [specSum_op a Y y sp ha hc hsp hY, map_sum]
    simp only [map_smul]
  rw [key, map_sum]
  simp only [map_smul, smul_eq_mul]
end

