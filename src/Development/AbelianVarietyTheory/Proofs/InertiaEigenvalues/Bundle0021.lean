import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitFrobeniusIterateProductEq
section
namespace GlobalTheory.FrobeniusProduct

theorem exists_adic_limit {A : Type} [CommRing A] (I : Ideal A) [IsPrecomplete I A]
    (s : ℕ → A) (hs : ∀ r : ℕ, ∃ N : ℕ, ∀ m ≥ N, s (m + 1) - s m ∈ I ^ r) :
    ∃ L : A, ∀ r : ℕ, ∃ N : ℕ, ∀ m ≥ N, s m - L ∈ I ^ r := by
  have hsm : ∀ J : Ideal A, J • (⊤ : Submodule A A) = J := fun J => by simp
  choose N hN using hs
  have tele : ∀ r a b, (∀ k ≥ a, s (k + 1) - s k ∈ I ^ r) → a ≤ b → s b - s a ∈ I ^ r := by
    intro r a b h hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      have := (I ^ r).add_mem (h b hab) ih
      convert this using 1
      ring
  set N' : ℕ → ℕ := fun r => ∑ j ∈ Finset.range (r + 1), N j with hN'
  have hN'ge : ∀ r, N r ≤ N' r := fun r =>
    Finset.single_le_sum (f := N) (fun j _ => Nat.zero_le _) (Finset.self_mem_range_succ r)
  have hN'mono : Monotone N' := fun a b hab =>
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hab))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := A) inferInstance
    (f := fun r => s (N' r)) (by
      intro m n hmn
      rw [SModEq.sub_mem, hsm]
      have := tele m (N' m) (N' n) (fun k hk => hN m k (le_trans (hN'ge m) hk)) (hN'mono hmn)
      have := (I ^ m).neg_mem this
      simpa using this)
  refine ⟨L, fun r => ⟨N' r, fun m hm => ?_⟩⟩
  have h1 := tele r (N' r) m (fun k hk => hN r k (le_trans (hN'ge r) hk)) hm
  have h2 : s (N' r) - L ∈ I ^ r := by
    have := hL r
    rw [SModEq.sub_mem, hsm] at this
    exact this
  have := (I ^ r).add_mem h1 h2
  convert this using 1
  ring

theorem exists_unit_iterate_mul_eq :
    ∀ (A : Type) [CommRing A] (p : ℕ), IsAdicComplete (Ideal.span {(p : A)}) A →
      ∀ (φ : A →+* A) (u : A), IsUnit u →
        (∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑φ)^[m] u - 1 ∈ Ideal.span {(p : A)} ^ r) →
          ∀ n : ℕ, 0 < n → ∃ c : A, IsUnit c ∧ (⇑φ)^[n] c * (⇑φ)^[n - 1] u = c := by
  intro A _ p hc φ u hu hconv n hn
  haveI := hc
  set I : Ideal A := Ideal.span {(p : A)} with hI
  have hsm : ∀ J : Ideal A, J • (⊤ : Submodule A A) = J := fun J => by simp
  obtain ⟨w, hw⟩ : ∃ w : ℕ → A, w = fun k => (⇑φ)^[n * k + (n - 1)] u := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ → A, s = fun N => ∏ k ∈ Finset.range N, w k := ⟨_, rfl⟩
  have hwconv : ∀ r, ∃ M, ∀ k ≥ M, w k - 1 ∈ I ^ r := fun r => by
    obtain ⟨M, hM⟩ := hconv r
    exact ⟨M, fun k hk => by rw [hw]; exact hM _ (by nlinarith)⟩
  have hcauchy : ∀ r, ∃ N, ∀ m ≥ N, s (m + 1) - s m ∈ I ^ r := by
    intro r
    obtain ⟨M, hM⟩ := hwconv r
    refine ⟨M, fun m hm => ?_⟩
    have e : s (m + 1) - s m = s m * (w m - 1) := by
      simp only [hs, Finset.prod_range_succ]; ring
    rw [e]
    exact Ideal.mul_mem_left _ _ (hM m hm)
  obtain ⟨c, hc'⟩ := exists_adic_limit I s hcauchy
  have haus : ∀ x : A, (∀ r : ℕ, x ∈ I ^ r) → x = 0 := fun x hx =>
    IsHausdorff.haus (I := I) (M := A) inferInstance x (fun r => by rw [SModEq.zero, hsm]; exact hx r)
  have hmap : ∀ k (x : A) r, x ∈ I ^ r → (⇑φ)^[k] x ∈ I ^ r := by
    intro k x r hx
    have := Ideal.mem_map_of_mem (φ ^ k) hx
    rwa [Ideal.map_pow, hI, Ideal.map_span, Set.image_singleton, map_natCast,
      RingHom.coe_pow] at this
  have hsub : ∀ x y : A, (⇑φ)^[n] (x - y) = (⇑φ)^[n] x - (⇑φ)^[n] y := by
    intro x y; rw [← RingHom.coe_pow]; exact map_sub _ _ _
  have key : ∀ N, (⇑φ)^[n] (s N) * (⇑φ)^[n - 1] u = s (N + 1) := by
    intro N
    simp only [hs, Finset.prod_range_succ']
    rw [← RingHom.coe_pow, map_prod]
    congr 1
    · apply Finset.prod_congr rfl
      intro k _
      simp only [RingHom.coe_pow, hw]
      rw [← Function.iterate_add_apply]
      congr 1
      ring
    · simp [hw]
  have hwunit : ∀ k, IsUnit (w k) := fun k => by
    rw [hw]; show IsUnit ((⇑φ)^[n * k + (n - 1)] u)
    rw [← RingHom.coe_pow]; exact hu.map _
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := hc' 1
    have h1 : s N - c ∈ I := by simpa using hN N le_rfl
    have hsN : IsUnit (s N) := by
      rw [hs]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
        (fun k _ => hwunit k)
    obtain ⟨v, hv⟩ := hsN
    have hy : -(s N - c) ∈ (⊥ : Ideal A).jacobson :=
      IsAdicComplete.le_jacobson_bot I (I.neg_mem h1)
    have hu' := (Ideal.mem_jacobson_bot.mp hy) (↑v⁻¹ : A)
    have heq : c = (-(s N - c) * (↑v⁻¹ : A) + 1) * ↑v := by
      rw [add_mul, mul_assoc, Units.inv_mul, mul_one, one_mul, hv]; ring
    rw [heq]
    exact hu'.mul v.isUnit
  · refine sub_eq_zero.mp (haus _ fun r => ?_)
    obtain ⟨N, hN⟩ := hc' r
    have e : (⇑φ)^[n] c * (⇑φ)^[n - 1] u - c =
        -((⇑φ)^[n] (s N - c) * (⇑φ)^[n - 1] u) + (s (N + 1) - c) := by
      rw [← key N, hsub]; ring
    rw [e]
    exact (I ^ r).add_mem ((I ^ r).neg_mem (Ideal.mul_mem_right _ _ (hmap n _ r (hN N le_rfl))))
      (hN (N + 1) (by omega))

end GlobalTheory.FrobeniusProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitOfSumEqZero
section
open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

namespace GlobalTheory.IntegerUnitBound

open scoped Classical in

theorem exists_unit_norm_add_le (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : logSpace E, ∃ u : (𝓞 E)ˣ,
      ∀ w, |v w + logEmbedding E (Additive.ofMul u) w| ≤ C := by
  let B := (basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E)
  refine ⟨∑ i, ‖B i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun v => ?_⟩

  have hmem : -((ZSpan.floor B v : logSpace E)) ∈ unitLattice E := by
    rw [← Module.Basis.ofZLatticeBasis_span ℝ (unitLattice E) (basisUnitLattice E)]
    exact neg_mem (ZSpan.floor B v).2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.1 hmem
  refine ⟨Additive.toMul x, fun w => ?_⟩
  have hsum : v + logEmbedding E (Additive.ofMul (Additive.toMul x)) = ZSpan.fract B v := by
    have hx' : logEmbedding E x = -((ZSpan.floor B v : logSpace E)) := hx
    rw [ofMul_toMul, hx', ZSpan.fract_apply, sub_eq_add_neg]
  calc |v w + logEmbedding E (Additive.ofMul (Additive.toMul x)) w|
      = ‖(v + logEmbedding E (Additive.ofMul (Additive.toMul x))) w‖ := by
        rw [Real.norm_eq_abs, Pi.add_apply]
    _ ≤ ‖v + logEmbedding E (Additive.ofMul (Additive.toMul x))‖ := norm_le_pi_norm _ w
    _ = ‖ZSpan.fract B v‖ := by rw [hsum]
    _ ≤ ∑ i, ‖B i‖ := ZSpan.norm_fract_le B v

open scoped Classical in

theorem exists_unit_of_sum_eq_zero (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, ∀ t : InfinitePlace E → ℝ, ∑ w, (mult w : ℝ) * t w = 0 → ∃ u : (𝓞 E)ˣ,
      ∀ w : InfinitePlace E, |t w + Real.log (w (u : E))| ≤ C := by
  obtain ⟨C₁, hC₁, hC⟩ := exists_unit_norm_add_le E
  refine ⟨Fintype.card (InfinitePlace E) * C₁, fun t ht => ?_⟩
  obtain ⟨u, hu⟩ := hC (fun w => (mult w.1 : ℝ) * t w.1)
  refine ⟨u, ?_⟩

  have hoff : ∀ w : {w : InfinitePlace E // w ≠ w₀},
      |(mult w.1 : ℝ) * (t w.1 + Real.log (w.1 (u : E)))| ≤ C₁ := by
    intro w
    have h := hu w
    rw [logEmbedding_component] at h
    rwa [mul_add]

  have hone : ∀ w : InfinitePlace E,
      |t w + Real.log (w (u : E))| ≤ |(mult w : ℝ) * (t w + Real.log (w (u : E)))| := by
    intro w
    rw [abs_mul, abs_of_pos (Nat.cast_pos.2 mult_pos : (0 : ℝ) < mult w)]
    exact le_mul_of_one_le_left (abs_nonneg _) one_le_mult
  have hcard : C₁ ≤ Fintype.card (InfinitePlace E) * C₁ := by
    have h : (1 : ℝ) ≤ Fintype.card (InfinitePlace E) := by exact_mod_cast Fintype.card_pos
    nlinarith
  intro w
  by_cases hw : w = w₀
  ·
    subst hw
    have htot : ∑ w : InfinitePlace E, (mult w : ℝ) * (t w + Real.log (w (u : E))) = 0 := by
      simp only [mul_add, Finset.sum_add_distrib, ht, sum_mult_mul_log, add_zero]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at htot
    calc |t w₀ + Real.log (w₀ (u : E))|
        ≤ |(mult w₀ : ℝ) * (t w₀ + Real.log (w₀ (u : E)))| := hone w₀
      _ = |∑ w : {w : InfinitePlace E // w ≠ w₀}, (mult w.1 : ℝ) * (t w.1 + Real.log (w.1 (u : E)))| := by
        rw [eq_neg_of_add_eq_zero_left htot, abs_neg]
      _ ≤ ∑ w : {w : InfinitePlace E // w ≠ w₀}, |(mult w.1 : ℝ) * (t w.1 + Real.log (w.1 (u : E)))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w : {w : InfinitePlace E // w ≠ w₀}, C₁ := Finset.sum_le_sum fun w _ => hoff w
      _ = Fintype.card {w : InfinitePlace E // w ≠ w₀} * C₁ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Fintype.card (InfinitePlace E) * C₁ := by
        gcongr
        exact_mod_cast Fintype.card_subtype_le _
  · exact (hone w).trans ((hoff ⟨w, hw⟩).trans hcard)

theorem exists_unit_int_abs_le (E : Type) [Field E] [NumberField E] :
    ∃ R : ℝ, ∀ t : InfinitePlace E → ℝ, ∃ (u : (𝓞 E)ˣ) (n : ℤ), ∀ w : InfinitePlace E,
      |t w + Real.log (w (algebraMap (𝓞 E) E (u : 𝓞 E))) + (n : ℝ)| ≤ R := by
  classical
  obtain ⟨C, hC⟩ := exists_unit_of_sum_eq_zero E
  refine ⟨C + 1, fun t => ?_⟩

  have hmpos : 0 < ∑ w : InfinitePlace E, (mult w : ℝ) :=
    Finset.sum_pos (fun w _ => Nat.cast_pos.2 mult_pos) Finset.univ_nonempty
  set s : ℝ := (∑ w : InfinitePlace E, (mult w : ℝ) * t w) / ∑ w : InfinitePlace E, (mult w : ℝ) with hs
  have hms : (∑ w : InfinitePlace E, (mult w : ℝ)) * s = ∑ w : InfinitePlace E, (mult w : ℝ) * t w := by
    rw [hs]
    field_simp
  have hsum : ∑ w : InfinitePlace E, (mult w : ℝ) * (t w - s) = 0 := by
    rw [Finset.sum_congr rfl fun w _ => mul_sub (mult w : ℝ) (t w) s, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hms, sub_self]
  obtain ⟨u, hu⟩ := hC (fun w => t w - s) hsum

  refine ⟨u, -⌊s⌋, fun w => ?_⟩
  have h1 := abs_le.1 (hu w)
  have h2 := Int.fract_nonneg s
  have h3 := Int.fract_lt_one s
  have hcoe : algebraMap (𝓞 E) E (u : 𝓞 E) = (u : E) := rfl
  have heq : t w + Real.log (w (algebraMap (𝓞 E) E (u : 𝓞 E))) + ((-⌊s⌋ : ℤ) : ℝ) =
      (t w - s + Real.log (w (u : E))) + Int.fract s := by
    rw [hcoe, Int.fract]
    push_cast
    ring
  rw [heq, abs_le]
  constructor <;> linarith [h1.1, h1.2]

end GlobalTheory.IntegerUnitBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpIntegralEntireRealPos
section
open MeasureTheory

namespace GlobalTheory

theorem norm_mul_cexp_le_of_abs_le_on_support {s : ℂ} {f t : ℝ} {R : ℝ} (hf : 0 ≤ f) (hR : f ≠ 0 → |t| ≤ R) :
    ‖(f : ℂ) * Complex.exp (s * t)‖ ≤ f * Real.exp (‖s‖ * R) := by
  by_cases h0 : f = 0
  · simp [h0]
  have ht := hR h0
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf]
  apply mul_le_mul_of_nonneg_left _ hf
  apply Real.exp_le_exp.mpr
  have h1 : (s * (t : ℂ)).re = s.re * t := by simp
  rw [h1]
  calc s.re * t ≤ |s.re * t| := le_abs_self _
    _ = |s.re| * |t| := abs_mul _ _
    _ ≤ ‖s‖ * R := mul_le_mul (Complex.abs_re_le_norm s) ht (abs_nonneg _) (norm_nonneg _)

theorem exp_integral_entire_real_pos {X : Type} [MeasurableSpace X] (ν : Measure X) (f t : X → ℝ)
    (hfm : Measurable f) (htm : Measurable t) (hf0 : ∀ y, 0 ≤ f y)
    (hfi : Integrable f ν) (hR : ∃ R : ℝ, ∀ y, f y ≠ 0 → |t y| ≤ R) :
    Differentiable ℂ (fun s : ℂ => ∫ y, (f y : ℂ) * Complex.exp (s * t y) ∂ν) ∧
    ∀ r : ℝ, (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).im = 0 ∧
      (0 < ∫ y, f y ∂ν → 0 < (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).re) := by
  obtain ⟨R, hR⟩ := hR
  have hmeas : ∀ s : ℂ, Measurable fun y => (f y : ℂ) * Complex.exp (s * t y) := by
    intro s; fun_prop
  have hint : ∀ s : ℂ, Integrable (fun y => (f y : ℂ) * Complex.exp (s * t y)) ν := by
    intro s
    refine Integrable.mono' (hfi.mul_const (Real.exp (‖s‖ * R))) (hmeas s).aestronglyMeasurable
      (ae_of_all _ fun y => norm_mul_cexp_le_of_abs_le_on_support (hf0 y) (hR y))
  refine ⟨?_, ?_⟩
  · intro s₀
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := s₀)
      (F := fun s y => (f y : ℂ) * Complex.exp (s * t y))
      (F' := fun s y => (f y : ℂ) * (Complex.exp (s * t y) * t y))
      (bound := fun y => f y * R * Real.exp ((‖s₀‖ + 1) * R))
      (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s => (hmeas s).aestronglyMeasurable) (hint s₀)
      (by fun_prop : Measurable fun y => (f y : ℂ) * (Complex.exp (s₀ * t y) * t y)).aestronglyMeasurable
      (ae_of_all _ fun y s hs => ?_)
      ((hfi.mul_const R).mul_const _)
      (ae_of_all _ fun y s _ => ?_)
    · exact key.2.differentiableAt
    · by_cases h0 : f y = 0
      · simp [h0]
      have ht := hR y h0
      have hR0 : 0 ≤ R := (abs_nonneg _).trans ht
      have hs' : ‖s‖ ≤ ‖s₀‖ + 1 := by
        have := norm_le_norm_add_norm_sub' s s₀
        rw [Metric.mem_ball, dist_eq_norm] at hs
        linarith
      have e1 := norm_mul_cexp_le_of_abs_le_on_support (s := s) (hf0 y) (hR y)
      rw [← mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖(f y : ℂ) * Complex.exp (s * t y)‖ * |t y|
          ≤ (f y * Real.exp (‖s‖ * R)) * R := mul_le_mul e1 ht (abs_nonneg _) (mul_nonneg (hf0 y) (Real.exp_pos _).le)
        _ ≤ f y * R * Real.exp ((‖s₀‖ + 1) * R) := by
          have : Real.exp (‖s‖ * R) ≤ Real.exp ((‖s₀‖ + 1) * R) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs' hR0)
          have := mul_le_mul_of_nonneg_left this (mul_nonneg (hf0 y) hR0)
          nlinarith [this]
    · have := ((hasDerivAt_id s).mul_const (t y : ℂ)).cexp
      simp only [id, one_mul] at this
      exact this.const_mul (f y : ℂ)
  · intro r
    have hre : ∀ y, (f y : ℂ) * Complex.exp (r * t y) = ((f y * Real.exp (r * t y) : ℝ) : ℂ) := by
      intro y; push_cast; ring_nf
    simp_rw [hre]
    rw [integral_complex_ofReal]
    refine ⟨Complex.ofReal_im _, fun hpos => ?_⟩
    rw [Complex.ofReal_re]
    have gint : Integrable (fun y => f y * Real.exp (r * t y)) ν := by
      have := hint (r : ℂ)
      simp_rw [hre] at this
      exact this.re
    have hle : ∀ y, f y * Real.exp (-(|r| * R)) ≤ f y * Real.exp (r * t y) := by
      intro y
      by_cases h0 : f y = 0
      · simp [h0]
      apply mul_le_mul_of_nonneg_left _ (hf0 y)
      apply Real.exp_le_exp.mpr
      have ht := hR y h0
      have : |r * t y| ≤ |r| * R := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
      linarith [neg_abs_le (r * t y)]
    calc 0 < (∫ y, f y ∂ν) * Real.exp (-(|r| * R)) := mul_pos hpos (Real.exp_pos _)
      _ = ∫ y, f y * Real.exp (-(|r| * R)) ∂ν := (integral_mul_const _ _).symm
      _ ≤ ∫ y, f y * Real.exp (r * t y) ∂ν := integral_mono (hfi.mul_const _) gint hle

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgInfSupOfIsCompl
section
open NumberField

namespace GlobalTheory

theorem fg_inf_sup_of_isCompl (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (A : Submodule (𝓞 K) V) (U U' : Submodule K V) :
    A.FG → IsCompl U U' →
      (U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K))).FG := by
  intro hA h
  let p : V →ₗ[K] V := U.subtype ∘ₗ Submodule.linearProjOfIsCompl U U' h
  let q : V →ₗ[𝓞 K] V := p.restrictScalars (𝓞 K)
  have hpU : ∀ x, p x ∈ U := fun x => (Submodule.linearProjOfIsCompl U U' h x).2
  have hpl : ∀ x ∈ U, p x = x := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left h ⟨x, hx⟩)
  have hpr : ∀ x ∈ U', p x = 0 := fun x hx => by
    have := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff h).2 hx
    show ((Submodule.linearProjOfIsCompl U U' h x : U) : V) = 0
    exact congrArg Subtype.val this
  have hsub : ∀ x, x - p x ∈ U' := fun x => by
    rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff h]
    have h1 : p (x - p x) = 0 := by rw [map_sub, hpl _ (hpU x), sub_self]
    have h2 : ((Submodule.linearProjOfIsCompl U U' h (x - p x) : U) : V) = 0 := h1
    exact_mod_cast h2
  have heq : U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K)) = A.map q := by
    ext x
    constructor
    · rintro ⟨hxU, hx⟩
      obtain ⟨a, ha, u, hu, rfl⟩ := Submodule.mem_sup.1 hx
      refine ⟨a, ha, ?_⟩
      change p a = a + u
      have e1 : p (a + u) = a + u := hpl _ hxU
      rw [map_add, hpr u hu, add_zero] at e1
      exact e1
    · rintro ⟨a, ha, rfl⟩
      refine ⟨hpU a, ?_⟩
      refine Submodule.mem_sup.2 ⟨a, ha, p a - a, ?_, by abel⟩
      have := U'.neg_mem (hsub a)
      simpa using this
  rw [heq]
  exact hA.map q

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesModUniformizerPowMatrices
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.GenUnr

theorem finite_classes_mod_pow (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]
    (r t : ℕ) (ϖ : O) (hϖ : Irreducible ϖ) (N : ℕ) :
    ∃ T : Finset (Matrix (Fin r ⊕ Fin t) (Fin r) K),
      ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O),
        algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K) →
        ∃ y ∈ T, ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O,
          x = y + (ϖ ^ N • z').map (algebraMap O K) := by
  classical
  have hfin : Finite (O ⧸ Ideal.span {ϖ ^ (2 * N)}) :=
    IsLocalRing.finite_quotient_iff.mpr
      ⟨2 * N, by rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩
  haveI := Fintype.ofFinite (Matrix (Fin r ⊕ Fin t) (Fin r) (O ⧸ Ideal.span {ϖ ^ (2 * N)}))
  have hϖK : algebraMap O K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hϖ.ne_zero
  let lift : O ⧸ Ideal.span {ϖ ^ (2 * N)} → O := fun c => (Ideal.Quotient.mk_surjective c).choose
  have hlift : ∀ c, Ideal.Quotient.mk _ (lift c) = c := fun c =>
    (Ideal.Quotient.mk_surjective c).choose_spec
  let rep : Matrix (Fin r ⊕ Fin t) (Fin r) (O ⧸ Ideal.span {ϖ ^ (2 * N)}) →
      Matrix (Fin r ⊕ Fin t) (Fin r) K :=
    fun c => (algebraMap O K (ϖ ^ N))⁻¹ • (c.map lift).map (algebraMap O K)
  refine ⟨Finset.univ.image rep, fun x z hxz => ?_⟩
  have hdiff : ∀ i j, ∃ a : O, a * ϖ ^ (2 * N) = z i j - lift (Ideal.Quotient.mk _ (z i j)) :=
    fun i j => Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp (hlift _).symm)
  choose w hw using hdiff
  refine ⟨rep (z.map (Ideal.Quotient.mk _)), Finset.mem_image_of_mem _ (Finset.mem_univ _), Matrix.of w, ?_⟩
  ext i j
  have hx := congrFun (congrFun hxz i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, map_pow] at hx
  have hz : lift (Ideal.Quotient.mk _ (z i j)) = z i j - w i j * ϖ ^ (2 * N) := by
    rw [hw]; ring
  simp only [rep, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hz, map_sub,
    map_mul, map_pow, Matrix.of_apply, ← hx]
  field_simp
  ring

end GlobalTheory.GenUnr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFieldExistsTraceFormDualBasesPowOne
section
namespace GlobalTheory

theorem finiteField_exists_traceForm_dualBases_pow_one :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l],
      ∃ t : k →+ ZMod (l ^ 1), (∀ b, (∀ a, t (a * b) = 0) → b = 0) ∧
        ∃ (n : ℕ) (a e : Fin n → k), ∀ z, z = ∑ j, ((t (a j * z)).val : k) * e j := by
  intro l _ k _ _ _
  rw [pow_one]
  let _ : Algebra (ZMod l) k := ZMod.algebra k l
  have hnd := traceForm_nondegenerate (ZMod l) k
  let b := Module.finBasis (ZMod l) k
  let d := (Algebra.traceForm (ZMod l) k).dualBasis hnd b
  refine ⟨(Algebra.trace (ZMod l) k).toAddMonoidHom, ?_, Module.finrank (ZMod l) k, b, d, ?_⟩
  · intro x hx
    apply hnd.1 x
    intro y
    rw [Algebra.traceForm_apply, mul_comm]
    exact hx y
  · intro z
    conv_lhs => rw [← d.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm z (b j)]
    simp only [LinearMap.toAddMonoidHom_coe]
    obtain ⟨c, hc⟩ : ∃ c, Algebra.trace (ZMod l) k (b j * z) = c := ⟨_, rfl⟩
    rw [hc]
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFreeModuleCompactAdicDvr
section
namespace GlobalTheory

open IsLocalRing

theorem finite_free_compact_adic_dvr
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] (hadic : IsAdic (IsLocalRing.maximalIdeal O))
    {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] [T2Space M] [Module.Free O M] [Module.Finite O M]
    (ϖ : O) (hϖ : Irreducible ϖ) :
    CompactSpace M ∧ IsOpen (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) ∧
      Topology.IsClosedEmbedding (fun m : M => ϖ • m) := by
  classical
  let b := Module.Free.chooseBasis O M
  have hΦ : Continuous (b.equivFun.symm : (Module.Free.ChooseBasisIndex O M → O) → M) := by
    have : (b.equivFun.symm : (Module.Free.ChooseBasisIndex O M → O) → M) =
        fun v => ∑ i, v i • b i := by
      funext v; simp
    rw [this]
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  let H : (Module.Free.ChooseBasisIndex O M → O) ≃ₜ M :=
    hΦ.homeoOfEquivCompactToT2 (f := b.equivFun.symm.toEquiv)
  have hH : ∀ v, H v = b.equivFun.symm v := fun v => rfl
  have hcpt : CompactSpace M := by
    refine ⟨?_⟩
    have := isCompact_univ.image H.continuous
    rwa [Set.image_univ, H.surjective.range_eq] at this
  refine ⟨hcpt, ?_, ?_⟩
  · have hm : IsOpen ((IsLocalRing.maximalIdeal O : Ideal O) : Set O) := by
      have := (isAdic_iff.mp hadic).1 1
      simpa using this
    let S : Set (Module.Free.ChooseBasisIndex O M → O) :=
      ⋂ i, (fun v => v i) ⁻¹' ((IsLocalRing.maximalIdeal O : Ideal O) : Set O)
    have hS : IsOpen S := isOpen_iInter_of_finite fun i => hm.preimage (continuous_apply i)
    have heq : (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) = H '' S := by
      ext m
      simp only [SetLike.mem_coe, LinearMap.mem_range, LinearMap.lsmul_apply, S,
        Set.mem_image, Set.mem_iInter, Set.mem_preimage, hϖ.maximalIdeal_eq,
        Ideal.mem_span_singleton', hH]
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨b.equivFun (ϖ • x), fun i => ⟨b.equivFun x i, ?_⟩, by simp⟩
        simp [mul_comm]
      · rintro ⟨v, hv, rfl⟩
        choose c hc using hv
        refine ⟨b.equivFun.symm c, ?_⟩
        rw [← LinearEquiv.map_smul]
        congr 1
        funext i
        simp [← hc i, mul_comm]
    rw [heq]
    exact H.isOpenMap S hS
  · refine (continuous_const_smul ϖ).isClosedEmbedding ?_
    exact smul_right_injective M hϖ.ne_zero

end GlobalTheory
end

