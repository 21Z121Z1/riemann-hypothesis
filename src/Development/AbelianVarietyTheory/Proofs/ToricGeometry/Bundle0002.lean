import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.EntirePeriodicEqZeroOfFourierCoeffEqZero
section
open Complex Matrix Filter Topology
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory

theorem apply_add_intCast_of_periodic_single {g : ℕ} {β : Type*} {A : (Fin g → ℝ) → β}
    (hA : ∀ (i : Fin g) x, A (x + Pi.single i 1) = A x) (n : Fin g → ℤ) (x : Fin g → ℝ) :
    A (x + fun i => (n i : ℝ)) = A x := by
  have h1 : (fun i => (n i : ℝ)) = ∑ i, n i • (Pi.single i 1 : Fin g → ℝ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h1]
  have h2 : ∀ s : Finset (Fin g),
      Function.Periodic A (∑ i ∈ s, n i • (Pi.single i 1 : Fin g → ℝ)) := fun s => by
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (Function.Periodic.zsmul (hA a) (n a)).add_period ih
  exact h2 _ x

theorem eq_zero_of_cube_fourierCoeff_eq_zero {g : ℕ} {A : (Fin g → ℝ) → ℂ} (hc : Continuous A)
    (hA : ∀ (i : Fin g) x, A (x + Pi.single i 1) = A x)
    (h : ∀ m : Fin g → ℤ, (∫ x in Set.Icc (0 : Fin g → ℝ) 1,
      A x * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = 0) (y : Fin g → ℝ) :
    A y = 0 := by
  set p : (Fin g → ℝ) → UnitAddTorus (Fin g) := fun x i ↦ (x i : UnitAddCircle) with hp
  have hq : IsOpenQuotientMap p :=
    IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk
  set f₀ : UnitAddTorus (Fin g) → ℂ := fun z ↦ A (Function.surjInv hq.surjective z) with hf₀
  have hfp : ∀ x, f₀ (p x) = A x := fun x ↦ by
    set x' := Function.surjInv hq.surjective (p x)
    have h1 : p x' = p x := Function.surjInv_eq _ _
    have h2 : ∀ i, ∃ n : ℤ, (n : ℝ) = x' i - x i := fun i ↦ by
      have h3 : ((x' i - x i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, sub_eq_zero]; exact congrFun h1 i
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h3
      exact ⟨n, by simpa using hn⟩
    choose n hn using h2
    rw [← apply_add_intCast_of_periodic_single hA n x]
    change A x' = _
    congr 1
    funext i
    simp [hn]
  let f : C(UnitAddTorus (Fin g), ℂ) := ⟨f₀,
    hq.isQuotientMap.continuous_iff.2 <| by
      rw [show f₀ ∘ p = A from funext hfp]; exact hc⟩
  have hchar : ∀ n x, UnitAddTorus.mFourier (-n) (p x) =
      cexp (-(2 * Real.pi * I) * ∑ i, (n i : ℂ) * (x i : ℂ)) := fun n x ↦ by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, hp, fourier_coe_apply,
      ← Complex.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Pi.neg_apply]
    push_cast
    ring
  have hcoeff : ∀ n, UnitAddTorus.mFourierCoeff f n = 0 := fun n ↦ by
    rw [UnitAddTorus.mFourierCoeff_eq_integral f n 0, ← h n]
    simp only [Pi.zero_apply, zero_add]
    have h2 : {x : Fin g → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1} =
        Set.pi Set.univ fun i ↦ Set.Ioc ((0 : Fin g → ℝ) i) ((1 : Fin g → ℝ) i) := by
      ext x; simp
    rw [h2, MeasureTheory.setIntegral_congr_set
      (μ := MeasureTheory.volume) MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc]
    refine MeasureTheory.integral_congr_ae (.of_forall fun x ↦ ?_)
    change UnitAddTorus.mFourier (-n) (p x) • f₀ (p x) = _
    simp only [hchar, hfp, smul_eq_mul, mul_comm]
  have hsum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := f)
    (by rw [funext hcoeff]; exact summable_zero) (p y)
  change HasSum _ (f₀ (p _)) at hsum
  simp only [hcoeff, zero_smul, hfp] at hsum
  exact hsum.unique hasSum_zero

theorem entire_periodic_eq_zero_of_fourierCoeff_eq_zero :
    (∀ (g : ℕ) (f : (Fin g → ℂ) → ℂ), Differentiable ℂ f → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → ∀ (m : Fin g → ℤ) (w : Fin g → ℂ), (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f ((fun i => (x i : ℂ)) + w) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = cexp (2 * Real.pi * I * ∑ i, (m i : ℂ) * w i) * (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ)))) → (∀ (g : ℕ) (f : (Fin g → ℂ) → ℂ), Differentiable ℂ f → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ m : Fin g → ℤ, (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = 0) → f = 0) := by
  intro H g f hf hper h0
  funext w
  have hc := hf.continuous
  have := eq_zero_of_cube_fourierCoeff_eq_zero (A := fun x => f ((fun i => (x i : ℂ)) + w))
    (by fun_prop) (fun i x => by
      rw [← hper i ((fun i => (x i : ℂ)) + w)]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp; ring
      · simp [hj])
    (fun m => by rw [H g f hf hper m w, h0 m, mul_zero]) 0
  have h1 : (fun i => (((0 : Fin g → ℝ) i : ℝ) : ℂ)) + w = w := by
    funext j; simp
  rw [h1] at this
  exact this

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.EventuallyEqZeroOfIsBigOCubeOfDoubling
section
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

private lemma eq_zero_of_cube_bound_of_doubling {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (F : E → ℂ) (ε C : ℝ)
    (hP : ∀ w : E, ‖w‖ < ε → ‖F w‖ ≤ C * ‖w‖ ^ 3 ∧ F ((2 : ℂ) • w) = 3 * F w + F (-w))
    (z : E) (hz : ‖z‖ < ε) : F z = 0 := by

  set M : E → ℝ := fun w => ‖F w‖ + ‖F (-w)‖ with hM
  have step : ∀ w : E, ‖w‖ < ε → M ((2 : ℂ) • w) ≤ 4 * M w := by
    intro w hw
    have h1 := (hP w hw).2
    have h2 := (hP (-w) (by rwa [norm_neg])).2
    rw [neg_neg] at h2
    simp only [hM]
    rw [← smul_neg, h1, h2]
    have e1 : ‖3 * F w + F (-w)‖ ≤ 3 * ‖F w‖ + ‖F (-w)‖ :=
      (norm_add_le _ _).trans (by simp)
    have e2 : ‖3 * F (-w) + F w‖ ≤ 3 * ‖F (-w)‖ + ‖F w‖ :=
      (norm_add_le _ _).trans (by simp)
    linarith
  set w : ℕ → E := fun n => ((2 : ℂ)⁻¹) ^ n • z with hw
  have hnorm : ∀ n, ‖w n‖ = ((2 : ℝ) ^ n)⁻¹ * ‖z‖ := by
    intro n
    simp [hw, norm_smul]
  have hsmall : ∀ n, ‖w n‖ < ε := by
    intro n
    rw [hnorm]
    have h1 : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    calc ((2 : ℝ) ^ n)⁻¹ * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
      _ < ε := by simpa using hz
  have hsucc : ∀ n, w n = (2 : ℂ) • w (n + 1) := by
    intro n
    simp only [hw, smul_smul]
    congr 1
    rw [pow_succ]
    field_simp
  have hiter : ∀ n : ℕ, M z ≤ 4 ^ n * M (w n) := by
    intro n
    induction n with
    | zero => simp [hw]
    | succ n ih =>
      calc M z ≤ 4 ^ n * M (w n) := ih
        _ = 4 ^ n * M ((2 : ℂ) • w (n + 1)) := by rw [← hsucc]
        _ ≤ 4 ^ n * (4 * M (w (n + 1))) := by
          gcongr
          exact step _ (hsmall _)
        _ = 4 ^ (n + 1) * M (w (n + 1)) := by ring
  have hbound : ∀ n : ℕ, M z ≤ (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n := by
    intro n
    have hb : M (w n) ≤ 2 * C * ‖w n‖ ^ 3 := by
      have a1 := (hP (w n) (hsmall n)).1
      have a2 := (hP (-w n) (by rw [norm_neg]; exact hsmall n)).1
      rw [norm_neg] at a2
      simp only [hM]
      linarith
    have h4 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    calc M z ≤ 4 ^ n * M (w n) := hiter n
      _ ≤ 4 ^ n * (2 * C * ‖w n‖ ^ 3) := by gcongr
      _ = (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n := by
        have h2 : ((1 : ℝ) / 2) ^ n * 2 ^ n = 1 := by
          rw [← mul_pow]
          norm_num
        rw [hnorm, h4]
        field_simp
        linear_combination (-(C * ‖z‖ ^ 3)) * h2
  have hlim : Filter.Tendsto (fun n : ℕ => (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n)
      Filter.atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (2 * C * ‖z‖ ^ 3)
    simpa using this
  have hM0 : M z ≤ 0 := ge_of_tendsto' hlim hbound
  have : ‖F z‖ ≤ 0 := by
    have := norm_nonneg (F (-z))
    simp only [hM] at hM0
    linarith
  exact norm_le_zero_iff.1 this

theorem eventually_eq_zero_of_isBigO_cube_of_doubling :
    (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : E → ℂ),
      F =O[𝓝 0] (fun z => ‖z‖ ^ 3) →
      (∀ᶠ z in 𝓝 0, F ((2 : ℂ) • z) = 3 * F z + F (-z)) → ∀ᶠ z in 𝓝 0, F z = 0) := by
  intro E _ _ F hO hrel
  obtain ⟨C, hC⟩ := hO.bound
  have hev : ∀ᶠ z in 𝓝 (0 : E), ‖F z‖ ≤ C * ‖z‖ ^ 3 ∧ F ((2 : ℂ) • z) = 3 * F z + F (-z) := by
    filter_upwards [hC, hrel] with z h1 h2
    exact ⟨by simpa using h1, h2⟩
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 hev
  filter_upwards [Metric.ball_mem_nhds (0 : E) hε] with z hz
  exact eq_zero_of_cube_bound_of_doubling F ε C (fun w hw => hP (by simpa using hw)) z
    (by simpa using hz)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.Imports
section
universe u_1 u_2

namespace GlobalTheory.CommonDenominatorForFinset

theorem exists_common_denominator {R : Type u_1} {A : Type u_2} [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Module.Finite R A] (a : A)
    (h : ∀ b : A, ∃ s : R, s ≠ 0 ∧ ∃ r : Polynomial R,
      algebraMap R A s * b = Polynomial.aeval a r) :
    ∃ s : R, s ≠ 0 ∧ ∀ b : A, ∃ r : Polynomial R,
      algebraMap R A s * b = Polynomial.aeval a r := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R) (M := A)
  choose f hf0 r hr using h
  refine ⟨∏ b ∈ S, f b, Finset.prod_ne_zero_iff.mpr fun b _ => hf0 b, ?_⟩

  let N : Submodule R A :=
    { carrier := {b | ∃ p : Polynomial R, algebraMap R A (∏ b ∈ S, f b) * b = Polynomial.aeval a p}
      add_mem' := by
        rintro x y ⟨p, hp⟩ ⟨q, hq⟩
        exact ⟨p + q, by rw [mul_add, hp, hq, map_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨p, hp⟩
        refine ⟨Polynomial.C c * p, ?_⟩
        rw [map_mul, Polynomial.aeval_C, ← hp, Algebra.smul_def]
        ring }

  have hgen : (S : Set A) ⊆ N := by
    intro b hb
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem f hb
    refine ⟨Polynomial.C t * r b, ?_⟩
    rw [map_mul, Polynomial.aeval_C, ← hr b, ht, map_mul]
    ring
  have htop : (⊤ : Submodule R A) ≤ N := by
    rw [← hS, Submodule.span_le]
    exact hgen
  intro b
  exact htop Submodule.mem_top

end GlobalTheory.CommonDenominatorForFinset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.NegOneZpowFormApplySemicharacter
section
open Matrix Polynomial
open scoped BigOperators

namespace GlobalTheory

theorem neg_one_zpow_form_apply_semicharacter :
    (∀ (X : Type) [AddCommGroup X] (E : LinearMap.BilinForm ℤ X) (w w' : X →ₗ[ℤ] X), (∀ x, E x x = 0) → w + w' = LinearMap.id → (∀ x y, E (w x) y = E x (w' y)) → ∀ x y, (-1 : ℂ) ^ E (x + y) (w (x + y)) = (-1) ^ E x (w x) * (-1) ^ E y (w y) * (-1) ^ E x y) := by
  intro X _ E w w' halt hsum hadj x y
  have hskew : ∀ a b, E a b = - E b a := by
    intro a b
    have h := halt (a + b)
    simp only [map_add, LinearMap.add_apply, halt] at h
    linarith
  have hy : w y + w' y = y := by
    have := LinearMap.congr_fun hsum y
    simpa using this
  have h1 : E x (w y) + E x (w' y) = E x y := by rw [← map_add, hy]
  have h2 : E y (w x) = - E x (w' y) := by rw [hskew, hadj]
  have h3 : E (x + y) (w (x + y))
      = E x (w x) + E y (w y) + E x y + 2 * (E x (w y) - E x y) := by
    simp only [map_add, LinearMap.add_apply]
    linarith
  have hne : (-1 : ℂ) ≠ 0 := by norm_num
  rw [h3, zpow_add₀ hne, zpow_add₀ hne, zpow_add₀ hne, _root_.zpow_mul]
  have h4 : (-1 : ℂ) ^ (2 : ℤ) = 1 := by norm_num
  rw [h4, _root_.one_zpow, mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.NodupRootsOfDerivativeNeZero
section
open Filter Topology Polynomial

namespace GlobalTheory.SimpleRoots

variable {d : ℕ}

theorem eval_map_eq_sum (p : Polynomial (MvPolynomial (Fin d) ℂ)) (x : Fin d → ℂ) (y : ℂ) :
    (p.map (MvPolynomial.eval x)).eval y
      = ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval x (p.coeff i) * y ^ i := by
  rw [eval_map, eval₂_eq_sum_range]

theorem analyticAt_mvPolynomial_eval (a : MvPolynomial (Fin d) ℂ) (x : Fin d → ℂ) :
    AnalyticAt ℂ (fun x : Fin d → ℂ => MvPolynomial.eval x a) x :=
  AnalyticOnNhd.eval_mvPolynomial a x (Set.mem_univ x)

theorem analyticAt_eval_map (p : Polynomial (MvPolynomial (Fin d) ℂ)) (z : (Fin d → ℂ) × ℂ) :
    AnalyticAt ℂ (fun w : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval w.1)).eval w.2) z := by
  simp only [eval_map_eq_sum]
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact ((analyticAt_mvPolynomial_eval _ _).comp analyticAt_fst).mul (analyticAt_snd.pow i)

theorem exists_analytic_root (p : Polynomial (MvPolynomial (Fin d) ℂ)) {x₀ : Fin d → ℂ} {y₀ : ℂ}
    (h0 : (p.map (MvPolynomial.eval x₀)).eval y₀ = 0)
    (h1 : (p.map (MvPolynomial.eval x₀)).derivative.eval y₀ ≠ 0) :
    ∃ ψ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ ψ x₀ ∧ ψ x₀ = y₀ ∧
      (∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (ψ x) = 0) ∧
      ∀ᶠ w in 𝓝 (x₀, y₀), (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 ↔ ψ w.1 = w.2 := by
  set f : (Fin d → ℂ) × ℂ → ℂ := fun w => (p.map (MvPolynomial.eval w.1)).eval w.2 with hf
  have ha : AnalyticAt ℂ f (x₀, y₀) := analyticAt_eval_map p _
  have hc : ContDiffAt ℂ ⊤ f (x₀, y₀) := ha.contDiffAt
  have hd : HasFDerivAt (fun y : ℂ => f (x₀, y))
      (fderiv ℂ f (x₀, y₀) ∘L .inr ℂ (Fin d → ℂ) ℂ) y₀ :=
    ha.differentiableAt.hasFDerivAt.comp y₀ (hasFDerivAt_prodMk_right x₀ y₀)
  have hd' := ((p.map (MvPolynomial.eval x₀)).hasDerivAt y₀).hasFDerivAt
  have he := hd.unique hd'
  have hi : (fderiv ℂ f (x₀, y₀) ∘L .inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [he]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩
    ext
    simp
  refine ⟨hc.implicitFunction (by simp) hi, ?_, hc.implicitFunction_apply_self (by simp) hi, ?_, ?_⟩
  · exact (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt
  · filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with x hx
    exact hx.trans h0
  · filter_upwards [hc.eventually_apply_eq_iff_implicitFunction (by simp) hi] with w hw
    rw [← hw]
    exact Iff.of_eq (congrArg _ h0.symm)

theorem nodup_roots_of_derivative_ne_zero {P : ℂ[X]} (hP : P ≠ 0)
    (h : ∀ y, P.eval y = 0 → P.derivative.eval y ≠ 0) : P.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro y
  rw [count_roots]
  by_contra hy
  obtain ⟨h1, h2⟩ := (one_lt_rootMultiplicity_iff_isRoot hP).mp (not_le.mp hy)
  exact h y h1 h2

theorem exists_analytic_roots {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    {x₀ : Fin d → ℂ}
    (h : ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 →
      (p.map (MvPolynomial.eval x₀)).derivative.eval y ≠ 0) :
    ∃ ψ : ℂ → (Fin d → ℂ) → ℂ,
      (∀ y ∈ (p.map (MvPolynomial.eval x₀)).roots, AnalyticAt ℂ (ψ y) x₀ ∧ ψ y x₀ = y) ∧
      ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).roots
        = (p.map (MvPolynomial.eval x₀)).roots.map fun y => ψ y x := by
  classical
  have hne : ∀ x, p.map (MvPolynomial.eval x) ≠ 0 := fun x => (hp.map _).ne_zero
  have hex : ∀ y, ∃ ψ : (Fin d → ℂ) → ℂ, y ∈ (p.map (MvPolynomial.eval x₀)).roots →
      AnalyticAt ℂ ψ x₀ ∧ ψ x₀ = y ∧
        ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (ψ x) = 0 := by
    intro y
    by_cases hy : y ∈ (p.map (MvPolynomial.eval x₀)).roots
    · have hy' := (mem_roots (hne x₀)).mp hy
      obtain ⟨ψ, h1, h2, h3, -⟩ := exists_analytic_root p hy' (h y hy')
      exact ⟨ψ, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun hy' => absurd hy' hy⟩
  choose ψ hψ using hex
  refine ⟨ψ, fun y hy => ⟨(hψ y hy).1, (hψ y hy).2.1⟩, ?_⟩
  set S := (p.map (MvPolynomial.eval x₀)).roots with hS
  have hnd : S.Nodup := nodup_roots_of_derivative_ne_zero (hne x₀) h
  have hcard : ∀ x, (p.map (MvPolynomial.eval x)).roots.card = p.natDegree := fun x => by
    rw [← hp.natDegree_map (MvPolynomial.eval x)]
    exact (IsAlgClosed.splits _).natDegree_eq_card_roots.symm
  have e1 : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ S.toFinset, (p.map (MvPolynomial.eval x)).eval (ψ y x) = 0 :=
    (Finset.eventually_all _).mpr fun y hy => (hψ y (Multiset.mem_toFinset.mp hy)).2.2
  have e2 : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ S.toFinset, ∀ y' ∈ S.toFinset, y ≠ y' → ψ y x ≠ ψ y' x := by
    refine (Finset.eventually_all _).mpr fun y hy => (Finset.eventually_all _).mpr fun y' hy' => ?_
    by_cases hyy : y = y'
    · exact Eventually.of_forall fun _ hn => absurd hyy hn
    · obtain ⟨a1, a2, -⟩ := hψ y (Multiset.mem_toFinset.mp hy)
      obtain ⟨b1, b2, -⟩ := hψ y' (Multiset.mem_toFinset.mp hy')
      have := (a1.continuousAt.ne_iff_eventually_ne b1.continuousAt).mp (by rwa [a2, b2])
      exact this.mono fun x hx _ => hx
  filter_upwards [e1, e2] with x h1 h2
  symm
  refine Multiset.eq_of_le_of_card_le ?_ ?_
  · refine (Multiset.le_iff_subset (hnd.map_on fun y hy y' hy' hyy => ?_)).mpr fun t ht => ?_
    · by_contra hn
      exact h2 y (Multiset.mem_toFinset.mpr hy) y' (Multiset.mem_toFinset.mpr hy') hn hyy
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp ht
      exact (mem_roots (hne x)).mpr (h1 y (Multiset.mem_toFinset.mpr hy))
  · rw [Multiset.card_map, hcard, hS, hcard]

theorem differentiableAt_coeff_prod {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : Multiset ι) (ψ : ι → E → ℂ) {x₀ : E} (h : ∀ y ∈ T, DifferentiableAt ℂ (ψ y) x₀) (k : ℕ) :
    DifferentiableAt ℂ (fun x => (T.map fun y => X - C (ψ y x)).prod.coeff k) x₀ := by
  induction T using Multiset.induction_on generalizing k with
  | empty => simp
  | cons a T ih =>
    have ha := h a (Multiset.mem_cons_self a T)
    have ih' := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    simp only [Multiset.map_cons, Multiset.prod_cons, sub_mul, coeff_sub, coeff_C_mul]
    refine DifferentiableAt.sub ?_ (ha.mul (ih' k))
    cases k with
    | zero => simp
    | succ k => simpa only [coeff_X_mul] using ih' k

theorem norm_coeff_prod_le (T : Multiset ℂ) {R : ℝ} (hR : 0 ≤ R) (h : ∀ y ∈ T, ‖y‖ ≤ R) (k : ℕ) :
    ‖(T.map fun y => X - C y).prod.coeff k‖ ≤ (1 + R) ^ T.card := by
  induction T using Multiset.induction_on generalizing k with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, coeff_one, Multiset.card_zero, pow_zero]
    split_ifs <;> simp
  | cons a T ih =>
    have ha := h a (Multiset.mem_cons_self a T)
    have ih' := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    simp only [Multiset.map_cons, Multiset.prod_cons, sub_mul, coeff_sub, coeff_C_mul,
      Multiset.card_cons]
    have h1 : ‖(X * (T.map fun y => X - C y).prod).coeff k‖ ≤ (1 + R) ^ T.card := by
      cases k with
      | zero => simp; positivity
      | succ k => simpa only [coeff_X_mul] using ih' k
    have h2 : ‖a * (T.map fun y => X - C y).prod.coeff k‖ ≤ R * (1 + R) ^ T.card := by
      rw [norm_mul]
      exact mul_le_mul ha (ih' k) (norm_nonneg _) hR
    refine (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq ?_)
    ring

theorem exists_norm_eval_le (a : MvPolynomial (Fin d) ℂ) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ x : Fin d → ℂ, ‖MvPolynomial.eval x a‖ ≤ C * (1 + ‖x‖) ^ m := by
  induction a using MvPolynomial.induction_on with
  | C c => exact ⟨‖c‖, 0, norm_nonneg _, fun x => by simp⟩
  | add a b ha hb =>
    obtain ⟨C₁, m₁, h₁, ha⟩ := ha
    obtain ⟨C₂, m₂, h₂, hb⟩ := hb
    refine ⟨C₁ + C₂, m₁ + m₂, by positivity, fun x => ?_⟩
    have h1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    rw [map_add, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((ha x).trans ?_) ((hb x).trans ?_))
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) h₁
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) h₂
  | mul_X a i ha =>
    obtain ⟨C₁, m₁, h₁, ha⟩ := ha
    refine ⟨C₁, m₁ + 1, h₁, fun x => ?_⟩
    rw [map_mul, MvPolynomial.eval_X, norm_mul, pow_succ, ← mul_assoc]
    refine mul_le_mul (ha x) ?_ (norm_nonneg _) (by positivity)
    linarith [norm_le_pi_norm x i]

theorem norm_root_le {P : ℂ[X]} (hP : P.Monic) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i < P.natDegree, ‖P.coeff i‖ ≤ M) {y : ℂ} (hy : P.eval y = 0) : ‖y‖ ≤ M + 1 := by
  have h1 := IsRoot.norm_lt_cauchyBound hP.ne_zero hy
  lift M to NNReal using hM0
  have h2 : P.cauchyBound ≤ M + 1 := by
    unfold cauchyBound
    rw [hP.leadingCoeff, nnnorm_one, div_one]
    gcongr
    exact Finset.sup_le fun i hi => by exact_mod_cast hM i (Finset.mem_range.mp hi)
  exact_mod_cast (h1.trans_le h2).le

theorem exists_norm_root_le {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ (x : Fin d → ℂ) (y : ℂ),
      (p.map (MvPolynomial.eval x)).eval y = 0 → ‖y‖ ≤ C * (1 + ‖x‖) ^ m := by
  choose C m hC h using fun i => exists_norm_eval_le (p.coeff i)
  set s := Finset.range p.natDegree
  have hs : 0 ≤ ∑ i ∈ s, C i := Finset.sum_nonneg fun i _ => hC i
  refine ⟨∑ i ∈ s, C i + 1, ∑ i ∈ s, m i, by positivity, fun x y hy => ?_⟩
  have h1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have h2 := norm_root_le (hp.map _) (M := (∑ i ∈ s, C i) * (1 + ‖x‖) ^ (∑ i ∈ s, m i))
    (by positivity) (fun i hi => ?_) hy
  · rw [add_mul, one_mul]
    linarith [one_le_pow₀ h1 (n := ∑ i ∈ s, m i)]
  · rw [hp.natDegree_map] at hi
    have hi' : i ∈ s := Finset.mem_range.mpr hi
    rw [coeff_map]
    refine (h i x).trans (mul_le_mul (Finset.single_le_sum (fun j _ => hC j) hi')
      (pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le _) hi'))
      (by positivity) hs)

end GlobalTheory.SimpleRoots
end

