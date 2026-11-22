import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Matrix

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.BasicExpBound
section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem basic_exp_bound (x : ℝ) (hx : 1 ≤ x) :
    (x + 1) ^ 2 + (x + Real.log x) ≤ 2 * Real.exp x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have h4 := Real.sum_le_exp_of_nonneg hx0 4
  simp [Finset.sum_range_succ, Nat.factorial] at h4
  have hl := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < x)
  nlinarith [sq_nonneg (x - 7 / 5), mul_nonneg hx0 (sq_nonneg (x - 7 / 5)),
    mul_nonneg (by linarith : (0:ℝ) ≤ x - 1) (sq_nonneg (x - 7 / 5))]

theorem basic_exp_seven : Real.exp 7 ≤ 1250 := by
  have h := Real.exp_one_lt_d9
  have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have : Real.exp 7 = Real.exp 1 ^ 7 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 7 ≤ (2.7182818286 : ℝ) ^ 7 := by gcongr
    _ ≤ 1250 := by norm_num

theorem basic_real (A ε : ℝ) (hε : 0 < ε) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) :
    let X := 1 + Real.log (1 + ε ^ 2) - Real.log (A + ε ^ 2)
    1 ≤ X ∧ 1 ≤ X + Real.log X ∧ 1 + 1 / X ≤ 2 ∧ X + Real.log X ≤ (X + 1) ^ 2 ∧
      X ≤ 1 + Real.log (1 + ε ^ 2) - Real.log (ε ^ 2) ∧
      A + ε ^ 2 = (1 + ε ^ 2) * Real.exp (1 - X) := by
  intro X
  have he2 : 0 < ε ^ 2 := by positivity
  have hQ : 0 < A + ε ^ 2 := by linarith
  have hlog : Real.log (A + ε ^ 2) ≤ Real.log (1 + ε ^ 2) :=
    Real.log_le_log hQ (by linarith)
  have hX : 1 ≤ X := by simp only [X]; linarith
  have hX0 : 0 < X := by linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlX' := Real.log_le_sub_one_of_pos hX0
  refine ⟨hX, by linarith, ?_, by nlinarith, ?_, ?_⟩
  · have : 1 / X ≤ 1 := by rw [div_le_one hX0]; exact hX
    linarith
  · have : Real.log (ε ^ 2) ≤ Real.log (A + ε ^ 2) := Real.log_le_log he2 (by linarith)
    simp only [X]; linarith
  · have h1 : (1 : ℝ) - X = Real.log (A + ε ^ 2) - Real.log (1 + ε ^ 2) := by simp only [X]; ring
    rw [h1, Real.exp_sub, Real.exp_log hQ, Real.exp_log (by positivity)]
    field_simp

theorem basic (n : ℕ) (M : Type u) : BasicStatement n M := by
  intro g ph ph2 r j ε δ hr hε hA
  have hev : ∀ x, 0 ≤ ev n g ph r x ∧ ev n g ph r x ≤ 1 := by
    intro x
    have hr2 : 0 < r ^ 2 := by positivity
    refine ⟨by unfold ev; positivity, ?_⟩
    unfold ev
    rw [div_le_one hr2]; exact hA x
  have hR : ∀ x, _ := fun x => basic_real (ev n g ph r x) ε hε (hev x).1 (hev x).2
  have hxx : ∀ x, xx n g ph r ε x =
      1 + Real.log (1 + ε ^ 2) - Real.log (ev n g ph r x + ε ^ 2) := fun x => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨h1, h2, h3, h4, -⟩ := hR x
    simp only [eta, kap, hxx]
    exact ⟨h1, h2, h3, h4⟩
  · refine ⟨Real.log (1 + Real.log (1 + ε ^ 2) - Real.log (ε ^ 2) +
      Real.log (1 + Real.log (1 + ε ^ 2) - Real.log (ε ^ 2))), fun x => ?_⟩
    obtain ⟨h1, h2, -, -, h5, -⟩ := hR x
    simp only [twist, eta, hxx]
    set X := 1 + Real.log (1 + ε ^ 2) - Real.log (ev n g ph r x + ε ^ 2)
    set B := 1 + Real.log (1 + ε ^ 2) - Real.log (ε ^ 2)
    have hl0 : 0 ≤ Real.log (X + Real.log X) := Real.log_nonneg h2
    have hlB : Real.log X ≤ Real.log B := Real.log_le_log (by linarith) h5
    have : Real.log (X + Real.log X) ≤ Real.log (B + Real.log B) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [abs_neg, abs_of_nonneg hl0]; exact this
  · intro h50 x hx
    obtain ⟨h1, h2, -, -, -, -⟩ := hR x
    simp only [eta, hxx]
    set X := 1 + Real.log (1 + ε ^ 2) - Real.log (ev n g ph r x + ε ^ 2)
    have hlX : 0 ≤ Real.log X := Real.log_nonneg h1
    have he2 : 0 < ε ^ 2 := by positivity
    have hQ : ev n g ph r x + ε ^ 2 ≤ 2 * ε ^ 2 := by linarith
    have hQ0 : 0 < ev n g ph r x + ε ^ 2 := by linarith [(hev x).1]
    have hsm : 2 * ε ^ 2 ≤ Real.exp (-7) := by
      have hε2 : ε ^ 2 ≤ (1 / 50) ^ 2 := by gcongr
      have : (1 : ℝ) / 1250 ≤ Real.exp (-7) := by
        rw [Real.exp_neg, one_div]; exact inv_anti₀ (Real.exp_pos 7) basic_exp_seven
      nlinarith
    have hlQ : Real.log (ev n g ph r x + ε ^ 2) ≤ -7 := by
      rw [Real.log_le_iff_le_exp hQ0]; linarith
    have hl1 : 0 ≤ Real.log (1 + ε ^ 2) := Real.log_nonneg (by linarith)
    simp only [X] at hlX ⊢
    linarith
  · intro hn hδ hδε x
    obtain ⟨h1, -, -, -, -, h6⟩ := hR x
    have hD := basic_exp_bound _ h1
    simp only [eta, hxx, wgt, lw] at hD ⊢
    set X := 1 + Real.log (1 + ε ^ 2) - Real.log (ev n g ph r x + ε ^ 2)
    set A := ev n g ph r x
    set E := Real.exp (-ph2 x - ((n : ℝ) + j) * ph x)
    set D := (X + 1) ^ 2 + (X + Real.log X)
    have hA0 : 0 ≤ A := (hev x).1
    have hAδ : 0 < A + δ ^ 2 := by positivity
    have hD0 : 0 < D := by
      have : 0 ≤ Real.log X := Real.log_nonneg h1
      positivity
    have hE : 0 < E := Real.exp_pos _
    have hexp : Real.exp (-(ph2 x + ((n : ℝ) + j) * ph x + n * Real.log (A + δ ^ 2))) =
        E / (A + δ ^ 2) ^ n := by
      rw [show -(ph2 x + ((n : ℝ) + j) * ph x + n * Real.log (A + δ ^ 2)) =
        (-ph2 x - ((n : ℝ) + j) * ph x) - n * Real.log (A + δ ^ 2) by ring, Real.exp_sub,
        ← Real.log_pow, Real.exp_log (by positivity)]
    rw [hexp]

    have hpow : (A + δ ^ 2) ^ n ≤ (1 + ε ^ 2) ^ n * Real.exp (1 - X) := by
      have hle : A + δ ^ 2 ≤ (1 + ε ^ 2) * Real.exp (1 - X) := by
        rw [← h6]; have : δ ^ 2 ≤ ε ^ 2 := by gcongr
        linarith
      calc (A + δ ^ 2) ^ n ≤ ((1 + ε ^ 2) * Real.exp (1 - X)) ^ n := by gcongr
        _ = (1 + ε ^ 2) ^ n * Real.exp (1 - X) ^ n := by rw [mul_pow]
        _ ≤ (1 + ε ^ 2) ^ n * Real.exp (1 - X) := by
          gcongr
          exact pow_le_of_le_one (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
            (by omega)
    have hkey : (A + δ ^ 2) ^ n * D ≤ 2 * Real.exp 1 * (1 + ε ^ 2) ^ n := by
      have h2 : Real.exp (1 - X) * D ≤ 2 * Real.exp 1 := by
        rw [Real.exp_sub]
        rw [div_mul_eq_mul_div, div_le_iff₀ (Real.exp_pos X)]
        nlinarith [Real.exp_pos 1]
      calc (A + δ ^ 2) ^ n * D ≤ (1 + ε ^ 2) ^ n * Real.exp (1 - X) * D := by gcongr
        _ = (1 + ε ^ 2) ^ n * (Real.exp (1 - X) * D) := by ring
        _ ≤ (1 + ε ^ 2) ^ n * (2 * Real.exp 1) := by gcongr
        _ = 2 * Real.exp 1 * (1 + ε ^ 2) ^ n := by ring
    rw [div_div, mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hkey hE.le]

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.CovDet
section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem covDet (n : ℕ) (f' : V n →L[ℂ] V n) :
    |(f'.restrictScalars ℝ : V n →L[ℝ] V n).det| =
      ‖LinearMap.det (f' : V n →ₗ[ℂ] V n)‖ ^ 2 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, LinearMap.det_restrictScalars,
    Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity)]

theorem cov (n : ℕ) : CovStatement n := by
  intro W G f hW hG hinj _
  have hd : ∀ y ∈ W, HasFDerivWithinAt G ((fderiv ℂ G y).restrictScalars ℝ) W y := fun y hy =>
    (((hG y hy).differentiableAt (hW.mem_nhds hy)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hW.measurableSet hd hinj f]
  simp only [covDet]

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.Cutoff
section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

namespace SmoothCutoff

noncomputable def bump (s : ℝ) : ℝ :=
  Real.smoothTransition (20 * (s - 1 / 2)) * Real.smoothTransition (20 * (1 - s))

theorem bump_contDiff : ContDiff ℝ ∞ bump := by
  unfold bump
  apply ContDiff.mul
  · exact Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  · exact Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))

theorem bump_continuous : Continuous bump := bump_contDiff.continuous

theorem bump_nonneg (s : ℝ) : 0 ≤ bump s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem bump_le_one (s : ℝ) : bump s ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem bump_of_le_half {s : ℝ} (h : s ≤ 1 / 2) : bump s = 0 := by
  unfold bump
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem bump_of_one_le {s : ℝ} (h : 1 ≤ s) : bump s = 0 := by
  unfold bump
  rw [Real.smoothTransition.zero_of_nonpos (x := 20 * (1 - s)) (by linarith), mul_zero]

theorem bump_of_mem {s : ℝ} (h1 : 11 / 20 ≤ s) (h2 : s ≤ 19 / 20) : bump s = 1 := by
  unfold bump
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), one_mul]

noncomputable def prim (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, bump s

theorem prim_hasDerivAt (t : ℝ) : HasDerivAt prim (bump t) t :=
  (bump_continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem deriv_prim : deriv prim = bump := funext fun t => (prim_hasDerivAt t).deriv

theorem prim_contDiff : ContDiff ℝ ∞ prim :=
  contDiff_infty_iff_deriv.2
    ⟨fun t => (prim_hasDerivAt t).differentiableAt, by rw [deriv_prim]; exact bump_contDiff⟩

theorem prim_monotone : Monotone prim :=
  monotone_of_deriv_nonneg (fun t => (prim_hasDerivAt t).differentiableAt)
    (fun t => by rw [deriv_prim]; exact bump_nonneg t)

theorem prim_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) : prim t = 0 := by
  unfold prim
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
  intro s hs
  apply bump_of_le_half
  have := (Set.mem_uIcc.1 hs)
  rcases this with h | h <;> linarith [h.1, h.2]

theorem prim_of_one_le {t : ℝ} (ht : 1 ≤ t) : prim t = prim 1 := by
  unfold prim
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
    (bump_continuous.intervalIntegrable _ _) (bump_continuous.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_congr (a := 1) (b := t) (g := fun _ => (0 : ℝ)),
    intervalIntegral.integral_zero, add_zero]
  intro s hs
  rw [Set.uIcc_of_le ht] at hs
  exact bump_of_one_le hs.1

theorem prim_one_ge : 2 / 5 ≤ prim 1 := by
  unfold prim
  have hi : ∀ a b : ℝ, IntervalIntegrable bump volume a b :=
    fun a b => bump_continuous.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 19 / 20) (hi _ _) (hi _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := 11 / 20) (hi _ _) (hi _ _)]
  have h1 : 0 ≤ ∫ s in (0 : ℝ)..11 / 20, bump s :=
    intervalIntegral.integral_nonneg (by norm_num) (fun s _ => bump_nonneg s)
  have h3 : 0 ≤ ∫ s in (19 / 20 : ℝ)..1, bump s :=
    intervalIntegral.integral_nonneg (by norm_num) (fun s _ => bump_nonneg s)
  have h2 : ∫ s in (11 / 20 : ℝ)..19 / 20, bump s = 2 / 5 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
    · simp; norm_num
    · intro s hs
      rw [Set.uIcc_of_le (by norm_num)] at hs
      exact bump_of_mem hs.1 hs.2
  linarith

theorem prim_nonneg (t : ℝ) : 0 ≤ prim t := by
  have := prim_monotone (min_le_left t (1 / 2))
  rwa [prim_of_le_half (min_le_right t (1 / 2))] at this

theorem prim_le (t : ℝ) : prim t ≤ prim 1 := by
  have := prim_monotone (le_max_left t 1)
  rwa [prim_of_one_le (le_max_right t 1)] at this

noncomputable def chi (t : ℝ) : ℝ := 1 - prim t / prim 1

theorem chi_hasDerivAt (t : ℝ) : HasDerivAt chi (-(bump t / prim 1)) t :=
  ((prim_hasDerivAt t).div_const (prim 1)).const_sub 1

theorem isCutoff_chi : IsCutoff chi := by
  have hI : 0 < prim 1 := by linarith [prim_one_ge]
  refine ⟨contDiff_const.sub (prim_contDiff.div_const _), ?_, ?_, ?_, ?_⟩
  · intro t ht
    simp [chi, prim_of_le_half ht]
  · intro t ht
    simp [chi, prim_of_one_le ht, hI.ne']
  · intro t
    have h0 : 0 ≤ prim t / prim 1 := div_nonneg (prim_nonneg t) hI.le
    have h1 : prim t / prim 1 ≤ 1 := (div_le_one hI).2 (prim_le t)
    constructor <;> simp only [chi] <;> linarith
  · intro t
    rw [(chi_hasDerivAt t).deriv, abs_neg, abs_of_nonneg (div_nonneg (bump_nonneg t) hI.le),
      div_le_iff₀ hI]
    nlinarith [bump_le_one t, prim_one_ge]

end SmoothCutoff

theorem cutoff : CutoffStatement := ⟨SmoothCutoff.chi, SmoothCutoff.isCutoff_chi⟩

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.HoloClosedNeed
section
namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Filter Topology
open scoped ENNReal

def HoloClosedNeed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (ps : M → ℝ) (F : ℕ → M → ℂ) (f : M → ℂ),
    SmoothR n X.z ps → (∀ k, Holo n X.z (F k)) → Measurable f →
    Tendsto (fun k => wint n X.z (fun x => F k x - f x) ps) atTop (𝓝 0) →
    ∃ G : M → ℂ, Holo n X.z G ∧ f =ᵐ[vol n X.z] G

def EvalNeed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (ps : M → ℝ) (x0 : M), SmoothR n X.z ps →
    ∃ C : ℝ, ∀ F : M → ℂ, Holo n X.z F →
      ENNReal.ofReal (‖F x0‖ ^ 2) ≤ ENNReal.ofReal C * wint n X.z F ps

def CVXNeed.{u} : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H], CVXStatement H

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
section
open Complex ComplexConjugate Filter Topology Matrix

namespace ReciprocityTheory.L2DbarEstimates

noncomputable def wJac (n p : ℕ) (g : Fin p → V n → ℂ) (x : V n) : Matrix (Fin p) (Fin n) ℂ :=
  fun i k => wd n k (g i) x

def LeviLogNormSqStatement : Prop :=
  ∀ (n p : ℕ) (g : Fin p → V n → ℂ) (x : V n) (ξ : Fin n → ℂ),
    (∀ i, ContDiffAt ℂ 2 (g i) x) → (fun i => g i x) ≠ 0 →
    leviV n (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) x ξ =
      ((sqNorm (projPerp (fun i => g i x) *ᵥ (wJac n p g x *ᵥ ξ)) / sqNorm (fun i => g i x) : ℝ) : ℂ)

variable {n : ℕ}

theorem contDiffAt_normSq_comp {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    ContDiffAt ℝ 2 (fun y => Complex.normSq (g y)) x := by
  have h1 : ContDiffAt ℝ 2 g x := hg.restrict_scalars ℝ
  have h2 : (fun y => Complex.normSq (g y)) = fun y => ‖g y‖ ^ 2 :=
    funext fun y => Complex.normSq_eq_norm_sq _
  rw [h2]
  exact h1.norm_sq ℝ

theorem wd_normSq_comp {j : Fin n} {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    wd n j (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) x = wd n j g x * conj (g x) := by
  have hgC : DifferentiableAt ℂ g x := hg.differentiableAt (by norm_num)
  have hgR : DifferentiableAt ℝ g x := hgC.restrictScalars ℝ
  have hc : DifferentiableAt ℝ (fun y => conj (g y)) x := Complex.conjCLE.differentiableAt.comp x hgR
  rw [show (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) from
    funext fun y => (Complex.mul_conj (g y)).symm, wd_mul hgR hc, wd_conj hgR,
    wdb_of_differentiableAt hgC, map_zero, mul_zero, add_zero]

theorem leviV_normSq_comp {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) x ξ =
      ((Complex.normSq (∑ j, wd n j g x * ξ j) : ℝ) : ℂ) := by
  have hcd : ∀ {f : V n → ℂ} {y : V n}, DifferentiableAt ℝ f y →
      DifferentiableAt ℝ (fun z => conj (f z)) y :=
    fun h => Complex.conjCLE.differentiableAt.comp _ h
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℂ 2 g y := hg.eventually (by simp)
  have hdC : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y :=
    hev.mono fun y hy => hy.differentiableAt (by norm_num)
  have hgR : DifferentiableAt ℝ g x := (hg.differentiableAt (by norm_num)).restrictScalars ℝ

  have hwdk : ∀ k, wd n k g =ᶠ[𝓝 x] fun y => fderiv ℂ g y (bas n k) :=
    fun k => hdC.mono fun y hy => wd_of_differentiableAt hy
  have hfd : ∀ k, DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n k)) x := by
    intro k
    have h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x := hg.fderiv_right (by norm_num)
    exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
  have hwdbwd : ∀ j k, wdb n j (wd n k g) x = 0 :=
    fun j k => (wdb_congr (hwdk k)).trans (wdb_of_differentiableAt (hfd k))
  have hwdR : ∀ k, DifferentiableAt ℝ (wd n k g) x :=
    fun k => ((hfd k).restrictScalars ℝ).congr_of_eventuallyEq (hwdk k)
  have hwdbf : ∀ k, wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun y => g y * conj (wd n k g y) := by
    intro k
    filter_upwards [hev] with y hy
    have hyC : DifferentiableAt ℂ g y := hy.differentiableAt (by norm_num)
    have hyR : DifferentiableAt ℝ g y := hyC.restrictScalars ℝ
    rw [show (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) from
      funext fun y => (Complex.mul_conj (g y)).symm, wdb_mul hyR (hcd hyR), wdb_conj hyR,
      wdb_of_differentiableAt hyC, zero_mul, zero_add]
  have hterm : ∀ j k, wd n j (wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ))) x =
      wd n j g x * conj (wd n k g x) := by
    intro j k
    rw [wd_congr (hwdbf k), wd_mul hgR (hcd (hwdR k)), wd_conj (hwdR k), hwdbwd j k, map_zero,
      mul_zero, add_zero]
  unfold leviV
  simp_rw [hterm]
  rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul]
  ring

theorem leviLogNormSq : LeviLogNormSqStatement := by
  intro n p g x ξ hg hG
  set G : Fin p → ℂ := fun i => g i x with hGdef
  have hpos : 0 < sqNorm G := sqNorm_pos hG
  have hne : ((sqNorm G : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hv : ContDiffAt ℝ 2 (fun y => sqNorm (fun i => g i y)) x := by
    unfold sqNorm
    exact ContDiffAt.sum fun i _ => contDiffAt_normSq_comp (hg i)
  have hk : ContDiffAt ℝ 2 Real.log (sqNorm (fun i => g i x)) := Real.contDiffAt_log.mpr hpos.ne'
  have hc : leviV n (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) x ξ =
      ((deriv Real.log (sqNorm G) : ℝ) : ℂ) *
          leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ +
        ((deriv (deriv Real.log) (sqNorm G) : ℝ) : ℂ) *
          ((Complex.normSq (∑ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x * ξ j) :
            ℝ) : ℂ) :=
    leviChain n Real.log (fun y => sqNorm (fun i => g i y)) x ξ hv hk
  have hlv : leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ =
      ((sqNorm (wJac n p g x *ᵥ ξ) : ℝ) : ℂ) := by
    have h1 : leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ =
        ∑ i, leviV n (fun y => ((Complex.normSq (g i y) : ℝ) : ℂ)) x ξ :=
      leviV_ofReal_sum (u := fun i y => Complex.normSq (g i y))
        (fun i => contDiffAt_normSq_comp (hg i)) ξ
    rw [h1, sqNorm, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => leviV_normSq_comp (hg i) ξ
  have hwd : ∀ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x =
      ∑ i, wd n j (g i) x * conj (g i x) := by
    intro j
    have h1 : wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x =
        ∑ i, wd n j (fun y => ((Complex.normSq (g i y) : ℝ) : ℂ)) x :=
      wd_ofReal_sum (u := fun i y => Complex.normSq (g i y))
        (fun i => (contDiffAt_normSq_comp (hg i)).differentiableAt (by norm_num))
    rw [h1]
    exact Finset.sum_congr rfl fun i _ => wd_normSq_comp (hg i)
  have hS : ∑ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x * ξ j =
      star G ⬝ᵥ (wJac n p g x *ᵥ ξ) := by
    simp only [hwd, dotProduct, Matrix.mulVec, wJac, Pi.star_apply, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hGdef, Complex.star_def]
    ring
  rw [hc, hlv, hS, projPerp_sqNorm p G _ hG, Real.deriv_log, Real.deriv_log', deriv_inv]
  push_cast
  field_simp
  ring

end ReciprocityTheory.L2DbarEstimates
end

