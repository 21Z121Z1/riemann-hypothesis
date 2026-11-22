import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.RightRule
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentOdeFirst
section
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.OdeRoots

theorem energy_pointwise (z x y : ℂ) (s e : ℝ) (hz : z.re < s) (he : 0 ≤ e) :
    2 * (inner ℝ x (z * x + y)) * e + ‖x‖ ^ 2 * (e * (-2 * s)) ≤
      -(s - z.re) * (‖x‖ ^ 2 * e) + (1 / (s - z.re)) * (‖y‖ ^ 2 * e) := by
  have ha : 0 < s - z.re := sub_pos.2 hz
  have h1 : inner ℝ x (z * x + y) = z.re * ‖x‖ ^ 2 + inner ℝ x y := by
    rw [inner_add_right]
    congr 1
    rw [Complex.inner, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have h2 : inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  rw [h1]
  set a := s - z.re with hadef
  set p := ‖x‖
  set q := ‖y‖
  have hs : s = a + z.re := by rw [hadef]; ring
  have h3 : 0 ≤ (a * p - q) ^ 2 / a := by positivity
  have h4 : (a * p - q) ^ 2 / a = a * p ^ 2 - 2 * (p * q) + (1 / a) * q ^ 2 := by
    field_simp
    ring
  have h5 : 2 * (z.re * p ^ 2 + inner ℝ x y) + p ^ 2 * (-2 * s) ≤
      -a * p ^ 2 + (1 / a) * q ^ 2 := by
    rw [hs]
    nlinarith
  have := mul_le_mul_of_nonneg_right h5 he
  nlinarith

theorem odeA : CompanionTheory.RgExh.Dec.N.OdeA := by
  intro z s hz f g hf hg hgi
  have ha : 0 < s - z.re := sub_pos.2 hz
  set a := s - z.re with hadef

  let ft : ℝ → ℂ := fun t => f (max t 0)
  have hfon : ContinuousOn f (Ici 0) := fun t ht =>
    (hf t ht).continuousAt.continuousWithinAt
  have hft : Continuous ft :=
    hfon.comp_continuous (continuous_id.max continuous_const) (fun t => mem_Ici.2 (le_max_right _ _))
  have hfe : ∀ t, 0 ≤ t → ft t = f t := fun t ht => by simp [ft, max_eq_left ht]
  let E : ℝ → ℝ := fun t => Real.exp (-2 * s * t)
  have hE : Continuous E := by fun_prop
  have hEpos : ∀ t, 0 ≤ E t := fun t => (Real.exp_pos _).le
  let U : ℝ → ℝ := fun t => ‖ft t‖ ^ 2 * E t
  let V : ℝ → ℝ := fun t => ‖g t‖ ^ 2 * E t
  have hU : Continuous U := by fun_prop
  have hV : Continuous V := by fun_prop
  have hUn : ∀ t, 0 ≤ U t := fun t => mul_nonneg (by positivity) (hEpos t)
  have hVn : ∀ t, 0 ≤ V t := fun t => mul_nonneg (by positivity) (hEpos t)
  let D : ℝ → ℝ := fun t =>
    2 * (inner ℝ (ft t) (z * ft t + g t)) * E t + ‖ft t‖ ^ 2 * (E t * (-2 * s))
  have hD : Continuous D := by
    have : Continuous fun t => inner ℝ (ft t) (z * ft t + g t) :=
      Continuous.inner hft (by fun_prop)
    fun_prop
  have hDle : ∀ t, D t ≤ -a * U t + (1 / a) * V t := fun t =>
    energy_pointwise z (ft t) (g t) s (E t) hz (hEpos t)
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt (fun x => ‖f x‖ ^ 2 * E x) (D t) t := by
    intro t ht
    have h1 := (hf t ht).norm_sq
    have h2 : HasDerivAt E (E t * (-2 * s)) t := by
      have := ((hasDerivAt_id t).const_mul (-2 * s)).exp
      simpa [E] using this
    have e : D t = 2 * (inner ℝ (f t) (z * f t + g t)) * E t + ‖f t‖ ^ 2 * (E t * (-2 * s)) := by
      simp only [D, hfe t ht]
    rw [e]
    exact h1.mul h2

  have hVlin : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (V t)) < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) hgi
    refine lintegral_congr fun t => ?_
    simp only [V, E]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm]
  have hVint : IntegrableOn V (Ioi 0) :=
    ⟨hV.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ hVn)).2 hVlin⟩
  set C : ℝ := ∫ t in Ioi (0 : ℝ), V t with hC
  have hVle : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, V t ≤ C := by
    intro T hT
    rw [intervalIntegral.integral_of_le hT]
    exact setIntegral_mono_set hVint (ae_of_all _ hVn) Ioc_subset_Ioi_self.eventuallyLE
  have hbound : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, U t ≤ (U 0 + (1 / a) * C) / a := by
    intro T hT
    have hI : ∫ t in (0 : ℝ)..T, D t = ‖f T‖ ^ 2 * E T - ‖f 0‖ ^ 2 * E 0 := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => ‖f x‖ ^ 2 * E x) (fun t ht => ?_)
        (hD.intervalIntegrable _ _)
      rw [uIcc_of_le hT] at ht
      exact hderiv t ht.1
    have hmono : ∫ t in (0 : ℝ)..T, D t ≤ ∫ t in (0 : ℝ)..T, (-a * U t + (1 / a) * V t) :=
      intervalIntegral.integral_mono_on hT (hD.intervalIntegrable _ _)
        (((continuous_const.mul hU).add (continuous_const.mul hV)).intervalIntegrable _ _)
        (fun t _ => hDle t)
    have hsplit : ∫ t in (0 : ℝ)..T, (-a * U t + (1 / a) * V t) =
        -a * (∫ t in (0 : ℝ)..T, U t) + (1 / a) * ∫ t in (0 : ℝ)..T, V t := by
      have c1 : IntervalIntegrable (fun t => -a * U t) volume 0 T :=
        (continuous_const.mul hU).intervalIntegrable _ _
      have c2 : IntervalIntegrable (fun t => (1 / a) * V t) volume 0 T :=
        (continuous_const.mul hV).intervalIntegrable _ _
      rw [intervalIntegral.integral_add c1 c2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hT0 : 0 ≤ ‖f T‖ ^ 2 * E T := mul_nonneg (by positivity) (hEpos T)
    have hU0 : U 0 = ‖f 0‖ ^ 2 * E 0 := by simp only [U, hfe 0 le_rfl]
    have hVa : (1 / a) * ∫ t in (0 : ℝ)..T, V t ≤ (1 / a) * C :=
      mul_le_mul_of_nonneg_left (hVle T hT) (by positivity)
    rw [le_div_iff₀ ha]
    rw [hI, hsplit] at hmono
    nlinarith
  have hUint : IntegrableOn U (Ioi 0) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
      ((U 0 + (1 / a) * C) / a) 0 (l := atTop) (b := fun T : ℝ => T)
      (fun T => (hU.integrableOn_Icc (a := 0) (b := T)).mono_set Ioc_subset_Icc_self) tendsto_id ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hUn _)] using hbound T hT
  have hfin := hUint.lintegral_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  simp only [U, E, hfe t ht0]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm_eq_enorm]

end GlobalTheory.CompanionTheory.OdeRoots
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentRightRule
section
noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RightRule

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec

variable {n : ℕ}

def RightOK (ε : Fin n → Bool) (X : GMod n) (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) : Prop :=
  ∀ (u : X.V) (Y : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inG ε Y → ∀ g, Formalism.REAL.inUJ ε g →
    HasDerivAt (fun t : ℝ => c u (g * NormedSpace.exp ((t : ℂ) • Y))) (c (∑ a, ∑ b, Y a b • X.E a b u) g) 0

set_option backward.isDefEq.respectTransparency false in
theorem exp_entry (Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Y) i j) (Y i j) 0 := by
  have e1 : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Y) i j) =
      fun t : ℝ => Matrix.entryLinearMap ℝ ℂ i j (NormedSpace.exp (t • Y)) := by
    funext t
    have : (t : ℂ) • Y = t • Y := by ext a b; simp [Complex.real_smul]
    rw [this]; rfl
  have e2 : Y i j = Matrix.entryLinearMap ℝ ℂ i j (NormedSpace.exp ((0 : ℝ) • Y) * Y) := by
    simp [NormedSpace.exp_zero]
  rw [e1, e2]
  open scoped Matrix.Norms.Operator in
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0)

theorem mul_exp_entry (g Y : Matrix (Fin n) (Fin n) ℂ) (j i : Fin n) :
    HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • Y)) j i) ((g * Y) j i) 0 := by
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum (u := Finset.univ) (A := fun l (t : ℝ) => g j l * NormedSpace.exp ((t : ℂ) • Y) l i)
    fun l _ => (exp_entry Y l i).const_mul (g j l)

theorem mul_exp_zero (g Y : Matrix (Fin n) (Fin n) ℂ) : g * NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = g := by
  simp [NormedSpace.exp_zero]

theorem tens_action (X : GMod n) (Y : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → X.V) (i : Fin n) :
    (∑ a, ∑ b, Y a b • (tens X).E a b u) i = (∑ a, ∑ b, Y a b • X.E a b (u i)) + ∑ b, Y i b • u b := by
  show (∑ a, ∑ b, (Y a b • tensE X a b u : Fin n → X.V)) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, tensE_apply, smul_add, sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
  simp

theorem tens_ok {ε : Fin n → Bool} {X : GMod n} {c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)}
    (h : RightOK ε X c) (j : Fin n) : RightOK ε (tens X) (tensCoef X c j) := by
  intro u Y hY g hg
  have h1 : ∀ i, HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • Y)) j i *
      c (u i) (g * NormedSpace.exp ((t : ℂ) • Y)))
      ((g * Y) j i * c (u i) g + g j i * c (∑ a, ∑ b, Y a b • X.E a b (u i)) g) 0 := by
    intro i
    refine ((mul_exp_entry g Y j i).fun_mul (h (u i) Y hY g hg)).congr_deriv ?_
    simp only [mul_exp_zero]
  have h2 := HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun i (t : ℝ) => (g * NormedSpace.exp ((t : ℂ) • Y)) j i * c (u i) (g * NormedSpace.exp ((t : ℂ) • Y)))
    fun i _ => h1 i
  refine h2.congr_deriv ?_
  have e : ∀ i, c ((∑ a, ∑ b, Y a b • (tens X).E a b u) i) g =
      c (∑ a, ∑ b, Y a b • X.E a b (u i)) g + ∑ b, Y i b * c (u b) g := by
    intro i
    refine (congrArg (fun v => c v g) (tens_action X Y u i)).trans ?_
    simp only [map_add, Pi.add_apply, map_sum, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  show _ = ∑ i, g j i * c ((∑ a, ∑ b, Y a b • (tens X).E a b u) i) g
  refine Eq.trans ?_ (sum_congr rfl fun i _ => congrArg (g j i * ·) (e i).symm)
  simp only [mul_add, sum_add_distrib, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [add_comm]
  congr 1
  rw [Finset.sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem step_ok {ε : Fin n → Bool} {X : GMod n} {c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)}
    (h : RightOK ε X c) (z : ℂ) (j : Fin n) : RightOK ε (step X z) (stepCoef X z c j) := by
  intro u Y hY g hg
  let S : (step X z).V →ₗ[ℂ] (tens X).V := (stepSub X z).subtype
  have hS : ∀ a b w, S ((step X z).E a b w) = (tens X).E a b (S w) := fun _ _ _ => rfl
  have e : S (∑ a, ∑ b, Y a b • (step X z).E a b u) = ∑ a, ∑ b, Y a b • (tens X).E a b (S u) := by
    simp only [map_sum, map_smul, hS]
  have h1 := tens_ok h j (S u) Y hY g hg
  refine h1.congr_deriv ?_
  show tensCoef X c j _ g = tensCoef X c j (S _) g
  rw [e]

theorem path_ok {ε : Fin n → Bool} : ∀ (ss : List (Fin n)) (X : GMod n)
    (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (χ : Fin n → ℂ) (js : List (Fin n)),
    RightOK ε X c → RightOK ε (path X χ ss) (pathCoef X c χ ss js)
  | [], _, _, _, _, h => h
  | s :: ss, X, c, χ, js, h => path_ok ss (step X (χ s)) (stepCoef X (χ s) c (js.headD s)) (χ + Pi.single s 1) js.tail
      (step_ok h _ _)

theorem base_ok {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hK : CompanionTheory.D.LK.IsKMod ε σ D E) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (ξ : H) :
    RightOK ε ⟨D, E, hK.gl⟩ (baseCoef σ D ξ) := by
  intro u Y hY g hg
  let L : H →L[ℝ] ℂ := ((innerSL ℂ ξ).comp (σ g)).restrictScalars ℝ
  have h1 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hK.real Y hY u)
  have e : (fun t : ℝ => baseCoef σ D ξ u (g * NormedSpace.exp ((t : ℂ) • Y))) =
      L ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) (u : H) := by
    funext t
    show ⟪ξ, σ (g * NormedSpace.exp ((t : ℂ) • Y)) (u : H)⟫_ℂ = ⟪ξ, σ g (σ (NormedSpace.exp ((t : ℂ) • Y)) (u : H))⟫_ℂ
    rw [hσ.1.2 g hg _ (Formalism.REAL.exp_indefinite_unitary_holds n ε Y hY t)]
    rfl
  rw [e]
  refine h1.congr_deriv ?_
  show ⟪ξ, σ g (∑ a, ∑ b, Y a b • (E a b u : H))⟫_ℂ = ⟪ξ, σ g ((∑ a, ∑ b, Y a b • E a b u : D) : H)⟫_ℂ
  simp only [Submodule.coe_sum, Submodule.coe_smul]

theorem rightRule : CompanionTheory.RgExh.Dec.N.RightRule := by
  intro n ε H _ _ _ σ D E hK χ ss hσ i u X hX g hg
  exact path_ok ss ⟨D, E, hK.gl⟩ (baseCoef σ D (i.1 : H)) χ i.2 (base_ok hK hσ _) u X hX g hg

end GlobalTheory.CompanionTheory.RightRule
end
end

