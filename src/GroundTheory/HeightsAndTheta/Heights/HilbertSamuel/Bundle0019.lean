import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.FderivFderivLogRho
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FSLevi

variable {J : Type} [Fintype J]

def reP (p : J) : (J → ℂ) →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj p)

def imaginary (p : J) : (J → ℂ) →L[ℝ] ℝ := Complex.imCLM.comp (ContinuousLinearMap.proj p)

def nsq (z : J → ℂ) : ℝ := ∑ p, (reP p z ^ 2 + imaginary p z ^ 2)

def bil : (J → ℂ) →L[ℝ] ((J → ℂ) →L[ℝ] ℝ) :=
  ∑ p, ((reP p).smulRight (reP p) + (imaginary p).smulRight (imaginary p))

theorem bil_apply (u v : J → ℂ) : bil u v = ∑ p, (reP p u * reP p v + imaginary p u * imaginary p v) := by
  simp [bil, ContinuousLinearMap.sum_apply]

theorem reP_apply (p : J) (z : J → ℂ) : reP p z = (z p).re := rfl

theorem imaginaryPart_apply (p : J) (z : J → ℂ) : imaginary p z = (z p).im := rfl

theorem hasFDerivAt_nsq (z : J → ℂ) : HasFDerivAt nsq ((2 : ℝ) • bil z) z := by
  have h : ∀ p : J, HasFDerivAt (fun z : J → ℂ ↦ reP p z ^ 2 + imaginary p z ^ 2)
      ((2 * reP p z) • reP p + (2 * imaginary p z) • imaginary p) z := by
    intro p
    have h1 := (reP p).hasFDerivAt (x := z) |>.pow 2
    have h2 := (imaginary p).hasFDerivAt (x := z) |>.pow 2
    refine (h1.add h2).congr_fderiv ?_
    ext v
    simp
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun p _ ↦ h p)
  refine hs.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, bil_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  ring

theorem norm_sq_eq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem log_rho_eq (z : J → ℂ) : Real.log ((fsMetric J).ρ z) = (1 / 2) * Real.log (nsq z) := by
  have : (fsMetric J).ρ z = Real.sqrt (nsq z) := by
    simp [fsMetric, EuclideanSpace.norm_eq, nsq, reP_apply, imaginaryPart_apply, norm_sq_eq]
  rw [this, Real.log_sqrt (x := nsq z) (Finset.sum_nonneg fun p _ ↦ by positivity)]
  ring

theorem nsq_pos {z : J → ℂ} (hz : z ≠ 0) : 0 < nsq z := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hz
  refine Finset.sum_pos' (fun q _ ↦ by positivity) ⟨p, Finset.mem_univ _, ?_⟩
  rw [reP_apply, imaginaryPart_apply, ← norm_sq_eq]
  exact pow_pos (norm_pos_iff.mpr hp) 2

theorem hasFDerivAt_logRho {z : J → ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun z ↦ Real.log ((fsMetric J).ρ z)) ((nsq z)⁻¹ • bil z) z := by
  have h := ((hasFDerivAt_nsq z).log (nsq_pos hz).ne').const_mul (1 / 2 : ℝ)
  have e : (fun z ↦ Real.log ((fsMetric J).ρ z)) = fun z ↦ (1 / 2) * Real.log (nsq z) :=
    funext log_rho_eq
  rw [e]
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem hasFDerivAt_deriv {z : J → ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun z ↦ (nsq z)⁻¹ • bil z)
      ((nsq z)⁻¹ • bil + (((ContinuousLinearMap.toSpanSingleton ℝ (-(nsq z ^ 2)⁻¹)).comp
        ((2 : ℝ) • bil z))).smulRight (bil z)) z := by
  have hinv := (hasFDerivAt_inv (𝕜 := ℝ) (nsq_pos hz).ne').comp z (hasFDerivAt_nsq z)
  exact hinv.fun_smul bil.hasFDerivAt

theorem fderiv_fderiv_logRho {z : J → ℂ} (hz : z ≠ 0) :
    fderiv ℝ (fderiv ℝ fun z ↦ Real.log ((fsMetric J).ρ z)) z =
      (nsq z)⁻¹ • bil + (((ContinuousLinearMap.toSpanSingleton ℝ (-(nsq z ^ 2)⁻¹)).comp
        ((2 : ℝ) • bil z))).smulRight (bil z) := by
  have hev : (fderiv ℝ fun z ↦ Real.log ((fsMetric J).ρ z)) =ᶠ[nhds z]
      fun z ↦ (nsq z)⁻¹ • bil z := by
    filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
    exact (hasFDerivAt_logRho hz').fderiv
  rw [hev.fderiv_eq]
  exact (hasFDerivAt_deriv hz).fderiv

theorem cs (z w : J → ℂ) :
    (∑ p, (reP p z * reP p w + imaginary p z * imaginary p w)) ^ 2 +
      (∑ p, (reP p z * reP p (Complex.I • w) + imaginary p z * imaginary p (Complex.I • w))) ^ 2 ≤
      nsq z * nsq w := by
  set a : J → ℂ := fun p ↦ starRingEnd ℂ (z p) * w p
  have h1 : (∑ p, (reP p z * reP p w + imaginary p z * imaginary p w)) = (∑ p, a p).re := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp [a, reP_apply, imaginaryPart_apply, Complex.mul_re]
  have h2 : (∑ p, (reP p z * reP p (Complex.I • w) + imaginary p z * imaginary p (Complex.I • w))) =
      -(∑ p, a p).im := by
    rw [Complex.im_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp [a, reP_apply, imaginaryPart_apply, Complex.mul_re, Complex.mul_im]
    ring
  rw [h1, h2, neg_sq]
  have h3 : (∑ p, a p).re ^ 2 + (∑ p, a p).im ^ 2 = ‖∑ p, a p‖ ^ 2 := (norm_sq_eq _).symm
  rw [h3]
  have h4 : ‖∑ p, a p‖ ≤ ∑ p, ‖z p‖ * ‖w p‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [a]
  have h5 : (∑ p, ‖z p‖ * ‖w p‖) ^ 2 ≤ nsq z * nsq w := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun p ↦ ‖z p‖) (fun p ↦ ‖w p‖)
    simpa [nsq, reP_apply, imaginaryPart_apply, norm_sq_eq] using this
  calc ‖∑ p, a p‖ ^ 2 ≤ (∑ p, ‖z p‖ * ‖w p‖) ^ 2 := by gcongr
    _ ≤ nsq z * nsq w := h5

theorem leviForm_nonneg {z : J → ℂ} (hz : z ≠ 0) (w : J → ℂ) :
    0 ≤ leviForm (fun z ↦ Real.log ((fsMetric J).ρ z)) z w := by
  unfold leviForm
  rw [fderiv_fderiv_logRho hz]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  have hN := nsq_pos hz
  have hww : bil w w = nsq w := by
    rw [bil_apply, nsq]; exact Finset.sum_congr rfl fun p _ ↦ by ring
  have hiw : bil (Complex.I • w) (Complex.I • w) = nsq w := by
    rw [bil_apply, nsq]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp [reP_apply, imaginaryPart_apply]
    ring
  rw [hww, hiw]
  have hc := cs z w
  rw [← bil_apply, ← bil_apply] at hc
  set X := bil z w
  set Y := bil z (Complex.I • w)
  have key : (nsq z)⁻¹ * nsq w + (2 * X) * -(nsq z ^ 2)⁻¹ * X +
      ((nsq z)⁻¹ * nsq w + (2 * Y) * -(nsq z ^ 2)⁻¹ * Y) =
        2 * (nsq z * nsq w - (X ^ 2 + Y ^ 2)) / nsq z ^ 2 := by
    field_simp; ring
  have hnn : 0 ≤ 2 * (nsq z * nsq w - (X ^ 2 + Y ^ 2)) / nsq z ^ 2 :=
    div_nonneg (by linarith) (by positivity)
  have : 0 ≤ (nsq z)⁻¹ * nsq w + (2 * X) * -(nsq z ^ 2)⁻¹ * X +
      ((nsq z)⁻¹ * nsq w + (2 * Y) * -(nsq z ^ 2)⁻¹ * Y) := key ▸ hnn
  nlinarith [this]

end FSLevi

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalCoordinates
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BirationalCoordinates

section Ratios

variable {Ω : Type} [Field Ω] {κ : Type} [Fintype κ]

def ratioField (x : Ix κ → Ω) (c : κ) : Subfield Ω :=
  Subfield.closure (Set.range fun p : Ix κ => x p / x ⟨(), c⟩)

def ratios (x : Ix κ → Ω) (c : κ) : Ix κ → ratioField x c := fun p =>
  ⟨x p / x ⟨(), c⟩, Subfield.subset_closure ⟨p, rfl⟩⟩

omit [Fintype κ] in
theorem ratios_c (x : Ix κ → Ω) {c : κ} (hc : x ⟨(), c⟩ ≠ 0) : ratios x c ⟨(), c⟩ = 1 :=
  Subtype.ext (div_self hc)

omit [Fintype κ] in
theorem eq_mul_ratios (x : Ix κ → Ω) {c : κ} (hc : x ⟨(), c⟩ ≠ 0) (p : Ix κ) :
    x p = x ⟨(), c⟩ * (ratioField x c).subtype (ratios x c p) := by
  change x p = x ⟨(), c⟩ * (x p / x ⟨(), c⟩)
  rw [mul_div_cancel₀ _ hc]

theorem birational_ratios (x : Ix κ → Ω) {c : κ} (hc : x ⟨(), c⟩ ≠ 0) :
    Birational (ι := GlobalTheory κ) (ratios x c) := by
  intro s
  obtain ⟨s, hs⟩ := s
  induction hs using Subfield.closure_induction with
  | mem t ht =>
    obtain ⟨p, rfl⟩ := ht
    refine ⟨fun _ => 1, X p, X ⟨(), c⟩, ?_, ?_, ?_, ?_⟩
    · convert ProjLine.isMultiHomog_X (ι := GlobalTheory κ) p using 1
      funext k
      simp
    · convert ProjLine.isMultiHomog_X (ι := GlobalTheory κ) ⟨(), c⟩ using 1
      funext k
      simp
    · rw [aeval_X, ratios_c x hc]
      exact one_ne_zero
    · rw [aeval_X, aeval_X, ratios_c x hc, mul_one]
      rfl
  | one =>
    refine ⟨0, 1, 1, ProjLine.isMultiHomog_one, ProjLine.isMultiHomog_one, by simp, ?_⟩
    simp only [map_one, mul_one]
    rfl
  | add a b ha hb iha ihb =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hne₁, he₁⟩ := iha
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hne₂, he₂⟩ := ihb
    have hsum : IsMultiHomog (g₁ * h₂ + g₂ * h₁) (d₁ + d₂) := by
      refine ProjLine.mhAdd (ProjLine.mhMul hg₁ hh₂) ?_
      rw [add_comm d₁]
      exact ProjLine.mhMul hg₂ hh₁
    refine ⟨d₁ + d₂, g₁ * h₂ + g₂ * h₁, h₁ * h₂, hsum, ProjLine.mhMul hh₁ hh₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hne₁ hne₂
    · rw [map_add, map_mul, map_mul, map_mul, he₁, he₂]
      have : (⟨a + b, add_mem ha hb⟩ : ratioField x c) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
      rw [this]
      ring
  | neg a ha iha =>
    obtain ⟨d, g, h, hg, hh, hne, he⟩ := iha
    refine ⟨d, -g, h, ProjLine.mhNeg hg, hh, hne, ?_⟩
    rw [map_neg, he]
    have : (⟨-a, neg_mem ha⟩ : ratioField x c) = -⟨a, ha⟩ := rfl
    rw [this]
    ring
  | inv a ha iha =>
    obtain ⟨d, g, h, hg, hh, hne, he⟩ := iha
    by_cases ha0 : (⟨a, ha⟩ : ratioField x c) = 0
    · refine ⟨0, 0, 1, ProjLine.isMultiHomog_zero _, ProjLine.isMultiHomog_one, by simp, ?_⟩
      have : (⟨a⁻¹, inv_mem ha⟩ : ratioField x c) = (⟨a, ha⟩ : ratioField x c)⁻¹ := rfl
      rw [this, ha0]
      simp
    · have hg0 : aeval (ratios x c) g ≠ 0 := by
        rw [he]
        exact mul_ne_zero ha0 hne
      refine ⟨d, h, g, hh, hg, hg0, ?_⟩
      have : (⟨a⁻¹, inv_mem ha⟩ : ratioField x c) = (⟨a, ha⟩ : ratioField x c)⁻¹ := rfl
      rw [this, he]
      field_simp
  | mul a b ha hb iha ihb =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hne₁, he₁⟩ := iha
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hne₂, he₂⟩ := ihb
    refine ⟨d₁ + d₂, g₁ * g₂, h₁ * h₂, ProjLine.mhMul hg₁ hg₂, ProjLine.mhMul hh₁ hh₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hne₁ hne₂
    · rw [map_mul, map_mul, he₁, he₂]
      have : (⟨a * b, mul_mem ha hb⟩ : ratioField x c) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [this]
      ring

end Ratios

theorem proof : Statement := by
  intro Ω _ _ κ _ x c hc
  have hx := eq_mul_ratios x hc
  refine ⟨ratioField x c, inferInstance, inferInstance, ratios x c,
    mCoordIdeal_eq (ratioField x c).subtype hc hx, birational_ratios x hc,
    fun A τ => smallSectionCount_eq_of_birational (ratioField x c).subtype hc hx hc A τ⟩

end BirationalCoordinates

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLatticeCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Metric Module ZSpan

noncomputable section

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (La : Submodule ℤ V) {c : ℝ}

theorem LatticeCount.exists_near (B : ShortLatticeBasis La c) (x : V) :
    ∃ μ ∈ La, ‖x + μ‖ ≤ finrank ℝ V * c := by
  let e := basisOfLinearIndependentOfCardEqFinrank' B.vec B.linearIndependent (Fintype.card_fin _)
  have he : ∀ i, e i = B.vec i := fun i ↦ by simp [e]
  refine ⟨-((floor e x : Submodule.span ℤ (Set.range e)) : V), ?_, ?_⟩
  · refine La.neg_mem ?_
    have hle : Submodule.span ℤ (Set.range e) ≤ La := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [he]
      exact B.mem i
    exact hle (floor e x).2
  · rw [← sub_eq_add_neg, ← fract_apply]
    calc ‖fract e x‖ ≤ ∑ i, ‖e i‖ := norm_fract_le e x
      _ ≤ ∑ _i : Fin (finrank ℝ V), c :=
          Finset.sum_le_sum fun i _ ↦ by rw [he]; exact B.norm_le i
      _ = _ := by simp

theorem LatticeCount.encard_le (B : ShortLatticeBasis La c) (b : ℝ) (x : V) :
    {y : V | y ∈ La ∧ ‖y‖ ≤ b}.encard ≤
      {g : La | g +ᵥ x ∈ closedBall (0 : V) (b + finrank ℝ V * c)}.encard := by
  classical
  obtain ⟨μ, hμ, hxμ⟩ := LatticeCount.exists_near La B x
  refine Set.encard_le_encard_of_injOn
    (f := fun y : V ↦ if h : y ∈ La then (⟨y + μ, La.add_mem h hμ⟩ : La) else 0) ?_ ?_
  · rintro y ⟨hy, hyb⟩
    simp only [Set.mem_ofPred_eq, hy, dif_pos, mem_closedBall, dist_zero_right,
      Submodule.vadd_def, vadd_eq_add]
    calc ‖y + μ + x‖ = ‖y + (x + μ)‖ := by congr 1; abel
      _ ≤ ‖y‖ + ‖x + μ‖ := norm_add_le _ _
      _ ≤ b + finrank ℝ V * c := add_le_add hyb hxμ
  · rintro y ⟨hy, -⟩ y' ⟨hy', -⟩ h
    simp only [hy, hy', dif_pos, Subtype.mk.injEq, add_left_inj] at h
    exact h

end

theorem LatticeCount.proof : LatticeCount.Statement := by
  intro V _ _ _ _ _ La _ _ c b B hb
  set R := finrank ℝ V with hRdef
  set S := {x : V | x ∈ La ∧ ‖x‖ ≤ b}
  have hfin : S.Finite := finite_lattice_closedBall La b
  refine ⟨hfin, ?_⟩
  have hRc : 0 ≤ (R : ℝ) * c := by
    rcases Nat.eq_zero_or_pos R with h | h
    · simp [h]
    · exact mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (B.norm_le ⟨0, h⟩))
  set r := b + R * c with hrdef
  have hr : 0 ≤ r := add_nonneg hb hRc
  have : MeasurableVAdd La V := (inferInstance : MeasurableVAdd La.toAddSubgroup V)
  have : VAddInvariantMeasure La V volume :=
    (inferInstance : VAddInvariantMeasure La.toAddSubgroup V volume)
  set bz := Free.chooseBasis ℤ La
  have hF := ZLattice.isAddFundamentalDomain bz volume
  set F := fundamentalDomain (bz.ofZLatticeBasis ℝ La)
  set A := closedBall (0 : V) r
  have hA : MeasurableSet A := measurableSet_closedBall
  have hmeas : ∀ g : La, Measurable fun x : V ↦ A.indicator (1 : V → ENNReal) (g +ᵥ x) :=
    fun g ↦ (measurable_one.indicator hA).comp (measurable_const_vadd g)
  have key : ∀ x : V,
      (S.encard : ENNReal) ≤ ∑' g : La, A.indicator (1 : V → ENNReal) (g +ᵥ x) := by
    intro x
    have hind : (fun g : La ↦ A.indicator (1 : V → ENNReal) (g +ᵥ x)) =
        {g : La | g +ᵥ x ∈ A}.indicator 1 := by
      funext g
      by_cases hg : g +ᵥ x ∈ A <;> simp [hg]
    rw [hind, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    exact_mod_cast LatticeCount.encard_le La B b x
  have hFfin : volume F ≠ ⊤ := (fundamentalDomain_isBounded _).measure_lt_top.ne
  have hvol : (S.encard : ENNReal) * ENNReal.ofReal (ZLattice.covolume La) ≤ volume A := by
    calc (S.encard : ENNReal) * ENNReal.ofReal (ZLattice.covolume La)
        = (S.encard : ENNReal) * volume F := by
          rw [ZLattice.covolume_eq_measure_fundamentalDomain La volume hF,
            ofReal_measureReal hFfin]
      _ = ∫⁻ _ in F, (S.encard : ENNReal) := (setLIntegral_const F _).symm
      _ ≤ ∫⁻ x in F, ∑' g : La, A.indicator 1 (g +ᵥ x) := lintegral_mono key
      _ = ∑' g : La, ∫⁻ x in F, A.indicator 1 (g +ᵥ x) :=
          lintegral_tsum fun g ↦ (hmeas g).aemeasurable
      _ = ∫⁻ x, A.indicator 1 x := (hF.lintegral_eq_tsum'' _).symm
      _ = volume A := lintegral_indicator_one hA
  have hunit : volume (ball (0 : V) 1) =
      volume (ball (0 : EuclideanSpace ℝ (Fin R)) 1) := by
    let f := (stdOrthonormalBasis ℝ V).repr
    rw [← f.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet,
      f.preimage_ball, map_zero]
  have hunitfin : volume (ball (0 : EuclideanSpace ℝ (Fin R)) 1) ≠ ⊤ :=
    isBounded_ball.measure_lt_top.ne
  have hball : volume A = ENNReal.ofReal (unitBallVolume R * r ^ R) := by
    rw [Measure.addHaar_closedBall volume 0 hr, hunit, unitBallVolume,
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hunitfin, mul_comm]
  have hS : (S.encard : ENNReal) * ENNReal.ofReal (ZLattice.covolume La) =
      ENNReal.ofReal (S.ncard * ZLattice.covolume La) := by
    rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hpos : 0 ≤ unitBallVolume R * r ^ R :=
    mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hr _)
  have := (hS ▸ hvol).trans_eq hball
  exact (ENNReal.ofReal_le_ofReal_iff hpos).1 this

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

