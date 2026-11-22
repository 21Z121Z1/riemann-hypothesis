import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0130
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0124
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffBoundaryBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0080
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0121
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0084
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0077
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0122
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0129
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0109
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0101
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0093
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0125
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBoundaryBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi CutOffBoundaryBound
open scoped ContDiff

noncomputable section

namespace SliceBoundaryBound

theorem levi_log_dualNorm_comp_nonneg {n D : ℕ} (h : HermNorm n) {τ : (Fin D → ℂ) → Fin n → ℂ}
    {z : Fin D → ℂ} (hτ : AnalyticAt ℂ τ z) (hz : τ z ≠ 0) (ξ : Fin D → ℂ) :
    0 ≤ levi ((fun x => Real.log (h.dualNorm x)) ∘ τ) z ξ := by
  let L : (Fin n → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin (FubiniStudyLogRegularization.regMat h 0 1))
  have hL : ∀ x, L x = FubiniStudyLogRegularization.regMat h 0 1 *ᵥ x := fun x => rfl
  have hσ : AnalyticAt ℂ (L ∘ τ) z := (L.analyticAt _).comp hτ
  have hS : sqSum ((L ∘ τ) z) ≠ 0 := by
    rw [Function.comp_apply, hL]
    exact SheetLogNormDensity.sqSum_ne_zero (FubiniStudyLogRegularization.regMat_mulVec_ne_zero h 0 one_pos hz)
  have hfun : (fun x => Real.log (h.dualNorm x)) ∘ τ = phi ∘ (L ∘ τ) := by
    funext y
    simp only [Function.comp_apply, hL]
    rw [FubiniStudyLogRegularization.log_dualNorm_eq]
    exact SheetLogNormDensity.log_sqrt_eq_phi _
  rw [hfun, levi_comp ξ hσ (contDiffAt_phi hS)]
  exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _

theorem exists_psh_nhd {n D : ℕ} (h : HermNorm n) {s : (Fin D → ℂ) → Fin n → ℂ} {y : Fin D → ℂ}
    (hs : AnalyticAt ℂ s y) (hy : s y ≠ 0) :
    ∃ U : Set (Fin D → ℂ), IsOpen U ∧ y ∈ U ∧
      ContDiffOn ℝ 2 ((fun x => Real.log (h.dualNorm x)) ∘ s) U ∧
      ∀ z ∈ U, ∀ ξ, 0 ≤ levi ((fun x => Real.log (h.dualNorm x)) ∘ s) z ξ := by
  have hev : ∀ᶠ z in 𝓝 y, AnalyticAt ℂ s z ∧ s z ≠ 0 :=
    hs.eventually_analyticAt.and (hs.continuousAt.eventually_ne hy)
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp hev
  refine ⟨U, hUo, hyU, fun z hz => ?_, fun z hz ξ =>
    levi_log_dualNorm_comp_nonneg h (hU z hz).1 (hU z hz).2 ξ⟩
  have hc : ContDiffAt ℝ 2 (fun x => Real.log (h.dualNorm x)) (s z) :=
    ((contDiffOn_log_dualNorm h).contDiffAt (isOpen_compl_singleton.mem_nhds (hU z hz).2)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  exact (hc.comp z (hU z hz).1.restrictScalars.contDiffAt).contDiffWithinAt

theorem abs_le_of_sq_le {v a b : ℝ} (ha : 0 ≤ a) (h : v ^ 2 ≤ a * b) : |v| ≤ 1 * √a * √b := by
  rw [one_mul, ← Real.sqrt_mul ha]
  exact Real.abs_le_sqrt h

theorem vecCons_log_eq {n e : ℕ} (h : HermNorm n) (f : (Fin n → ℂ) → ℝ) :
    (vecCons f fun _ x => Real.log (h.dualNorm x) : Fin (e + 1) → (Fin n → ℂ) → ℝ) =
      fun k x => (vecCons 0 fun _ => 1 : Fin (e + 1) → ℝ) k * Real.log (h.dualNorm x) +
        (vecCons f fun _ _ => 0 : Fin (e + 1) → (Fin n → ℂ) → ℝ) k x := by
  funext k x
  refine Fin.cases ?_ (fun i => ?_) k <;> simp

end SliceBoundaryBound

open SliceBoundaryBound in

theorem SliceBoundaryBound.proof (hM : ChartMassCompact.Statement) (hSM : SliceFormMass.Statement) :
    SliceBoundaryBound.Statement := by
  intro n e h W g ℓ A F G hW hg hℓ hA hF0 hG0 hFs hGs
  obtain ⟨hIp, hdim, -⟩ := SliceIdeal.proof n (e + 1) W g ℓ hW hg hℓ
  have hZ0 : ∀ x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ - 1}), x ≠ 0 :=
    fun x hx => ne_zero_of_mem_zeroSet_slice hx
  have hU0 : IsOpen {x : Fin n → ℂ | x ≠ 0} := isOpen_ne
  have hsm : ∀ f : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ f {x | x ≠ 0} →
      SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) f :=
    fun f hf => ⟨_, hU0, fun x hx => hZ0 x hx, hf⟩
  have hLs : ContDiffOn ℝ ∞ (fun x : Fin n → ℂ => Real.log (h.dualNorm x)) {x | x ≠ 0} :=
    (contDiffOn_log_dualNorm h).mono fun x hx => hx
  have hω : ∀ i : Fin e, SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1}))
      ((fun _ x => Real.log (h.dualNorm x)) i : (Fin n → ℂ) → ℝ) := fun _ => hsm _ hLs
  have hcons : ∀ (f : (Fin n → ℂ) → ℝ) (ψ : Fin e → (Fin n → ℂ) → ℝ),
      SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) f →
      (∀ i, SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) (ψ i)) →
      ∀ i, SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) (vecCons f ψ i) := by
    intro f ψ hf hψ i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hf
    · simpa using hψ i
  have hoff : ∀ f : (Fin n → ℂ) → ℝ, ContinuousOn f {x | x ≠ 0} →
      ContinuousOn f (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) :=
    fun f hf => hf.mono fun x hx => hZ0 x hx
  have hFc : ContinuousOn F {x | x ≠ 0} := hFs.continuousOn
  have hGc : ContinuousOn G {x | x ≠ 0} := hGs.continuousOn

  have hslice : ∀ w f : (Fin n → ℂ) → ℝ, (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → w (t • x) = w x) →
      ContinuousOn w {x | x ≠ 0} → (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → f (t • x) = f x) →
      ContDiffOn ℝ ∞ f {x | x ≠ 0} →
      Integrable (chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A w
        (vecCons f fun _ x => Real.log (h.dualNorm x))) := by
    intro w f hw0 hwc hf0 hfs
    have hI := hSM n e h W g ℓ A w (vecCons 0 fun _ => 1) (vecCons f fun _ _ => 0) hW hg hℓ hA hw0 hwc
      (fun k => Fin.cases (fun t x ht => by simpa using hf0 t x ht) (fun i t x _ => by simp) k)
      (fun k => Fin.cases (by simpa using hfs) (fun i => by simpa using contDiffOn_const) k)
    rw [← vecCons_log_eq] at hI
    exact hI.mono' (measurable_chartDens hIp hdim hA (hoff w hwc) (hcons _ _ (hsm f hfs) hω)).aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using abs_chartDens_le _ A _ _ y)
  have hG2 : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → (fun x => G x ^ 2) (t • x) = (fun x => G x ^ 2) x :=
    fun t x ht => by simp only [hG0 t x ht]
  have hf₁ := hslice (fun x => G x ^ 2) (fun x => F x ^ 2 / 2) hG2 (hGc.pow 2)
    (fun t x ht => by simp only [hF0 t x ht]) ((hFs.pow 2).div_const 2)
  have hf₂ := hslice (fun x => G x ^ 2 * F x) F (fun t x ht => by simp only [hG0 t x ht, hF0 t x ht])
    ((hGc.pow 2).mul hFc) hF0 hFs
  set Φ := ∫ y, (chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => G x ^ 2)
      (vecCons (fun x => F x ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
    chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => G x ^ 2 * F x)
      (vecCons F fun _ x => Real.log (h.dualNorm x)) y) with hΦ

  obtain ⟨M₀, hM₀⟩ := bounded_of_degree_zero (fun x => G x * F x)
    (fun t x ht => by simp only [hG0 t x ht, hF0 t x ht]) (hGc.mul hFc)
  have hM₀0 : 0 ≤ M₀ := (abs_nonneg _).trans (hM₀ 0)
  refine ⟨max M₀ (2 * 1 * √(max Φ 1)), le_max_of_le_left hM₀0, fun χ hχ hχcs => ?_⟩
  have hχc : Continuous χ := hχ.continuous
  have hχn := hsm χ hχ.contDiffOn
  have hχFn := hsm (fun x => χ x * F x) (hχ.contDiffOn.mul hFs)
  have hχ2n := hsm (fun x => χ x ^ 2 / 2) ((hχ.pow 2).div_const 2).contDiffOn
  have hFn := hsm F hFs
  have hχ2cs : HasCompactSupport (fun x => χ x ^ 2 / 2) := hχcs.mono fun x hx h0 => hx (by simp [h0])
  have hD₁ := integrable_chartDens hM hIp hdim hA (hoff G hGc) (hcons _ _ hχFn hω)
    (Or.inr ⟨0, by rw [Matrix.cons_val_zero]; exact (hχcs.mul_right : HasCompactSupport (χ * F))⟩)
  have hD₂ := integrable_chartDens hM hIp hdim hA (f := fun x => χ x * G x)
    (hχc.continuousOn.mul (hoff G hGc)) (hcons _ _ hFn hω)
    (Or.inl (hχcs.mul_right : HasCompactSupport (χ * G)))
  have ha := hM n (e + 1) _ A (fun _ => 1) _ hIp hdim hA continuousOn_const (hcons _ _ hχn hω)
    (Or.inr ⟨0, by rw [Matrix.cons_val_zero]; exact hχcs⟩)
  have he₁ := integrable_chartDens hM hIp hdim hA (f := fun _ => 1) continuousOn_const (hcons _ _ hχ2n hω)
    (Or.inr ⟨0, by rw [Matrix.cons_val_zero]; exact hχ2cs⟩)
  have he₂ := integrable_chartDens hM hIp hdim hA (f := χ) hχc.continuousOn (hcons _ _ hχn hω)
    (Or.inl hχcs)
  have hle2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

  have key : ∀ t > 0, ∀ y,
      |chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A G
          (vecCons (fun x => χ x * F x) fun _ x => Real.log (h.dualNorm x)) y -
        chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => χ x * G x)
          (vecCons F fun _ x => Real.log (h.dualNorm x)) y| ≤
      M₀ * chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
          (vecCons χ fun _ x => Real.log (h.dualNorm x)) y +
      1 * t * (chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
          (vecCons (fun x => χ x ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
        chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A χ (vecCons χ fun _ x => Real.log (h.dualNorm x)) y) +
      1 / t * (chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => G x ^ 2)
          (vecCons (fun x => F x ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
        chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => G x ^ 2 * F x)
          (vecCons F fun _ x => Real.log (h.dualNorm x)) y) := by
    intro t ht y
    have hfin := (FibreBound.proof n (e + 1) _ A hIp hdim hA y).2.1
    unfold chartDens chartAbsDens
    refine abs_sheetSum_sub_le hfin _ _ _ _ _ _ _ _ _ _ fun x hx s hs => ?_
    obtain ⟨hxZ, hAx⟩ := hx
    have hsx : s y = x := by
      obtain ⟨_, _, _, _, h, -⟩ := hs
      rw [← hAx]
      exact h
    have han : AnalyticAt ℂ s y := by
      rw [← hAx]
      exact analyticAt_of_isSheetAt hs
    have hsc : ContDiffAt ℝ 2 s y := han.restrictScalars.contDiffAt
    have hy0 : s y ≠ 0 := hsx ▸ hZ0 x hxZ
    have c2 : ∀ f : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ f {x | x ≠ 0} → ContDiffAt ℝ 2 (f ∘ s) y :=
      fun f hf => ((hf.contDiffAt (hU0.mem_nhds hy0)).of_le hle2).comp y hsc
    have hχs := c2 χ hχ.contDiffOn
    have hFs' := c2 F hFs
    obtain ⟨U, hUo, hyU, hC2, hlev⟩ := exists_psh_nhd h han hy0
    simp only [vecCons_comp]
    have e₁ : maDens (Fin.cons ((fun x => χ x * F x) ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y =
        (χ ∘ s) y * maDens (Fin.cons (F ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y +
          (F ∘ s) y * maDens (Fin.cons (χ ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y +
            gradDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (χ ∘ s) (F ∘ s) y +
            gradDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (F ∘ s) (χ ∘ s) y :=
      (MaDensLeibniz.proof e (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (χ ∘ s) (F ∘ s) y hχs hFs').1
    have e₂ : maDens (Fin.cons ((fun x => χ x ^ 2 / 2) ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y =
        (χ ∘ s) y * maDens (Fin.cons (χ ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y +
          gradDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (χ ∘ s) (χ ∘ s) y :=
      (MaDensLeibniz.proof e (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (χ ∘ s) (χ ∘ s) y hχs hχs).2
    have e₃ : maDens (Fin.cons ((fun x => F x ^ 2 / 2) ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y =
        (F ∘ s) y * maDens (Fin.cons (F ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y +
          gradDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (F ∘ s) (F ∘ s) y :=
      (MaDensLeibniz.proof e (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (F ∘ s) (F ∘ s) y hFs' hFs').2
    have hEχ := gradDensNonneg_thm e (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (χ ∘ s) U hUo
      (fun _ => hC2) (fun _ => hlev) y hyU
    have hEF := gradDensNonneg_thm e (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (F ∘ s) U hUo
      (fun _ => hC2) (fun _ => hlev) y hyU
    have h₁ := abs_le_of_sq_le hEχ (gradDensCauchySchwarz_thm e
      (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (χ ∘ s) (F ∘ s) U hUo (fun _ => hC2) (fun _ => hlev) y hyU)
    have h₂ := abs_le_of_sq_le hEF (gradDensCauchySchwarz_thm e
      (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (F ∘ s) (χ ∘ s) U hUo (fun _ => hC2) (fun _ => hlev) y hyU)
    rw [e₁, e₂, e₃]
    simp only [Function.comp_apply, hsx] at hEχ hEF h₁ h₂ ⊢
    rw [show ∀ m E : ℝ, 1 * (χ x * m + E) - χ x * m = 1 * E from fun m E => by ring,
      show ∀ m E : ℝ, G x ^ 2 * (F x * m + E) - G x ^ 2 * F x * m = G x ^ 2 * E from fun m E => by ring]
    exact term_bound ht zero_le_one (hM₀ x) hEχ hEF h₁ h₂

  refine final_bound zero_le_one (integral_nonneg fun y => chartAbsDens_nonneg _ A _ _ y) fun t ht => ?_
  set D₁ := chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A G
    (vecCons (fun x => χ x * F x) fun _ x => Real.log (h.dualNorm x)) with hD₁def
  set D₂ := chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => χ x * G x)
    (vecCons F fun _ x => Real.log (h.dualNorm x)) with hD₂def
  set a := chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
    (vecCons χ fun _ x => Real.log (h.dualNorm x)) with hadef
  set e₁ := chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
    (vecCons (fun x => χ x ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) with he₁def
  set e₂ := chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A χ
    (vecCons χ fun _ x => Real.log (h.dualNorm x)) with he₂def
  set f₁ := chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => G x ^ 2)
    (vecCons (fun x => F x ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) with hf₁def
  set f₂ := chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => G x ^ 2 * F x)
    (vecCons F fun _ x => Real.log (h.dualNorm x)) with hf₂def
  have h1 : chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A G
        (vecCons (fun x => χ x * F x) fun _ x => Real.log (h.dualNorm x)) -
      chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => χ x * G x)
        (vecCons F fun _ x => Real.log (h.dualNorm x)) = ∫ y, (D₁ y - D₂ y) :=
    (integral_sub hD₁ hD₂).symm
  have h2 : chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
        (vecCons (fun x => χ x ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) -
      chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A χ (vecCons χ fun _ x => Real.log (h.dualNorm x)) =
      ∫ y, (e₁ y - e₂ y) := (integral_sub he₁ he₂).symm
  have h3 : ∫ y, (M₀ * a y + 1 * t * (e₁ y - e₂ y) + 1 / t * (f₁ y - f₂ y)) =
      M₀ * (∫ y, a y) + 1 * t * (∫ y, (e₁ y - e₂ y)) + 1 / t * Φ := by
    rw [integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul]
    all_goals first
      | exact ha.const_mul _
      | exact (he₁.sub he₂).const_mul _
      | exact (hf₁.sub hf₂).const_mul _
      | exact (ha.const_mul _).add ((he₁.sub he₂).const_mul _)
  rw [h1, h2, ← h3]
  refine le_trans ?_ (integral_mono (hD₁.sub hD₂).abs (((ha.const_mul _).add ((he₁.sub he₂).const_mul _)).add
    ((hf₁.sub hf₂).const_mul _)) fun y => key t ht y)
  exact (by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm fun y => D₁ y - D₂ y :
    |∫ y, (D₁ y - D₂ y)| ≤ ∫ y, |D₁ y - D₂ y|)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegCutTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

theorem SliceRegCutTail.proof (hM : SliceFormMass.Statement) : SliceRegCutTail.Statement := by
  classical
  intro n e h W F u' ℓ ε hW hF hℓ hε
  obtain ⟨hprime, hdim, -⟩ := SliceIdeal.proof n (e + 1) W F ℓ hW hF hℓ
  set I := W ⊔ Ideal.span {linForm ℓ - 1} with hIdef
  have hmem : linForm ℓ - 1 ∈ I := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  unfold varInt
  split_ifs with hA
  swap
  · exact tendsto_const_nhds
  set A := hA.choose
  have hAf : IsFiniteProjection I A := hA.choose_spec
  have hfin : ∀ y, (fibre I A y).Finite := fun y =>
    (ComplexSets.FibreBound.proof n (e + 1) I A hprime hdim hAf y).2.1
  have hne : zeroSet I ⊆ {x | x ≠ 0} := fun x hx hx0 => by
    subst hx0
    have := hx _ hmem
    simp [linForm] at this
  set φ : Fin (e + 1) → (Fin n → ℂ) → ℝ :=
    vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x) with hφ
  have hsm : ∀ i, SmoothNear (zeroSet I) (φ i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact ⟨{x | x ≠ 0}, isOpen_ne, hne, by simpa [hφ] using contDiffOn_fsLogReg h u' hε⟩
    · exact ⟨{x | x ≠ 0}, isOpen_ne, hne, by simpa [hφ] using h.contDiffOn_log_dualNorm⟩
  have hint : Integrable (chartAbsDens I A (fun _ => 1) φ) := by
    rw [hφ, SliceCutOffLimit.vecCons_eq_affine h (fsLogReg h u' ε)]
    refine hM n e h W F ℓ A _ _ _ hW hF hℓ hAf (fun _ _ _ => rfl) continuousOn_const
      (fun k t x ht => ?_) (fun k => ?_)
    · refine Fin.cases ?_ (fun i => ?_) k
      · simpa using fsLogReg_smul h u' ε t x ht
      · simp
    · refine Fin.cases ?_ (fun i => ?_) k
      · simpa using contDiffOn_fsLogReg h u' hε
      · simpa using contDiffOn_const
  unfold chartInt
  have key := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (F := fun k => chartDens I A (fun x => 1 - sliceCut h k x) φ) (chartAbsDens I A (fun _ => 1) φ)
    (fun k => (SheetSumMeasurable.proof n (e + 1) I A _ _ hprime hdim hAf
      (measurable_const.sub (SliceCut.measurable h k)) hsm).1.aestronglyMeasurable) hint
    (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · rwa [integral_zero] at key
  · rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens
    rw [CutOffDominated.sheetSum_eq_sum _ (hfin y), CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    split_ifs with hs
    · have h01 := SliceCut.mem_Icc h k x
      rw [abs_mul, abs_mul, abs_one, one_mul, abs_of_nonneg (by linarith [h01.2])]
      exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [h01.1])
    · simp
  · unfold chartDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    have hterm : ∀ x, Tendsto (fun k : ℕ => if hs : ∃ s, IsSheetAt I A x s then
        (1 - sliceCut h k x) * ReciprocityTheory.AnForm.maDens (fun i => φ i ∘ hs.choose) y else 0)
        atTop (𝓝 0) := fun x => by
      split_ifs with hs
      · simpa using ((SliceCut.tendsto_one h x).const_sub 1).mul_const
          (ReciprocityTheory.AnForm.maDens (fun i => φ i ∘ hs.choose) y)
      · exact tendsto_const_nhds
    simpa using tendsto_finsetSum (hfin y).toFinset fun x _ => hterm x

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegMassMono
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm FormIntegralPositivity
open scoped ContDiff

noncomputable section

theorem SliceRegMassMono.proof (hM : SliceFormMass.Statement) : SliceRegMassMono.Statement := by
  intro n e h W F u' ℓ ε a b hW hF hℓ hε ha hb ha0 hab hb1
  unfold varInt
  split_ifs with hA
  swap
  · simp
  have hAfin := hA.choose_spec
  unfold chartInt

  have hint : ∀ w : (Fin n → ℂ) → ℝ, Measurable w → (∀ x, |w x| ≤ 1) →
      ∀ (c : Fin (e + 1) → ℝ) (ψ : Fin (e + 1) → (Fin n → ℂ) → ℝ),
      (∀ k (t : ℂ) x, t ≠ 0 → ψ k (t • x) = ψ k x) → (∀ k, ContDiffOn ℝ ∞ (ψ k) {x | x ≠ 0}) →
      Integrable (chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) hA.choose w
        fun k x => c k * Real.log (h.dualNorm x) + ψ k x) := by
    intro w hw hw1 c ψ hψ hψs
    refine Integrable.mono' (hM n e h W F ℓ hA.choose (fun _ => 1) c ψ hW hF hℓ hAfin
      (fun _ _ _ => rfl) continuousOn_const hψ hψs) ?_ (Eventually.of_forall fun y => ?_)
    · exact (SheetSumMeasurable.measurable_sheetSum hAfin (fun a b => a * b)
        (continuous_fst.mul continuous_snd).measurable hw _).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hAfin y
      simp only [chartDens, chartAbsDens, sheetSum, finsum_mem_eq_finite_toFinset_sum _ hfin]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
      split_ifs
      · simp only [abs_mul, one_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (hw1 x)
      · simp
  have h1 : ∀ w : (Fin n → ℂ) → ℝ, Measurable w → (∀ x, |w x| ≤ 1) →
      Integrable (chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) hA.choose w
        (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))) := by
    intro w hw hw1
    have e1 : (fun (k : Fin (e + 1)) x => (vecCons 0 fun _ => 1 : Fin (e + 1) → ℝ) k *
        Real.log (h.dualNorm x) + (vecCons (fsLogReg h u' ε) fun _ _ => 0 :
          Fin (e + 1) → (Fin n → ℂ) → ℝ) k x) =
        vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x) := by
      funext k x
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩ <;> simp
    rw [← e1]
    refine hint w hw hw1 _ _ (fun k t x ht => ?_) fun k => ?_
    · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
      · exact FubiniStudyLogRegularization.fsLogReg_smul h u' ε ht x
      · rfl
    · rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
      · exact FubiniStudyLogRegularization.contDiffOn_fsLogReg h u' hε
      · exact contDiffOn_const
  have h2 : ∀ w : (Fin n → ℂ) → ℝ, Measurable w → (∀ x, |w x| ≤ 1) →
      Integrable (chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) hA.choose w
        fun _ x => Real.log (h.dualNorm x)) := by
    intro w hw hw1
    have := hint w hw hw1 (fun _ => 1) (fun _ _ => 0) (fun _ _ _ _ => rfl) fun _ => contDiffOn_const
    simpa using this
  have ha1 : ∀ x, |a x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [ha0 x], by linarith [hab x, hb1 x]⟩
  have hb1' : ∀ x, |b x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [ha0 x, hab x], hb1 x⟩
  rw [← integral_add (h1 a ha ha1) (h2 a ha ha1), ← integral_add (h1 b hb hb1') (h2 b hb hb1')]
  refine integral_mono ((h1 a ha ha1).add (h2 a ha ha1)) ((h1 b hb hb1').add (h2 b hb hb1'))
    fun y => ?_

  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hAfin y
  simp only [chartDens, sheetSum, finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, rfl⟩ := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hxZ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    simp [linForm] at this
  split_ifs with hs
  · have hpos := dens_sum_nonneg SheetLogNormDens.proof h u' hε hs.choose_spec hx0
    have hmono := mul_le_mul_of_nonneg_right (hab x) hpos
    linarith
  · simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLevelSet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

def SliceLevelSet.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)
    (ψ : ℝ → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) g → linForm ℓ ∉ W →
    IsFiniteProjection (W ⊔ Ideal.span {linForm ℓ - 1}) A → Continuous ψ → HasCompactSupport ψ →
      Integrable (fun y => sheetSum (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x s =>
          |ψ (Real.log (h.dualNorm x)) *
            gradDens (fun _ : Fin e => (fun x => Real.log (h.dualNorm x)) ∘ s)
              ((fun x => Real.log (h.dualNorm x)) ∘ s) ((fun x => Real.log (h.dualNorm x)) ∘ s) y|) y) ∧
        (∫ y, sheetSum (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x s =>
          |ψ (Real.log (h.dualNorm x)) *
            gradDens (fun _ : Fin e => (fun x => Real.log (h.dualNorm x)) ∘ s)
              ((fun x => Real.log (h.dualNorm x)) ∘ s) ((fun x => Real.log (h.dualNorm x)) ∘ s) y|) y) ≤
          (∫ y, chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
              (fun _ x => Real.log (h.dualNorm x)) y) * ∫ r, |ψ r|

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLevelSetSmooth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

def SliceLevelSetSmooth.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)
    (ψ : ℝ → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) g → linForm ℓ ∉ W →
    IsFiniteProjection (W ⊔ Ideal.span {linForm ℓ - 1}) A → ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    (∀ r, 0 ≤ ψ r) →
      Integrable (fun y => sheetSum (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x s =>
          |ψ (Real.log (h.dualNorm x)) *
            gradDens (fun _ : Fin e => (fun x => Real.log (h.dualNorm x)) ∘ s)
              ((fun x => Real.log (h.dualNorm x)) ∘ s) ((fun x => Real.log (h.dualNorm x)) ∘ s) y|) y) ∧
        (∫ y, sheetSum (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x s =>
          |ψ (Real.log (h.dualNorm x)) *
            gradDens (fun _ : Fin e => (fun x => Real.log (h.dualNorm x)) ∘ s)
              ((fun x => Real.log (h.dualNorm x)) ∘ s) ((fun x => Real.log (h.dualNorm x)) ∘ s) y|) y) ≤
          (∫ y, chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
              (fun _ x => Real.log (h.dualNorm x)) y) * ∫ r, |ψ r|

def SliceLevelSetSmooth.bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

end

end GroundTheory.Heights₂.Heights
end

