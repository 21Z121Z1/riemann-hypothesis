import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0109
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0124
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0126
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0121
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0106
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0107
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0077
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0102
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0084
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0127
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0117
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceRegMassLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace SliceRegMassLimit

theorem chartDens_one_sub {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin k) (Fin n) ℂ}
    (hfin : ∀ y, (fibre J A y).Finite) (f : (Fin n → ℂ) → ℝ) (φ : Fin k → (Fin n → ℂ) → ℝ) :
    chartDens J A (fun x => 1 - f x) φ = chartDens J A (fun _ => 1) φ - chartDens J A f φ := by
  funext y
  simp only [chartDens, sheetSum, Pi.sub_apply]
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
    finsum_mem_eq_finite_toFinset_sum _ (hfin y), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

theorem varInt_one_sub (hCM : ChartMassCompact.Statement) {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {φ : Fin k → (Fin n → ℂ) → ℝ} {f : (Fin n → ℂ) → ℝ} (hJ : J.IsPrime)
    (hφ : ∀ i, SmoothNear (zeroSet J) (φ i)) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (h1 : ∀ A, IsFiniteProjection J A → Integrable (chartAbsDens J A (fun _ => 1) φ)) :
    varInt J k (fun x => 1 - f x) φ = varInt J k (fun _ => 1) φ - varInt J k f φ := by
  unfold varInt
  split_ifs with h
  · set A := h.choose
    have hA : IsFiniteProjection J A := h.choose_spec
    have hd := VarIntAdd.ringKrullDim_of_isFiniteProjection hA
    have hfin : ∀ y, (fibre J A y).Finite := fun y => (FibreBound.proof n k J A hJ hd hA y).2.1
    have hint : ∀ w : (Fin n → ℂ) → ℝ, Measurable w → Integrable (chartAbsDens J A w φ) →
        Integrable (chartDens J A w φ) := by
      intro w hw habs
      refine habs.mono' (SheetSumMeasurable.proof n k J A w φ hJ hd hA hw hφ).1.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs]
      exact VarIntAdd.abs_chartDens_le hfin w φ y
    unfold chartInt
    rw [chartDens_one_sub hfin]
    simp only [Pi.sub_apply]
    rw [integral_sub (hint _ measurable_const (h1 A hA))
      (hint f hf.continuous.measurable
        (hCM n k J A f φ hJ hd hA hf.continuous.continuousOn hφ (Or.inl hfc)))]
  · simp

theorem varInt_one_fsLogReg (hC : SliceCutOffLimit.Statement) (hS : StokesOnVariety.Statement) {n e : ℕ}
    (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ)
    (u' ℓ : Fin n → ℂ) {ε : ℝ} (hW : IsProjPrime W) (hF : IsChowForm W (e + 2) F) (hℓ : linForm ℓ ∉ W)
    (hε : 0 < ε) :
    varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun _ => 1)
      (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) = 0 := by
  obtain ⟨hJ, hdim, -⟩ := SliceIdeal.proof n (e + 1) W F ℓ hW hF hℓ
  have hnear : ∀ G : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ G {x | x ≠ 0} →
      SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) G := fun G hG =>
    ⟨{x | x ≠ 0}, isOpen_ne, fun x hx => ne_zero_of_mem_zeroSet_slice hx, hG⟩
  obtain ⟨χ, hχs, hχc, hlim⟩ := hC n e h W F ℓ hW hF hℓ
  obtain ⟨h1, h2⟩ := hlim (fun _ => 1) (fsLogReg h u' ε) (fun _ _ _ => rfl) (fsLogReg_smul h u' ε)
    contDiffOn_const (contDiffOn_fsLogReg h u' hε)
  have hma : ∀ (s : (Fin (e + 1) → ℂ) → Fin n → ℂ) (y : Fin (e + 1) → ℂ),
      ReciprocityTheory.AnForm.maDens (fun k => (vecCons (fun _ => (1 : ℝ)) fun _ x => Real.log (h.dualNorm x)) k ∘ s)
        y = 0 := by
    intro s y
    have hH : ReciprocityTheory.AnForm.hessC ((fun _ => (1 : ℝ)) ∘ s) y = 0 := by
      ext i j
      simp [ReciprocityTheory.AnForm.hessC, Function.comp_def]
    unfold ReciprocityTheory.AnForm.maDens
    rw [LelongRegularise.mdisc_eq_zero_of_eq_zero _ (by simpa using hH)]
    simp
  have h0 : varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fsLogReg h u' ε)
      (vecCons (fun _ => 1) fun _ x => Real.log (h.dualNorm x)) = 0 := by
    simp [varInt, chartInt, chartDens, sheetSum, hma]
  refine (tendsto_nhds_unique h1 (h2.congr fun k => ?_)).trans h0
  exact (hS n e _ (fun x => χ k x * 1) (fsLogReg h u' ε) (fun _ x => Real.log (h.dualNorm x)) hJ hdim
    (hnear _ ((hχs k).contDiffOn.mul contDiffOn_const)) (hnear _ (contDiffOn_fsLogReg h u' hε))
    (fun _ => hnear _ h.contDiffOn_log_dualNorm) (Or.inl (hχc k).mul_right)).symm

end SliceRegMassLimit

theorem SliceRegMassLimit.proof (hC : SliceCutOffLimit.Statement) (hS : StokesOnVariety.Statement)
    (hLC : SliceFormLelongCompact.Statement) (hSec : SliceSectionMass.Statement) (hM : SliceFormMass.Statement)
    (hCM : ChartMassCompact.Statement) : SliceRegMassLimit.Statement := by
  intro n e h W F u' ℓ f hW hF hu hℓ hℓP hf hfc
  obtain ⟨hJ, -, -⟩ := SliceIdeal.proof n (e + 1) W F ℓ hW hF hℓ
  obtain ⟨-, himg, -⟩ := SliceComponents.proof n W u' ℓ hW hℓP
  have hω := smoothNear_log_dualNorm_slice h W ℓ
  have hlinG : ∀ ε : ℝ, 0 < ε → varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => 1 - f x)
      (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) =
      varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun _ => 1)
        (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) -
      varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) f
        (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x)) := by
    intro ε hε
    refine SliceRegMassLimit.varInt_one_sub hCM hJ (fun i => Fin.cases ?_ (fun _ => hω) i) hf hfc
      fun A hA => ?_
    · have := hM n e h W F ℓ A (fun _ => 1) (Fin.cons 0 fun _ => 1) (Fin.cons (fsLogReg h u' ε) fun _ _ => 0)
        hW hF hℓ hA (fun _ _ _ => rfl) continuousOn_const
        (fun k => Fin.cases (fsLogReg_smul h u' ε) (fun _ _ _ _ => rfl) k)
        (fun k => Fin.cases (contDiffOn_fsLogReg h u' hε) (fun _ => contDiffOn_const) k)
      convert this using 2
      funext k x
      refine Fin.cases ?_ (fun i => ?_) k <;> simp
    · exact ⟨{x | x ≠ 0}, isOpen_ne, fun x hx => ne_zero_of_mem_zeroSet_slice hx, contDiffOn_fsLogReg h u' hε⟩
  have hlinω : varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => 1 - f x)
      (fun _ x => Real.log (h.dualNorm x)) =
      varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun _ => 1) (fun _ x => Real.log (h.dualNorm x)) -
      varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) f (fun _ x => Real.log (h.dualNorm x)) := by
    refine SliceRegMassLimit.varInt_one_sub hCM hJ (fun _ => hω) hf hfc fun A hA => ?_
    have := hM n e h W F ℓ A (fun _ => 1) (fun _ => 1) (fun _ _ => 0) hW hF hℓ hA (fun _ _ _ => rfl)
      continuousOn_const (fun _ _ _ _ => rfl) (fun _ => contDiffOn_const)
    convert this using 2
    funext k x
    simp
  have hlinP : ∀ P ∈ (divCycle W u').support, varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e (fun x => 1 - f x)
      (fun _ x => Real.log (h.dualNorm x)) =
      varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e (fun _ => 1) (fun _ x => Real.log (h.dualNorm x)) -
      varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e f (fun _ x => Real.log (h.dualNorm x)) := by
    intro P hP
    have hmin : P ⊔ Ideal.span {linForm ℓ - 1} ∈
        (W ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u'}).minimalPrimes :=
      himg ▸ Set.mem_image_of_mem _ (Finset.mem_coe.mpr hP)
    have hPp : (P ⊔ Ideal.span {linForm ℓ - 1}).IsPrime := hmin.1.1
    refine SliceRegMassLimit.varInt_one_sub hCM hPp (fun _ => smoothNear_log_dualNorm_slice h P ℓ) hf hfc
      fun A hA => ?_
    exact SliceMassFinite.proof hM n e h _ ℓ A hPp (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      (VarIntAdd.ringKrullDim_of_isFiniteProjection hA) hA
  have hL := hLC n e h W F u' ℓ f hW hF hu hℓ hℓP (smoothNear_of_contDiff hf) hfc
  have hSM := hSec n e h W F u' ℓ hW hF hu hℓ hℓP
  have key := hL.neg.add_const (varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun _ => 1)
      (fun _ x => Real.log (h.dualNorm x)) -
    varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) f (fun _ x => Real.log (h.dualNorm x)))
  convert key.congr' ?_ using 2
  · rw [hSM, Finset.sum_congr rfl fun P hP => by rw [hlinP P hP]]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
    rw [hlinG ε hε, hlinω, SliceRegMassLimit.varInt_one_fsLogReg hC hS h W F u' ℓ hW hF hℓ hε]
    ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUniformiserGradientIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem UniformiserGradientIndependent.proof (hjac : NormalCurveJacobian.Statement)
    (hdvr : NormalCurvePointDVR.Statement) : UniformiserGradientIndependent.Statement := by
  intro σ _ I w t hI hic hdim hw ht
  obtain ⟨k, f, -, hk, hfI, hli, -, -⟩ := hjac σ I w hI hic hdim hw
  obtain ⟨_, _⟩ := hdvr σ I w hI hic hdim hw
  refine ⟨k, f, hk, hfI, hli.finCons fun hmem ↦ ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  set φ := algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) with hφ
  have hfw : ∀ j, eval w (f j) = 0 := fun j ↦ hw (f j) (hfI j)
  have htw : eval w t = 0 := by
    by_contra h
    exact ht.not_isUnit (isUnit_algebraMap_pointLocalRing I w t h)
  set p := t - ∑ j, C (c j) * f j with hp
  have hpm : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) := by
    simp [hp, RingHom.mem_ker, htw, hfw]
  have hpg : GradientAtPoint.grad w p = 0 := by
    rw [hp, map_sub, map_sum]
    simp_rw [GradientAtPoint.grad_mul_of_eval_eq_zero w _ _ (hfw _), eval_C]
    have hg : ∀ q, GradientAtPoint.grad w q = fun i ↦ eval w (pderiv i q) :=
      fun q ↦ funext (GradientAtPoint.grad_apply w q)
    simp_rw [hg]
    exact sub_eq_zero.2 hc.symm
  have hp2 := GradientAtPoint.mem_sq_of_grad_eq_zero w hpm hpg
  have hφf : ∀ j, φ (f j) = 0 := fun j ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ (hfI j))
  have hφt : φ t = φ p := by simp [hp, hφf]
  have hmax : Ideal.map φ (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ≤
      IsLocalRing.maximalIdeal (pointLocalRing I w) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu ↦ pointLocalRing_eval_ne_zero_of_isUnit I w hw g hu (RingHom.mem_ker.1 hg)
  have ht2 : φ t ∈ IsLocalRing.maximalIdeal (pointLocalRing I w) ^ 2 := by
    rw [hφt]
    exact Ideal.pow_right_mono hmax 2 (Ideal.map_pow φ _ 2 ▸ Ideal.mem_map_of_mem φ hp2)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 ht, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton'] at ht2
  obtain ⟨a, ha⟩ := ht2
  have h1 : φ t * (a * φ t) = φ t * 1 := by rw [mul_one]; nth_rewrite 3 [← ha]; ring
  exact ht.not_isUnit
    (IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact mul_left_cancel₀ ht.ne_zero h1))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUniformiserLocallyInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

theorem UniformiserLocallyInjective.proof (hgrad : UniformiserGradientIndependent.Statement)
    (hchart : PolynomialChartInjective.Statement) : UniformiserLocallyInjective.Statement := by
  intro σ _ I w t hI hic hdim hw ht
  obtain ⟨k, f, hk, hfI, hli⟩ := hgrad σ I w t hI hic hdim hw ht
  obtain ⟨U, hU, hinj⟩ := hchart σ k t f w hk hli
  refine ⟨U, hU, hinj.mono ?_⟩
  rintro z ⟨hz, hzU⟩
  exact ⟨hzU, fun j ↦ hz (f j) (hfI j)⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBoundaryBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceBoundaryBound.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)
    (F G : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) g → linForm ℓ ∉ W →
    IsFiniteProjection (W ⊔ Ideal.span {linForm ℓ - 1}) A →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → F (t • x) = F x) →
    (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → G (t • x) = G x) →
    ContDiffOn ℝ ∞ F {x | x ≠ 0} → ContDiffOn ℝ ∞ G {x | x ≠ 0} →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ χ : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
        |chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A G
              (vecCons (fun x => χ x * F x) fun _ x => Real.log (h.dualNorm x)) -
            chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => χ x * G x)
              (vecCons F fun _ x => Real.log (h.dualNorm x))| ≤
          C * ((∫ y, chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
                (vecCons χ fun _ x => Real.log (h.dualNorm x)) y) +
            Real.sqrt (chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
                (vecCons (fun x => χ x ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) -
              chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A χ
                (vecCons χ fun _ x => Real.log (h.dualNorm x))))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCutDecay
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceCutDecay.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 2) g → linForm ℓ ∉ W →
    IsFiniteProjection (W ⊔ Ideal.span {linForm ℓ - 1}) A →
      ∃ C : ℝ, ∀ k : ℕ,
        (∫ y, chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
            (vecCons (sliceCut h k) fun _ x => Real.log (h.dualNorm x)) y) ≤ C / ((k : ℝ) + 1) ∧
          chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
              (vecCons (fun x => sliceCut h k x ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) -
            chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A (sliceCut h k)
              (vecCons (sliceCut h k) fun _ x => Real.log (h.dualNorm x)) ≤ C / ((k : ℝ) + 1)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFsLogIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def SliceFsLogIntegrable.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm u ∉ J → linForm ℓ ∉ J →
    IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A →
      Integrable (chartAbsDens (J ⊔ Ideal.span {linForm ℓ - 1}) A (fsLog h u)
        (fun _ x => Real.log (h.dualNorm x)))

end

end GroundTheory.Heights₂.Heights
end

