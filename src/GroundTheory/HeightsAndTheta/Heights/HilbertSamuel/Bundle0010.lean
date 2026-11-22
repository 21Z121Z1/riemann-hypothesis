import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0009
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0005

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanNorms
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

theorem continuousOn_source_of_chart {E : Type*} [TopologicalSpace E] {f : X → E} (j : Fin A.n)
    (hf : ContinuousOn (f ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source)) :
    ContinuousOn f (A.chart j).source := by
  have h := hf.comp (A.chart j).continuousOn (fun y hy =>
    ⟨(A.chart j).map_source hy, by simpa [(A.chart j).left_inv hy] using hy⟩)
  exact h.congr (fun y hy => by simp [(A.chart j).left_inv hy])

theorem ptNormSq_eq_of_mem (W : Weight L) {n : ℕ} {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n)
    (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    ptNormSq W n s x = ‖s j x‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ j x) := by
  have hk : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have hkj : x ∈ (A.chart (chartIdx A x)).source ∩ (A.chart j).source := ⟨hk, hx⟩
  have hg : 0 < ‖L.g (chartIdx A x) j x‖ ^ 2 := by
    have := L.ne_zero _ _ x hkj
    positivity
  have he : Real.exp ((n : ℝ) * Real.log (‖L.g (chartIdx A x) j x‖ ^ 2)) =
      (‖L.g (chartIdx A x) j x‖ ^ 2) ^ n := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hg n)]
  rw [ptNormSq, hs.2.1 _ j x hkj, W.compat _ j x hkj, norm_mul, norm_pow,
    show -(n : ℝ) * (W.φ j x + Real.log (‖L.g (chartIdx A x) j x‖ ^ 2)) =
      -(n : ℝ) * W.φ j x - (n : ℝ) * Real.log (‖L.g (chartIdx A x) j x‖ ^ 2) by ring,
    Real.exp_sub, he]
  have hp : 0 < (‖L.g (chartIdx A x) j x‖ ^ 2) ^ n := pow_pos hg n
  field_simp
  ring

theorem ptNormSq_nonneg (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) :
    0 ≤ ptNormSq W n s x := by
  unfold ptNormSq; positivity

theorem continuous_ptNormSq (W : Weight L) {n : ℕ} {s : Fin A.n → X → ℂ}
    (hs : s ∈ L.sections n) : Continuous (ptNormSq W n s) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨j, hx⟩ := A.cover x
  have hsj : ContinuousOn (s j) (A.chart j).source :=
    continuousOn_source_of_chart j (hs.1 j j).continuousOn
  have hφj : ContinuousOn (W.φ j) (A.chart j).source :=
    continuousOn_source_of_chart j (W.smooth j j).continuousOn
  have hF : ContinuousOn (fun y => ‖s j y‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ j y))
      (A.chart j).source :=
    ((hsj.norm.pow 2).mul ((continuousOn_const.mul hφj).rexp))
  have hopen := (A.chart j).open_source
  refine (hF.continuousAt (hopen.mem_nhds hx)).congr ?_
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact (ptNormSq_eq_of_mem W hs j hy).symm

theorem ptNormSq_smul (W : Weight L) (n : ℕ) (c : ℂ) (s : Fin A.n → X → ℂ) (x : X) :
    ptNormSq W n (c • s) x = ‖c‖ ^ 2 * ptNormSq W n s x := by
  simp only [ptNormSq, Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

variable [MeasurableSpace X] [BorelSpace X]

theorem SmoothVolume.isOpenPosMeasure (dV : SmoothVolume A) : dV.μ.IsOpenPosMeasure := by
  refine ⟨fun U hU ⟨x, hxU⟩ hzero => ?_⟩
  obtain ⟨j, hx⟩ := A.cover x
  set O := (A.chart j).target ∩ (A.chart j).symm ⁻¹' U with hOdef
  have hO : IsOpen O := (A.chart j).isOpen_inter_preimage_symm hU
  have hxO : A.chart j x ∈ O :=
    ⟨(A.chart j).map_source hx, by simpa [(A.chart j).left_inv hx] using hxU⟩
  have hOt : O ⊆ (A.chart j).target := inter_subset_left
  have hmeas : Measurable (U.indicator (1 : X → ℝ≥0∞)) := measurable_one.indicator hU.measurableSet
  have h1 := dV.chart_lintegral j _ hmeas
  have hL : ∫⁻ y in (A.chart j).source, U.indicator (1 : X → ℝ≥0∞) y ∂dV.μ = 0 := by
    rw [lintegral_indicator_one hU.measurableSet, Measure.restrict_apply hU.measurableSet]
    exact measure_mono_null inter_subset_left hzero
  rw [hL] at h1
  have h2 : ∫⁻ y in O, ENNReal.ofReal (dV.dens j y) = 0 := by
    refine le_antisymm ?_ bot_le
    calc ∫⁻ y in O, ENNReal.ofReal (dV.dens j y)
        = ∫⁻ y in O, U.indicator (1 : X → ℝ≥0∞) ((A.chart j).symm y) *
            ENNReal.ofReal (dV.dens j y) := by
          refine setLIntegral_congr_fun hO.measurableSet fun y hy => ?_
          rw [Set.indicator_of_mem (show (A.chart j).symm y ∈ U from hy.2), Pi.one_apply, one_mul]
      _ ≤ ∫⁻ y in (A.chart j).target, U.indicator (1 : X → ℝ≥0∞) ((A.chart j).symm y) *
            ENNReal.ofReal (dV.dens j y) := lintegral_mono_set hOt
      _ = 0 := h1.symm
  have hae : AEMeasurable (fun y => ENNReal.ofReal (dV.dens j y)) (volume.restrict O) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((((dV.smooth j).continuousOn).mono hOt).aemeasurable hO.measurableSet)
  have h3 := (lintegral_eq_zero_iff' hae).1 h2
  rw [EventuallyEq, ae_restrict_iff' hO.measurableSet] at h3
  have h4 : volume O = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h3] with y hy hyO
    exact (ENNReal.ofReal_pos.2 (dV.pos j y (hOt hyO))).ne' (hy hyO)
  exact hO.measure_ne_zero volume ⟨_, hxO⟩ h4

theorem integrable_ptNormSq (W : Weight L) (dV : SmoothVolume A) [CompactSpace X] {n : ℕ}
    {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) : Integrable (ptNormSq W n s) dV.μ := by
  have := dV.isProb
  exact (continuous_ptNormSq W hs).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [BorelSpace X] in
theorem sectionL2NormSq_nonneg (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (s : Fin A.n → X → ℂ) :
    0 ≤ sectionL2NormSq W dV n s :=
  integral_nonneg fun x => ptNormSq_nonneg W n s x

omit [BorelSpace X] in

theorem sectionL2NormSq_smul (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (c : ℂ)
    (s : Fin A.n → X → ℂ) : sectionL2NormSq W dV n (c • s) = ‖c‖ ^ 2 * sectionL2NormSq W dV n s := by
  simp only [sectionL2NormSq, ptNormSq_smul]
  exact integral_const_mul _ _

theorem ptNormSq_eq_zero_of_l2NormSq_eq_zero (W : Weight L) (dV : SmoothVolume A) [CompactSpace X]
    {n : ℕ} {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) (h0 : sectionL2NormSq W dV n s = 0) (x : X) :
    ptNormSq W n s x = 0 := by
  have := dV.isOpenPosMeasure
  have hae := (integral_eq_zero_iff_of_nonneg (fun y => ptNormSq_nonneg W n s y)
    (integrable_ptNormSq W dV hs)).1 h0
  have := (Continuous.ae_eq_iff_eq (μ := dV.μ) (continuous_ptNormSq W hs) continuous_const).1 hae
  exact congrFun this x

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.HolLineBundleToAltTransition
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ComplexConjugate ENNReal ContDiff

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

namespace HolLineBundle

def toIndefiniteRowSideFullHecke (L : HolLineBundle A) : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A where
  g := L.g
  holo := L.holo
  ne_zero := L.ne_zero
  cocycle j k l x hx := (L.cocycle j k l x hx).symm

def split_model_to_place_model (L : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A) : HolLineBundle A where
  g := L.g
  holo := L.holo
  ne_zero := L.ne_zero
  cocycle j k l x hx := (L.cocycle j k l x hx).symm

def holLineBundleEquivAlt : HolLineBundle A ≃ IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A where
  toFun := toIndefiniteRowSideFullHecke
  invFun := split_model_to_place_model
  left_inv _ := rfl
  right_inv _ := rfl

theorem sections_eq_sectionSpace (L : HolLineBundle A) (n : ℕ) :
    L.sections n = IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.sectionSpace L.toIndefiniteRowSideFullHecke n := by
  ext f
  constructor
  · rintro ⟨a, b, c⟩
    exact ⟨a, c, b⟩
  · rintro ⟨a, b, c⟩
    exact ⟨a, c, b⟩

end HolLineBundle

namespace Weight

variable {L : HolLineBundle A}

theorem isWeight (W : Weight L) : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight L.toIndefiniteRowSideFullHecke W.φ :=
  ⟨W.smooth, W.compat⟩

def ofIsWeight {φ : Fin A.n → X → ℝ} (h : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight L.toIndefiniteRowSideFullHecke φ) :
    Weight L :=
  ⟨φ, h.1, h.2⟩

def split_model_to_place_model {L' : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.HolLineBundle A} {φ : Fin A.n → X → ℝ}
    (h : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight L' φ) : Weight (HolLineBundle.split_model_to_place_model L') :=
  ⟨φ, h.1, h.2⟩

def equivIsWeight : Weight L ≃ {φ : Fin A.n → X → ℝ // IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.IsWeight L.toIndefiniteRowSideFullHecke φ} where
  toFun W := ⟨W.φ, W.isWeight⟩
  invFun φ := ofIsWeight φ.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem lerp_φ (W₀ W₁ : Weight L) (t : ℝ) :
    (W₀.lerp W₁ t).φ = IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.interp W₀.φ W₁.φ t :=
  rfl

end Weight

theorem lintegral_map_chart [MeasurableSpace X] [BorelSpace X] (j : Fin A.n)
    {d : (Fin D → ℂ) → ℝ} (hd : ContinuousOn d (A.chart j).target) {g : X → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ x, g x ∂(((volume.restrict (A.chart j).target).withDensity
        fun y => ENNReal.ofReal (d y)).map (A.chart j).symm) =
      ∫⁻ y in (A.chart j).target, g ((A.chart j).symm y) * ENNReal.ofReal (d y) := by
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have hs : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
    (A.chart j).continuousOn_symm.aemeasurable hT
  have hf : AEMeasurable (fun y => ENNReal.ofReal (d y)) (volume.restrict (A.chart j).target) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hd.aemeasurable hT)
  rw [lintegral_map' hg.aemeasurable (hs.mono_ac (withDensity_absolutelyContinuous _ _)),
    lintegral_withDensity_eq_lintegral_mul₀ hf
      (show AEMeasurable (fun y => g ((A.chart j).symm y)) _ from hg.comp_aemeasurable hs)]
  refine lintegral_congr fun y => ?_
  simp only [Pi.mul_apply]
  exact mul_comm _ _

namespace SmoothVolume

variable [MeasurableSpace X] [BorelSpace X]

def toIndefiniteRowSideFullHecke (dV : SmoothVolume A) : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.SmoothVolume A where
  μ := dV.μ
  isProb := dV.isProb
  dens := dV.dens
  smooth := dV.smooth
  pos := dV.pos
  chart_eq j := Measure.ext_of_lintegral _ fun g hg => by
    rw [lintegral_map_chart j (dV.smooth j).continuousOn hg, dV.chart_lintegral j g hg]

def split_model_to_place_model (V : IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.SmoothVolume A) : SmoothVolume A where
  μ := V.μ
  isProb := V.isProb
  dens := V.dens
  smooth := V.smooth
  pos := V.pos
  chart_lintegral j g hg := by
    rw [← V.chart_eq j, lintegral_map_chart j (V.smooth j).continuousOn hg]

def holLineBundleEquivAlt : SmoothVolume A ≃ IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.SmoothVolume A where
  toFun := toIndefiniteRowSideFullHecke
  invFun := split_model_to_place_model
  left_inv _ := rfl
  right_inv _ := rfl

end SmoothVolume

variable {L : HolLineBundle A}

variable [MeasurableSpace X] [BorelSpace X]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexFormsOnPoints
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem ComplexFormsOnPoints.proof (hR : PrimeComplexRadical.Statement)
    (hM : ComplexMinimalPrimesContract.Statement) : ComplexFormsOnPoints.Statement := by
  intro K _ ι _ P hP hrel F hF
  have hrad := hR (Σ k, ι k) P hP
  apply hrad
  rw [← Ideal.sInf_minimalPrimes]
  refine Ideal.mem_sInf.2 fun {Q} hQ => ?_
  have hQp : Q.IsPrime := hQ.1.1
  have hc := hM (Σ k, ι k) P hP Q hQ
  choose i hi using hrel

  let h0 : MRing ι := ∏ k, X ⟨k, i k⟩
  have h0P : h0 ∉ P := by
    intro hmem
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP)).1 hmem
    exact hi k hk
  have hQh : map (Int.castRingHom ℂ) h0 ∉ Q := by
    intro hmem
    apply h0P
    rw [← hc]
    exact Ideal.mem_comap.2 hmem
  have hPQ : ∀ f ∈ P, map (Int.castRingHom ℂ) f ∈ Q := by
    intro f hf
    rw [← hc] at hf
    exact Ideal.mem_comap.1 hf
  have hv : F * map (Int.castRingHom ℂ) h0 ∈ vanishingIdeal ℂ (zeroLocus ℂ Q) := by
    rw [mem_vanishingIdeal_iff]
    intro z hz
    have hz : ∀ p ∈ Q, eval z p = 0 := hz
    change eval z _ = 0
    have hzh : eval z (map (Int.castRingHom ℂ) h0) = ∏ k, z ⟨k, i k⟩ := by
      simp [h0, map_prod]
    by_cases h0z : eval z (map (Int.castRingHom ℂ) h0) = 0
    · rw [map_mul, h0z, mul_zero]
    · have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := by
        rw [hzh] at h0z
        exact fun k => Finset.prod_ne_zero_iff.1 h0z k (Finset.mem_univ k)
      have hzP : z ∈ mcPts P := ⟨fun k => ⟨i k, hne k⟩, fun f hf => hz _ (hPQ f hf)⟩
      rw [map_mul, hF z hzP, zero_mul]
  rw [vanishingIdeal_zeroLocus_eq_radical, hQp.radical] at hv
  exact (hQp.mem_or_mem hv).resolve_right hQh

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolyLine
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Polynomial GroundTheory.Heights₂.Heights.NumbersDVR fwdDiff

noncomputable section

namespace EventualPolyLine

variable {K : Type}

def lineRestrict [Fintype K] (a c : K → ℚ) (p : MvPolynomial K ℚ) : ℚ[X] :=
  MvPolynomial.aeval (fun k => C (a k) * X + C (c k)) p

def topCoeff [Fintype K] (D : ℕ) (a : K → ℚ) (p : MvPolynomial K ℚ) : ℚ :=
  ∑ s ∈ p.support, p.coeff s * if ∑ k, s k = D then ∏ k, a k ^ s k else 0

theorem eval_lineRestrict [Fintype K] (a c : K → ℚ) (p : MvPolynomial K ℚ) (t : ℚ) :
    (lineRestrict a c p).eval t = MvPolynomial.eval (fun k => c k + t * a k) p := by
  unfold lineRestrict
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p k hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    ring

theorem prod_line_pow (a c : K → ℚ) (s : K → ℕ) (S : Finset K) :
    (∏ k ∈ S, (C (a k) * X + C (c k)) ^ (s k)).natDegree ≤ ∑ k ∈ S, s k ∧
      (∏ k ∈ S, (C (a k) * X + C (c k)) ^ (s k)).coeff (∑ k ∈ S, s k) = ∏ k ∈ S, a k ^ (s k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    have h1 : ((C (a k) * X + C (c k)) ^ (s k)).natDegree ≤ s k := by
      simpa using natDegree_pow_le_of_le (s k) (natDegree_linear_le (a := a k) (b := c k))
    have h2 : ((C (a k) * X + C (c k)) ^ (s k)).coeff (s k) = a k ^ s k := by
      have := coeff_pow_of_natDegree_le (m := s k) (natDegree_linear_le (a := a k) (b := c k))
      simpa using this
    rw [Finset.prod_insert hk, Finset.sum_insert hk, Finset.prod_insert hk]
    exact ⟨natDegree_mul_le.trans (add_le_add h1 ih.1),
      by rw [coeff_mul_add_eq_of_natDegree_le h1 ih.1, h2, ih.2]⟩

theorem lineRestrict_natDegree_coeff [Fintype K] (D : ℕ) (a c : K → ℚ) (p : MvPolynomial K ℚ)
    (hp : p.totalDegree ≤ D) :
    (lineRestrict a c p).natDegree ≤ D ∧ (lineRestrict a c p).coeff D = topCoeff D a p := by
  have hs : ∀ s ∈ p.support, ∑ k, s k ≤ D := fun s hs => by
    have := MvPolynomial.le_totalDegree hs
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    exact this.trans hp
  have hexp : lineRestrict a c p =
      ∑ s ∈ p.support, C (p.coeff s) * ∏ k, (C (a k) * X + C (c k)) ^ (s k) := by
    unfold lineRestrict
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    rfl
  rw [hexp]
  constructor
  · refine natDegree_sum_le_of_forall_le _ _ (fun s hs' => ?_)
    exact (natDegree_C_mul_le _ _).trans ((prod_line_pow a c s Finset.univ).1.trans (hs s hs'))
  · rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl (fun s hs' => ?_)
    rw [Polynomial.coeff_C_mul]
    congr 1
    split_ifs with hD
    · rw [← hD]
      exact (prod_line_pow a c s Finset.univ).2
    · exact coeff_eq_zero_of_natDegree_lt
        ((prod_line_pow a c s Finset.univ).1.trans_lt (lt_of_le_of_ne (hs s hs') hD))

theorem fwdDiff_iter_poly (D : ℕ) (P : ℚ[X]) (hP : P.natDegree ≤ D) :
    (fwdDiff (1 : ℚ))^[D] P.eval 0 = (D.factorial : ℚ) * P.coeff D := by
  rcases hP.lt_or_eq with h | h
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h, coeff_eq_zero_of_natDegree_lt h]
    simp
  · subst h
    rw [Polynomial.fwdDiff_iter_degree_eq_factorial]
    rw [Polynomial.coeff_natDegree]
    simp only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
    ring

theorem mixedDiff_const (D : ℕ) (a : K → ℤ) (f : (K → ℤ) → ℤ) :
    mixedDiff (fun _ : Fin D => a) f = (List.replicate D a).foldr diffStep f := by
  simp only [mixedDiff, List.ofFn_const]

theorem foldr_diffStep_replicate (a : K → ℤ) (f : (K → ℤ) → ℤ) (n : ℕ) (x : K → ℤ) :
    (List.replicate n a).foldr diffStep f x = (fwdDiff a)^[n] f (x - n • a) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have e1 : x - (n + 1) • a + a = x - n • a := by rw [succ_nsmul]; abel
    have e2 : x - a - n • a = x - (n + 1) • a := by rw [succ_nsmul]; abel
    rw [List.replicate_succ, List.foldr_cons, Function.iterate_succ_apply']
    show (List.replicate n a).foldr diffStep f x - (List.replicate n a).foldr diffStep f (x - a) = _
    rw [ih, ih, e2]
    show _ = (fwdDiff a)^[n] f (x - (n + 1) • a + a) - (fwdDiff a)^[n] f (x - (n + 1) • a)
    rw [e1]

end EventualPolyLine

open EventualPolyLine in

theorem EventualPolyLine.proof : EventualPolyLine.Statement := by
  intro K _ _ D f p a₀ a m hp hf
  obtain ⟨aQ, haQ⟩ : ∃ aQ : K → ℚ, aQ = fun k => (a k : ℚ) := ⟨_, rfl⟩
  have key : ∀ x : K → ℤ, (∀ k, (a₀ : ℤ) + D * |a k| ≤ x k) →
      ((mixedDiff (fun _ : Fin D => a) f x : ℤ) : ℚ) = (D.factorial : ℚ) * topCoeff D aQ p := by
    intro x hx
    obtain ⟨c, hc⟩ : ∃ c : K → ℚ, c = fun k => (((x - D • a) k : ℤ) : ℚ) := ⟨_, rfl⟩
    obtain ⟨hdeg, hcoeff⟩ := lineRestrict_natDegree_coeff D aQ c p hp
    rw [mixedDiff_const, foldr_diffStep_replicate, fwdDiff_iter_eq_sum_shift, ← hcoeff,
      ← fwdDiff_iter_poly D _ hdeg, fwdDiff_iter_eq_sum_shift, Int.cast_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjD : j ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hnn : ∀ k, (a₀ : ℤ) ≤ (x - D • a + j • a) k := by
      intro k
      have h1 := hx k
      have hj' : (j : ℤ) ≤ D := by exact_mod_cast hjD
      have hj0 : (0 : ℤ) ≤ j := by positivity
      simp only [Pi.add_apply, Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
      rcases abs_cases (a k) with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> nlinarith
    have hge : ∀ k, a₀ ≤ ((x - D • a + j • a) k).toNat := fun k => by have := hnn k; omega
    have hy : (fun k => ((((x - D • a + j • a) k).toNat : ℕ) : ℤ)) = x - D • a + j • a :=
      funext fun k => Int.toNat_of_nonneg (by have := hnn k; omega)
    have hfy : f (x - D • a + j • a) = f (fun k => ((((x - D • a + j • a) k).toNat : ℕ) : ℤ)) := by
      rw [hy]
    rw [smul_eq_mul, zsmul_eq_mul, Int.cast_mul, hfy, hf _ hge, eval_lineRestrict]
    congr 2
    congr 1
    funext k
    have e2 : ((((x - D • a + j • a) k).toNat : ℕ) : ℚ) = (((x - D • a + j • a) k : ℤ) : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by have := hnn k; omega)]
    rw [e2, hc, haQ]
    simp only [Pi.add_apply, Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, zero_add, mul_one]
    push_cast
    ring
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, mixedDiff (fun _ : Fin D => a) f (fun k => (a₀ : ℤ) + D * |a k|) = c₀ :=
    ⟨_, rfl⟩
  have h₀ := key (fun k => (a₀ : ℤ) + D * |a k|) (fun k => le_rfl)
  rw [hc₀] at h₀
  have hev : ∀ᶠ x in Filter.atTop, mixedDiff (fun _ : Fin D => a) f x = c₀ := by
    refine Filter.eventually_atTop.2 ⟨fun k => (a₀ : ℤ) + D * |a k|, fun x hx => ?_⟩
    have h1 := key x (fun k => hx k)
    exact_mod_cast h1.trans h₀.symm
  have hEV := (EventualValueFacts.proof K _ c₀ 0).1 hev
  obtain ⟨hdeg, hcoeff⟩ := lineRestrict_natDegree_coeff D aQ (fun k => (m k : ℚ)) p hp
  refine ⟨(lineRestrict aQ (fun k => (m k : ℚ)) p).map (algebraMap ℚ ℝ), natDegree_map_le.trans hdeg, ?_, ?_⟩
  · have hD : (D.factorial : ℝ) ≠ 0 := by positivity
    rw [Polynomial.coeff_map, hcoeff, hEV, eq_ratCast, eq_div_iff hD,
      show ((c₀ : ℤ) : ℝ) = (((c₀ : ℤ) : ℚ) : ℝ) by norm_cast, h₀]
    push_cast
    ring
  · intro n
    rw [Polynomial.eval_natCast_map, eval_lineRestrict, eq_ratCast]
    congr 2
    congr 1
    funext k
    rw [haQ]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

