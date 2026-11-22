import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.Measure
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.ConvergenceRate
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable ChartPartition integralWith
  locDens chartPartMeasure integral_chartPartMeasure isFiniteMeasure_chartPartMeasure existsPartition
  locDensCont mIntegrableCont)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

def convRate (D : ℕ) (C t : ℝ) : ℝ :=
  C * (Real.log (ell t) / ell t + Real.log (ell t) ^ (D + 1) / ell t)

theorem tendsto_ell : Tendsto ell (𝓝[>] 0) atTop :=
  Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero

theorem tendsto_convRate (D : ℕ) (C : ℝ) : Tendsto (convRate D C) (𝓝[>] 0) (𝓝 0) := by
  have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_ell
  have h2 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 (D + 1) one_ne_zero).comp tendsto_ell
  have h := (h1.add h2).const_mul C
  show Tendsto (fun t => C * (Real.log (ell t) / ell t + Real.log (ell t) ^ (D + 1) / ell t)) _ _
  simpa [Function.comp_def] using h

def ConvergenceRate.Statement : Prop :=
  ∀ (D : ℕ) (F : ℝ → ℝ) (C ℓ₀ : ℝ),
    (∀ t t', 0 < t' → t' ≤ t → ℓ₀ ≤ ell t → |F t - F t'| ≤ convRate D C t) →
    ∃ L : ℝ, Tendsto F (𝓝[>] 0) (𝓝 L) ∧
      ∀ t, 0 < t → ℓ₀ ≤ ell t → |F t - L| ≤ convRate D C t

theorem ConvergenceRate.proof : ConvergenceRate.Statement := by
  intro D F C ℓ₀ hF
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ℓ₀ ≤ ell t := tendsto_ell.eventually_ge_atTop ℓ₀
  have hc : Cauchy (map F (𝓝[>] (0 : ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    have hr : ∀ᶠ t in 𝓝[>] (0 : ℝ), convRate D C t < ε :=
      (tendsto_convRate D C).eventually (gt_mem_nhds hε)
    obtain ⟨δ, hδ, hδs⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 (hev.and hr)
    refine ⟨F '' Ioo 0 δ, mem_map.2 (mem_of_superset (Ioo_mem_nhdsGT hδ)
      (subset_preimage_image _ _)), ?_⟩
    rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩
    rw [Real.dist_eq]
    rcases le_total t' t with h | h
    · exact (hF t t' ht'.1 h (hδs ht).1).trans_lt (hδs ht).2
    · rw [abs_sub_comm]
      exact (hF t' t ht.1 h (hδs ht').1).trans_lt (hδs ht').2
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.1 hc
  refine ⟨L, hL, fun t ht hℓ => ?_⟩
  have hlim : Tendsto (fun t' => |F t - F t'|) (𝓝[>] 0) (𝓝 |F t - L|) :=
    (continuous_abs.tendsto _).comp (tendsto_const_nhds.sub hL)
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT ht] with t' ht'
  exact hF t t' ht'.1 ht'.2.le hℓ

section Signed

variable {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

def tvMeasure (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) : Measure X :=
  ∑ j, (chartPartMeasure A (existsPartition A).some Φ 1 j +
    chartPartMeasure A (existsPartition A).some Φ (-1) j)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
theorem chart_weight_continuousOn (A : FinHolAtlas D X) (P : ChartPartition A)
    (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) :
    ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target := by
  have h := (P.smooth j j).continuousOn
  rw [Set.preimage_univ, Set.inter_univ] at h
  exact continuousOn_const.mul (h.mul (locDensCont A Φ hΦ j))

omit [CompactSpace X] [T2Space X] in

theorem integrableOn_chart_of_part (A : FinHolAtlas D X) (P : ChartPartition A)
    (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) (g : X → ℝ)
    (hg : Measurable g) (hi : Integrable g (chartPartMeasure A P Φ s j)) :
    IntegrableOn (fun y => g ((A.chart j).symm y) *
      max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0) (A.chart j).target := by
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have hwc := chart_weight_continuousOn A P Φ hΦ s j
  have hsymm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
    (A.chart j).continuousOn_symm.aemeasurable hT
  have hd : AEMeasurable (fun y => ENNReal.ofReal
      (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) (volume.restrict (A.chart j).target) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hwc.aemeasurable hT)
  have hlt : ∀ᵐ y ∂(volume.restrict (A.chart j).target), ENNReal.ofReal
      (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hsymm' : AEMeasurable (A.chart j).symm ((volume.restrict (A.chart j).target).withDensity
      fun y => ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hfun : (fun y => (ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) *
      locDens A Φ j y))).toReal • (g ∘ (A.chart j).symm) y) = fun y => g ((A.chart j).symm y) *
        max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0 := by
    funext y
    rw [ENNReal.toReal_ofReal', smul_eq_mul, Function.comp_apply, mul_comm]
  unfold chartPartMeasure at hi
  rw [integrable_map_measure hg.aestronglyMeasurable hsymm',
    integrable_withDensity_iff_integrable_smul₀' hd hlt, hfun] at hi
  exact hi

theorem isFiniteMeasure_tvMeasure (A : FinHolAtlas D X) (Φ : Fin D → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) : IsFiniteMeasure (tvMeasure A Φ) := by
  refine ⟨?_⟩
  rw [tvMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  refine ENNReal.sum_lt_top.2 fun j _ => ?_
  have := isFiniteMeasure_chartPartMeasure A (existsPartition A).some Φ hΦ 1 j
  have := isFiniteMeasure_chartPartMeasure A (existsPartition A).some Φ hΦ (-1) j
  rw [Measure.add_apply]
  exact ENNReal.add_lt_top.2 ⟨measure_lt_top _ _, measure_lt_top _ _⟩

theorem abs_mInt_le (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (f : X → ℝ) (hf : Measurable f) (hfi : MIntegrable A Φ f) :
    Integrable f (tvMeasure A Φ) ∧ |mInt A Φ f| ≤ ∫ x, |f x| ∂tvMeasure A Φ := by
  have h1 := fun j => integral_chartPartMeasure A (existsPartition A).some Φ hΦ 1 j f hf hfi
  have h2 := fun j => integral_chartPartMeasure A (existsPartition A).some Φ hΦ (-1) j f hf hfi
  have hI : ∀ j, Integrable f (chartPartMeasure A (existsPartition A).some Φ 1 j +
      chartPartMeasure A (existsPartition A).some Φ (-1) j) :=
    fun j => (h1 j).1.add_measure (h2 j).1
  have hm : mInt A Φ f = ∑ j, (∫ x, f x ∂chartPartMeasure A (existsPartition A).some Φ 1 j -
      ∫ x, f x ∂chartPartMeasure A (existsPartition A).some Φ (-1) j) := by
    rw [mInt, dif_pos (existsPartition A)]
    unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(h1 j).2, (h2 j).2, ← integral_sub
      (integrableOn_chart_of_part A _ Φ hΦ 1 j f hf (h1 j).1)
      (integrableOn_chart_of_part A _ Φ hΦ (-1) j f hf (h2 j).1)]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    dsimp only
    rw [one_mul, neg_one_mul, ← mul_sub, max_zero_sub_max_neg_zero_eq_self]
    ring
  refine ⟨integrable_finsetSum_measure.2 fun j _ => hI j, ?_⟩
  rw [hm, tvMeasure, integral_finsetSum_measure fun j _ => (hI j).abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [integral_add_measure (h1 j).1.abs (h2 j).1.abs]
  exact (abs_sub _ _).trans (add_le_add abs_integral_le_integral_abs abs_integral_le_integral_abs)

structure TVBounds (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) (Yo : Set X) (r : X → ℝ)
    (M CE : ℝ) : Prop where
  null : tvMeasure A Φ Yoᶜ = 0
  mass : (tvMeasure A Φ Yo).toReal ≤ M
  tailInt : ∀ R₀ : ℝ, Real.exp 1 ≤ R₀ →
    Integrable ((tail Yo r R₀).indicator fun x => Real.log (r x)) (tvMeasure A Φ)
  tailLog : ∀ R₀ : ℝ, Real.exp 1 ≤ R₀ →
    ∫ x, (tail Yo r R₀).indicator (fun x => Real.log (r x)) x ∂tvMeasure A Φ ≤
      CE * Real.log R₀ ^ (D + 1) / R₀

end Signed

def ConvergenceSigned.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (Φ : Fin D → LocPot X), (∀ i, IsPotential A (Φ i)) →
    ∀ (Yo : Set X) (r : X → ℝ) (M CE : ℝ), TVBounds A Φ Yo r M CE →
    ∀ f : X → ℝ, Measurable f → MIntegrable A Φ f →
    ∀ a K ℓ : ℝ, 0 ≤ a → 0 ≤ K → Real.exp 1 ≤ ℓ →
      (∀ x ∈ Yo, r x ≤ ℓ → |f x| ≤ a) → (∀ x ∈ Yo, ℓ < r x → |f x| ≤ K * Real.log (r x)) →
      |mInt A Φ f| ≤ a * M + K * (CE * Real.log ℓ ^ (D + 1) / ℓ)

theorem ConvergenceSigned.proof : ConvergenceSigned.Statement := by
  intro D X _ _ _ _ _ A Φ hΦ Yo r M CE hB f hf hfi a K ℓ ha hK hℓ hnear hfar
  have := isFiniteMeasure_tvMeasure A Φ hΦ
  obtain ⟨hfI, habs⟩ := abs_mInt_le A Φ hΦ f hf hfi
  set ind := (tail Yo r ℓ).indicator fun x => Real.log (r x) with hind
  have hindI : Integrable ind (tvMeasure A Φ) := hB.tailInt ℓ hℓ
  have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hind0 : ∀ x, 0 ≤ ind x := fun x => Set.indicator_nonneg
    (fun y hy => Real.log_nonneg (by linarith [hy.2])) x
  have hae : ∀ᵐ x ∂tvMeasure A Φ, x ∈ Yo := mem_ae_iff.2 hB.null
  have hpt : ∀ᵐ x ∂tvMeasure A Φ, |f x| ≤ a + K * ind x := by
    filter_upwards [hae] with x hx
    by_cases hr : r x ≤ ℓ
    · have := hnear x hx hr
      have := mul_nonneg hK (hind0 x)
      linarith
    · replace hr := not_le.1 hr
      have hxt : x ∈ tail Yo r ℓ := ⟨hx, hr.le⟩
      rw [hind, Set.indicator_of_mem hxt]
      have := hfar x hx hr
      linarith
  have hint : ∫ x, |f x| ∂tvMeasure A Φ ≤ ∫ x, (a + K * ind x) ∂tvMeasure A Φ :=
    integral_mono_ae hfI.abs ((integrable_const a).add (hindI.const_mul K)) hpt
  rw [integral_add (integrable_const a) (hindI.const_mul K), integral_const, integral_const_mul,
    smul_eq_mul] at hint
  have hmass : (tvMeasure A Φ).real univ ≤ M := by
    rw [Measure.real, ← measure_congr (ae_eq_univ.2 hB.null)]
    exact hB.mass
  have e1 : (tvMeasure A Φ).real univ * a ≤ M * a := mul_le_mul_of_nonneg_right hmass ha
  have e2 : K * ∫ x, ind x ∂tvMeasure A Φ ≤ K * (CE * Real.log ℓ ^ (D + 1) / ℓ) :=
    mul_le_mul_of_nonneg_left (hB.tailLog ℓ hℓ) hK
  linarith

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential)

@[instance_reducible] def projectiveLineBorel : MeasurableSpace (OnePoint ℂ) := borel _

attribute [local instance] projectiveLineBorel

theorem projectiveLine_borelSpace : BorelSpace (OnePoint ℂ) := ⟨rfl⟩

attribute [local instance] projectiveLine_borelSpace

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergySum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open scoped ContDiff ComplexOrder
open ReciprocityTheory.AnForm (hessC maDens mdisc levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt ChartPartition locDens integralWith)

noncomputable section

open scoped Classical in

def tvInt {D : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas D X) (Φ : Fin D → LocPot X)
    (g : X → ℝ) : ℝ :=
  if h : Nonempty (ChartPartition A) then
    ∑ j, ∫ y in (A.chart j).target,
      h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * |locDens A Φ j y|
  else 0

def EnergySum.Statement : Prop :=
  ∀ (D : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas D X) (Yo : Set X) (m : ℕ)
    (P : Fin m → LocPot X) (a : Fin D → Fin m → ℝ) (V : ℝ),
    (∀ i, IsPotential A (P i)) → (∀ i, FormNonneg A Yo (P i)) →
    (∀ σ : Fin D → Fin m,
      (∀ (Q : ChartPartition A) (j : Fin A.n), IntegrableOn (fun y =>
          Q.χ j ((A.chart j).symm y) * Yo.indicator 1 ((A.chart j).symm y) *
            locDens A (fun k => P (σ k)) j y) (A.chart j).target) ∧
      mInt A (fun k => P (σ k)) (Yo.indicator 1) ≤ V) →
    tvInt A (fun k => lincomb m (a k) P) (Yo.indicator 1) ≤ (∏ k, ∑ i, |a k i|) * V

section Proof

variable {D : ℕ}

theorem norm_mdisc_sum_le {m : ℕ} (a : Fin D → Fin m → ℝ)
    (B : Fin D → Fin m → Matrix (Fin D) (Fin D) ℂ) (hB : ∀ k i, (B k i).PosSemidef) :
    ‖mdisc (fun k => ∑ i, (a k i : ℂ) • B k i)‖ ≤
      ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * (mdisc fun k => B k (σ k)).re := by
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)
  rw [← hM, MultilinearMap.map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  rw [MultilinearMap.map_smul_univ, norm_smul, hM, norm_prod]
  obtain ⟨him, hre⟩ := ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef _ fun k => hB k (σ k)
  have hz : mdisc (fun k => B k (σ k)) = ((mdisc fun k => B k (σ k)).re : ℂ) :=
    Complex.ext (by simp) (by simp [him])
  rw [hz, Complex.norm_of_nonneg hre]
  simp [Complex.norm_real]

theorem hessC_finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → (Fin D → ℂ) → ℝ)
    (z : Fin D → ℂ) (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) z) :
    hessC (fun w => ∑ i ∈ s, c i * f i w) z = ∑ i ∈ s, (c i : ℂ) • hessC (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := ReciprocityTheory.AnForm.M.hessC_const_mul' (D := D) 0 (fun _ => (0 : ℝ)) z
    simpa using h
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    rw [ReciprocityTheory.AnForm.M.hessC_add' _ _ z (contDiffAt_const.mul (hf i (Finset.mem_insert_self _ _)))
      (ContDiffAt.sum fun i' hi' => contDiffAt_const.mul (hf i' (Finset.mem_insert_of_mem hi'))),
      ReciprocityTheory.AnForm.M.hessC_const_mul', ih fun i' hi' => hf i' (Finset.mem_insert_of_mem hi')]

variable {X : Type*} [TopologicalSpace X]

theorem abs_locDens_lincomb_le (A : FinHolAtlas D X) (Yo : Set X) {m : ℕ} (P : Fin m → LocPot X)
    (a : Fin D → Fin m → ℝ) (hpot : ∀ i, IsPotential A (P i)) (hnn : ∀ i, FormNonneg A Yo (P i))
    (j : Fin A.n) (y : Fin D → ℂ) (hy : y ∈ (A.chart j).target) (hY : (A.chart j).symm y ∈ Yo) :
    |locDens A (fun k => lincomb m (a k) P) j y| ≤
      ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * locDens A (fun k => P (σ k)) j y := by
  have hmem : ∀ i, (A.chart j).symm y ∈ (P i).U ((A.chart j).symm y) := fun i => (P i).mem_U _
  let f : Fin m → (Fin D → ℂ) → ℝ := fun i y' => (P i).φ ((A.chart j).symm y) ((A.chart j).symm y')
  have hC : ∀ i, ContDiffAt ℝ 2 (f i) y := fun i =>
    (((hpot i).1 _ j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm
      ((P i).isOpen_U _)).mem_nhds ⟨hy, hmem i⟩)).of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top)
  have hP : ∀ i, (hessC (f i) y).PosSemidef := fun i =>
    ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hC i) fun w => hnn i _ j y ⟨hy, hY, hmem i⟩ w
  have hS : ∀ k, hessC (fun y' => (lincomb m (a k) P).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      ∑ i, (a k i : ℂ) • hessC (f i) y := fun k => by
    simp_rw [lincomb_φ]
    exact hessC_finset_sum _ _ f y fun i _ => hC i
  have hc : (0 : ℝ) ≤ (D.factorial : ℝ) * (2 / Real.pi) ^ D :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg zero_le_two Real.pi_pos.le) _)
  have hL : locDens A (fun k => lincomb m (a k) P) j y =
      (D.factorial : ℝ) * (2 / Real.pi) ^ D * (mdisc fun k => ∑ i, (a k i : ℂ) • hessC (f i) y).re := by
    simp only [locDens, maDens, hS]
  have hR : ∀ σ : Fin D → Fin m, locDens A (fun k => P (σ k)) j y =
      (D.factorial : ℝ) * (2 / Real.pi) ^ D * (mdisc fun k => hessC (f (σ k)) y).re := fun σ => rfl
  rw [hL, abs_mul, abs_of_nonneg hc]
  calc (D.factorial : ℝ) * (2 / Real.pi) ^ D *
        |(mdisc fun k => ∑ i, (a k i : ℂ) • hessC (f i) y).re|
      ≤ (D.factorial : ℝ) * (2 / Real.pi) ^ D *
          ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * (mdisc fun k => hessC (f (σ k)) y).re :=
        mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans
          (norm_mdisc_sum_le a (fun k i => hessC (f i) y) fun _ i => hP i)) hc
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [hR]
        ring

theorem tvInt_lincomb_le (A : FinHolAtlas D X) (Yo : Set X) {m : ℕ} (P : Fin m → LocPot X)
    (a : Fin D → Fin m → ℝ) (hpot : ∀ i, IsPotential A (P i)) (hnn : ∀ i, FormNonneg A Yo (P i))
    (hint : ∀ (σ : Fin D → Fin m) (Q : ChartPartition A) (j : Fin A.n), IntegrableOn (fun y =>
      Q.χ j ((A.chart j).symm y) * Yo.indicator 1 ((A.chart j).symm y) *
        locDens A (fun k => P (σ k)) j y) (A.chart j).target) :
    tvInt A (fun k => lincomb m (a k) P) (Yo.indicator 1) ≤
      ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * mInt A (fun k => P (σ k)) (Yo.indicator 1) := by
  unfold tvInt mInt
  split_ifs with h
  · simp only [integralWith]
    calc ∑ j, ∫ y in (A.chart j).target, h.some.χ j ((A.chart j).symm y) *
            Yo.indicator 1 ((A.chart j).symm y) * |locDens A (fun k => lincomb m (a k) P) j y|
        ≤ ∑ j, ∫ y in (A.chart j).target, ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) *
            (h.some.χ j ((A.chart j).symm y) * Yo.indicator 1 ((A.chart j).symm y) *
              locDens A (fun k => P (σ k)) j y) := by
          refine Finset.sum_le_sum fun j _ => integral_mono_of_nonneg ?_
            (integrable_finsetSum _ fun σ _ => (hint σ h.some j).const_mul _) ?_
          · exact Filter.Eventually.of_forall fun y => mul_nonneg (mul_nonneg (h.some.nonneg j _)
              (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) (abs_nonneg _)
          · refine (ae_restrict_iff' (A.chart j).open_target.measurableSet).2
              (Filter.Eventually.of_forall fun y hy => ?_)
            by_cases hY : (A.chart j).symm y ∈ Yo
            · simp only [Set.indicator_of_mem hY, Pi.one_apply, mul_one]
              calc h.some.χ j ((A.chart j).symm y) * |locDens A (fun k => lincomb m (a k) P) j y|
                  ≤ h.some.χ j ((A.chart j).symm y) * ∑ σ : Fin D → Fin m,
                      (∏ k, |a k (σ k)|) * locDens A (fun k => P (σ k)) j y :=
                    mul_le_mul_of_nonneg_left
                      (abs_locDens_lincomb_le A Yo P a hpot hnn j y hy hY) (h.some.nonneg j _)
                _ = _ := by
                    rw [Finset.mul_sum]
                    exact Finset.sum_congr rfl fun σ _ => by ring
            · simp [hY]
      _ = ∑ j, ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * ∫ y in (A.chart j).target,
            h.some.χ j ((A.chart j).symm y) * Yo.indicator 1 ((A.chart j).symm y) *
              locDens A (fun k => P (σ k)) j y := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [integral_finsetSum _ fun σ _ => (hint σ h.some j).const_mul _]
          exact Finset.sum_congr rfl fun σ _ => integral_const_mul _ _
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun σ _ => (Finset.mul_sum _ _ _).symm
  · simp

theorem EnergySum.proof : EnergySum.Statement := by
  intro D X _ A Yo m P a V hpot hnn hσ
  refine (tvInt_lincomb_le A Yo P a hpot hnn fun σ => (hσ σ).1).trans ?_
  rw [Fintype.prod_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun σ _ =>
    mul_le_mul_of_nonneg_left (hσ σ).2 (Finset.prod_nonneg fun k _ => abs_nonneg _)

end Proof

section Inhabitant

open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential projLine_isPlurisubharmonic projectiveLine_fubiniStudy_mass_one p1i0 p1i1 projectiveLine_locDens_first_chart projectiveLine_locDens_second_chart)
open ReciprocityTheory.AnForm (fsDens integrable_fsDens)

end Inhabitant

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.IntegrableOnTargetOfMIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot ChartPartition mInt MIntegrable integralWith locDens)

variable {e : ℕ} {X : Type*} [TopologicalSpace X]

theorem chartPartition_le_one {A : FinHolAtlas e X} (P : ChartPartition A) (j : Fin A.n) (x : X) :
    P.χ j x ≤ 1 := by
  rw [← P.sum_eq_one x]
  exact Finset.single_le_sum (fun k _ => P.nonneg k x) (Finset.mem_univ j)

theorem integrableOn_target_of_mIntegrable [CompactSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (P : ChartPartition A) {g : X → ℝ} (hg : MIntegrable A Φ g)
    (j : Fin A.n) :
    IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y)
      (A.chart j).target := by
  have hsub := P.tsupport_subset j
  have hKc : IsCompact ((A.chart j) '' tsupport (P.χ j)) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn ((A.chart j).continuousOn.mono hsub)
  have hKt : (A.chart j) '' tsupport (P.χ j) ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (hsub hx)
  have hχc : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
    have h := (P.smooth j j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at h
    exact h
  have hKm : MeasurableSet ((A.chart j) '' tsupport (P.χ j)) := hKc.isClosed.measurableSet
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have h1 : IntegrableOn (fun y => P.χ j ((A.chart j).symm y) *
      (g ((A.chart j).symm y) * locDens A Φ j y)) ((A.chart j) '' tsupport (P.χ j)) :=
    Integrable.bdd_mul (c := 1) (hg j _ hKt hKc) ((hχc.mono hKt).aestronglyMeasurable hKm)
      ((ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun y _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (P.nonneg j _)]
        exact chartPartition_le_one P j _))
  refine (h1.of_forall_sdiff_eq_zero hT fun y hy => ?_).congr_fun (fun y _ => by ring) hT
  have : (A.chart j).symm y ∉ tsupport (P.χ j) := fun h => hy.2 ⟨_, h, (A.chart j).right_inv hy.1⟩
  rw [image_eq_zero_of_notMem_tsupport this, zero_mul]

theorem mInt_le_mul_of_le [CompactSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (V : Set X)
    {f g : X → ℝ} {c : ℝ} (hg : MIntegrable A Φ g)
    (hdens : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ V → 0 ≤ locDens A Φ j y)
    (hf0 : ∀ x, 0 ≤ f x) (hfV : ∀ x ∉ V, f x = 0) (hgV : ∀ x ∉ V, g x = 0)
    (hfg : ∀ x ∈ V, f x ≤ c * g x) : mInt A Φ f ≤ c * mInt A Φ g := by
  classical
  unfold mInt
  split_ifs with h
  · unfold integralWith
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← integral_const_mul]
    have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
    refine integral_mono_of_nonneg ((ae_restrict_iff' hT).2 (Filter.Eventually.of_forall fun y hy => ?_))
      ((integrableOn_target_of_mIntegrable A Φ h.some hg j).const_mul c)
      ((ae_restrict_iff' hT).2 (Filter.Eventually.of_forall fun y hy => ?_))
    · by_cases hV : (A.chart j).symm y ∈ V
      · exact mul_nonneg (mul_nonneg (h.some.nonneg j _) (hf0 _)) (hdens j y hy hV)
      · simp [hfV _ hV]
    · by_cases hV : (A.chart j).symm y ∈ V
      · calc h.some.χ j ((A.chart j).symm y) * f ((A.chart j).symm y) * locDens A Φ j y
            ≤ h.some.χ j ((A.chart j).symm y) * (c * g ((A.chart j).symm y)) * locDens A Φ j y :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hfg _ hV) (h.some.nonneg j _))
                (hdens j y hy hV)
          _ = c * (h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y) := by ring
      · simp [hfV _ hV, hgV _ hV]
  · simp

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.KaehlerBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData projLineChartData)

def KaehlerBound.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (R : RegChartData A),
    ∃ Om : KaehlerForm A, LeviLe A Set.univ 1 (thetaOmega R) 1 Om.pot ∧
      LeviLe A Set.univ (-1) Om.pot 1 (thetaOmega R)

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StBoundingKaehler
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential)

def BoundingKaehler.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (_ : KaehlerForm A) (m : ℕ) (th : Fin m → LocPot X), (∀ i, IsPotential A (th i)) →
    ∃ Om : KaehlerForm A, ∀ i,
      LeviLe A Set.univ 1 (th i) 1 Om.pot ∧ LeviLe A Set.univ (-1) Om.pot 1 (th i)

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

