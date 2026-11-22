import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralParametrizedCover
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

section

variable {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]

omit [CompactSpace X] [T2Space X] in

theorem chartPartition_norm_le_one (A : FinHolAtlas e X) (Q : ChartPartition A) (j : Fin A.n)
    (x : X) : ‖Q.χ j x‖ ≤ 1 := by
  have h : Q.χ j x ≤ ∑ k, Q.χ k x :=
    Finset.single_le_sum (f := fun k => Q.χ k x) (fun k _ => Q.nonneg k x) (Finset.mem_univ j)
  rw [Q.sum_eq_one] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (Q.nonneg j x)]
  exact h

theorem chartTerm_integrableOn (A : FinHolAtlas e X) (Q : ChartPartition A) (P : Fin e → LocPot X)
    (g : X → ℝ) (hg : MIntegrable A P g) (j : Fin A.n) :
    IntegrableOn (fun y => Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y)
      (A.chart j).target := by
  have hK : IsCompact (A.chart j '' tsupport (Q.χ j)) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn
      ((A.chart j).continuousOn.mono (Q.tsupport_subset j))
  have hKt : A.chart j '' tsupport (Q.χ j) ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (Q.tsupport_subset j hx)
  have h0 := hg j _ hKt hK
  have hcont : ContinuousOn (fun y => Q.χ j ((A.chart j).symm y)) (A.chart j).target := by
    have h := (Q.smooth j j).continuousOn
    simpa [Function.comp_def] using h
  have hm : AEStronglyMeasurable (fun y => Q.χ j ((A.chart j).symm y))
      (volume.restrict (A.chart j '' tsupport (Q.χ j))) :=
    (hcont.mono hKt).aestronglyMeasurable hK.measurableSet
  have h1 : IntegrableOn
      (fun y => Q.χ j ((A.chart j).symm y) * (g ((A.chart j).symm y) * locDens A P j y))
      (A.chart j '' tsupport (Q.χ j)) :=
    Integrable.bdd_mul (c := 1) h0 hm (ae_of_all _ fun y => chartPartition_norm_le_one A Q j _)
  have h2 : IntegrableOn
      (fun y => Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y)
      (A.chart j '' tsupport (Q.χ j)) := by
    simpa only [mul_assoc] using h1
  refine IntegrableOn.of_forall_sdiff_eq_zero h2 (A.chart j).open_target.measurableSet ?_
  rintro y ⟨hy, hyK⟩
  have hn : (A.chart j).symm y ∉ tsupport (Q.χ j) := fun hmem =>
    hyK ⟨_, hmem, (A.chart j).right_inv hy⟩
  rw [image_eq_zero_of_notMem_tsupport hn]
  ring

theorem chartTerm_hasSum (A : FinHolAtlas e X) (V B : ℕ → Set (Fin e → ℂ))
    (Φ : ℕ → (Fin e → ℂ) → X) (P : Fin e → LocPot X) (g : X → ℝ) (Q : ChartPartition A)
    (hc : IsParamCover A V B Φ) (hC2 : ∀ n, ∀ z ∈ B n, ∀ i, IsTwiceDifferentiableAt A (P i) (Φ n z))
    (hg : MIntegrable A P g) (j : Fin A.n) :
    (∀ n, IntegrableOn (fun z => Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z) (B n)) ∧
      HasSum (fun n => ∫ z in B n, Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z)
        (∫ y in (A.chart j).target,
          Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y) := by
  obtain ⟨hpar, hB, hdisj, hnull⟩ := hc
  have hf := chartTerm_integrableOn A Q P g hg j
  have hCm : ∀ n, MeasurableSet (B n ∩ Φ n ⁻¹' (A.chart j).source) := by
    intro n
    have hO : IsOpen (V n ∩ Φ n ⁻¹' (A.chart j).source) :=
      (hpar n).2.1.isOpen_inter_preimage (hpar n).1 (A.chart j).open_source
    have hEq : B n ∩ Φ n ⁻¹' (A.chart j).source = B n ∩ (V n ∩ Φ n ⁻¹' (A.chart j).source) := by
      ext z
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (hB n).2 h1, h2⟩
      · rintro ⟨h1, _, h2⟩
        exact ⟨h1, h2⟩
    rw [hEq]
    exact (hB n).1.inter hO.measurableSet
  have key := fun n => GlobalTheory.T.monge_ampere_chart_density_integral e X A (V n) (B n ∩ Φ n ⁻¹' (A.chart j).source) (Φ n) P
    (fun x => Q.χ j x * g x) j (hpar n) (hCm n) (fun z hz => (hB n).2 hz.1) (fun z hz => hz.2)
    (fun z hz => hC2 n z hz.1)
  have hsub : ∀ n, (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source) ⊆
      (A.chart j).target := by
    rintro n _ ⟨z, hz, rfl⟩
    exact (A.chart j).map_source hz.2
  have hzero : ∀ n, ∀ z ∈ B n \ (B n ∩ Φ n ⁻¹' (A.chart j).source),
      Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z = 0 := by
    rintro n z ⟨hz, hz'⟩
    have hn : Φ n z ∉ tsupport (Q.χ j) := fun hmem =>
      hz' ⟨hz, Q.tsupport_subset j hmem⟩
    rw [image_eq_zero_of_notMem_tsupport hn]
    ring
  have hdis : Pairwise (Function.onFun Disjoint fun n =>
      (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source)) := by
    intro n m hnm
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hzw⟩
    have hEq : Φ n z = Φ m w := by
      refine (A.chart j).injOn hz.2 hw.2 ?_
      exact hzw.symm
    exact Set.disjoint_left.1 (hdisj hnm) ⟨z, hz.1, rfl⟩ ⟨w, hw.1, hEq.symm⟩
  have hUsub : (⋃ n, (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source)) ⊆
      (A.chart j).target := Set.iUnion_subset hsub
  have hsum := hasSum_integral_iUnion (fun n => (key n).1) hdis (hf.mono_set hUsub)
  have hUeq : (⋃ n, (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source)) =ᵐ[volume]
      (A.chart j).target := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [Set.sdiff_eq_empty.2 hUsub]
      exact measure_empty
    · refine measure_mono_null ?_ (hnull j)
      rintro y ⟨hy, hyU⟩
      refine ⟨hy, ?_⟩
      intro hmem
      obtain ⟨_, ⟨n, rfl⟩, z, hz, hzy⟩ := hmem
      refine hyU (Set.mem_iUnion.2 ⟨n, z, ⟨hz, ?_⟩, ?_⟩)
      · show Φ n z ∈ (A.chart j).source
        rw [hzy]
        exact (A.chart j).map_target hy
      · show A.chart j (Φ n z) = y
        rw [hzy]
        exact (A.chart j).right_inv hy
  rw [setIntegral_congr_set hUeq] at hsum
  constructor
  · intro n
    refine IntegrableOn.of_forall_sdiff_eq_zero
      ((key n).2.1.1 (hf.mono_set (hsub n))) (hB n).1 (hzero n)
  · have hEq : (fun n => ∫ z in B n, Q.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z) =
        fun n => ∫ y in (A.chart j ∘ Φ n) '' (B n ∩ Φ n ⁻¹' (A.chart j).source),
          Q.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y := by
      funext n
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hB n).1 Set.inter_subset_left
        (hzero n)]
      exact ((key n).2.2).symm
    rw [hEq]
    exact hsum

theorem integrableOn_hasSum_paramCover : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (V B : ℕ → Set (Fin e → ℂ)) (Φ : ℕ → (Fin e → ℂ) → X) (P : Fin e → LocPot X) (g : X → ℝ), IsParamCover A V B Φ → (∀ n, ∀ z ∈ B n, ∀ i, IsTwiceDifferentiableAt A (P i) (Φ n z)) → MIntegrable A P g → (∀ n, IntegrableOn (fun z => g (Φ n z) * paramDens P (Φ n) z) (B n)) ∧ HasSum (fun n => ∫ z in B n, g (Φ n z) * paramDens P (Φ n) z) (mInt A P g) := by
  intro e X _ _ _ A V B Φ P g hc hC2 hg
  have hne : Nonempty (ChartPartition A) := existsPartition A
  have hm : mInt A P g = ∑ j, ∫ y in (A.chart j).target,
      hne.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A P j y := by
    rw [mInt, dif_pos hne, integralWith]
  have hj := fun j => chartTerm_hasSum A V B Φ P g hne.some hc hC2 hg j
  have hpt : ∀ n z, g (Φ n z) * paramDens P (Φ n) z =
      ∑ j, hne.some.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z := by
    intro n z
    rw [← Finset.sum_mul, ← Finset.sum_mul, hne.some.sum_eq_one, one_mul]
  have hfun : ∀ n, (fun z => g (Φ n z) * paramDens P (Φ n) z) =
      fun z => ∑ j, hne.some.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z :=
    fun n => funext (hpt n)
  constructor
  · intro n
    rw [hfun n]
    exact integrable_finsetSum _ fun j _ => (hj j).1 n
  · rw [hm]
    have hs := hasSum_sum (s := Finset.univ) fun j _ => (hj j).2
    have hEq : (fun n => ∫ z in B n, g (Φ n z) * paramDens P (Φ n) z) =
        fun n => ∑ j, ∫ z in B n, hne.some.χ j (Φ n z) * g (Φ n z) * paramDens P (Φ n) z := by
      funext n
      rw [hfun n]
      exact integral_finset_sum _ fun j _ => (hj j).1 n
    rw [hEq]
    exact hs

end

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularization
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace AnMono

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isPsh_of_isPosPot (A : FinHolAtlas e X) (Θ : LocPot X) (h : IsPosPot A Θ) : IsPsh A Θ := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw
    simp [levi]
  · exact (h x j y hy w hw).le

theorem log_inv_ge {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-1)) :
    1 ≤ Real.log (1 / t) ∧ 0 ≤ Real.log (Real.log (1 / t)) := by
  have h1 : 1 ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]
    have := Real.log_le_log ht hte
    rw [Real.log_exp] at this
    linarith
  exact ⟨h1, Real.log_nonneg h1⟩

theorem quot_nonneg {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-1)) :
    0 ≤ Real.log (Real.log (1 / t)) / Real.log (1 / t) := by
  obtain ⟨h1, h2⟩ := log_inv_ge ht hte
  exact div_nonneg h2 (by linarith)

theorem epsT_mono {C C' t : ℝ} (hC : C ≤ C') (ht : 0 < t) (hte : t ≤ Real.exp (-1)) :
    epsT C t ≤ epsT C' t := by
  rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
  exact mul_le_mul_of_nonneg_right hC (quot_nonneg ht hte)

theorem mul_epsT_mono {C C' t : ℝ} (hC : |C| ≤ C') (ht : 0 < t) (hte : t ≤ Real.exp (-1)) :
    C * epsT C t ≤ C' * epsT C' t := by
  have hx := quot_nonneg ht hte
  rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, ← mul_assoc, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hx
  have h2 : C ^ 2 ≤ C' ^ 2 := by
    rw [← sq_abs C]
    exact pow_le_pow_left₀ (abs_nonneg C) hC 2
  nlinarith

theorem exp_one_le_rW (L : LocPot X) (s : X → X → ℂ) (hs : ∀ y, logNormSec L s y ≤ 0) (y : X) :
    Real.exp 1 ≤ rW L s y := by
  have := hs y
  unfold rW
  linarith

theorem one_le_log_rW (L : LocPot X) (s : X → X → ℂ) (hs : ∀ y, logNormSec L s y ≤ 0) (y : X) :
    1 ≤ Real.log (rW L s y) := by
  have := Real.log_le_log (Real.exp_pos 1) (exp_one_le_rW L s hs y)
  rwa [Real.log_exp] at this

theorem isSingWeight_mono (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ)
    (hs : ∀ y, logNormSec L s y ≤ 0) (th : LocPot X) (ph : X → ℝ) {C₅ C₅' : ℝ} (hC : C₅ ≤ C₅')
    (h : IsSingWeight A L s th ph C₅) : IsSingWeight A L s th ph C₅' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun y hy => ?_⟩
  obtain ⟨h5, h6⟩ := h4 y hy
  have hl := one_le_log_rW L s hs y
  constructor
  · nlinarith
  · linarith

theorem isRegFamily_enlarge (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) (th : LocPot X)
    (ph : X → ℝ) (phT : ℝ → X → ℝ) {C t₀ C' t₁ : ℝ} (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ)
    (hth : IsPotential A th) (hs : ∀ y, logNormSec L s y ≤ 0)
    (hF : IsRegFamily A Θ L s th ph phT C t₀) (hC : |C| ≤ C') (ht₁ : 0 < t₁) (ht₁₀ : t₁ ≤ t₀)
    (hte : t₁ ≤ Real.exp (-1)) : IsRegFamily A Θ L s th ph phT C' t₁ := by
  obtain ⟨-, ht₀1, hF⟩ := hF
  have hCC : C ≤ C' := (le_abs_self C).trans hC
  have hr : ∀ y, 0 ≤ rW L s y := fun y =>
    (Real.exp_pos 1).le.trans (exp_one_le_rW L s hs y)
  refine ⟨ht₁, ht₁₀.trans_lt ht₀1, fun t ht htt => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hF t ht (htt.trans ht₁₀)
  have hte' : t ≤ Real.exp (-1) := htt.trans hte
  have hε := epsT_mono hCC ht hte'
  have hll := (log_inv_ge ht hte').2
  refine ⟨h1, fun y => (h2 y).trans hCC, h3, fun y => ?_,
    GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono A Θ th (phT t) hΘ hΘp hth h1 hε h5, fun y hy hyr => ?_,
    fun y hy => ?_, fun t' htt' ht' y => ?_⟩
  · have := h4 y
    nlinarith
  · have := h6 y hy hyr
    linarith
  · have := h7 y hy
    have := mul_le_mul_of_nonneg_right hε (hr y)
    linarith
  · have := h8 t' htt' (ht'.trans ht₁₀) y
    have := mul_epsT_mono hC (ht.trans_le htt') (ht'.trans hte)
    linarith

theorem continuous_of_smooth (A : FinHolAtlas e X) (u : X → ℝ) (h : A.Smooth u) : Continuous u := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousOn (u ∘ (A.chart j).symm) (A.chart j).target := by
    have := (h j).continuousOn
    simpa using this
  have hx : (A.chart j) x ∈ (A.chart j).target := (A.chart j).map_source hj
  have h2 : ContinuousAt (u ∘ (A.chart j).symm) (A.chart j x) :=
    h1.continuousAt ((A.chart j).open_target.mem_nhds hx)
  have h3 : ContinuousAt (A.chart j) x := (A.chart j).continuousAt hj
  have h4 : ContinuousAt ((u ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    ContinuousAt.comp (g := u ∘ (A.chart j).symm) h2 h3
  refine h4.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [(A.chart j).left_inv hz]

theorem tendstoUniformlyOn_self {α β : Type*} [UniformSpace β] (f : α → β) (p : Filter ℝ)
    (K : Set α) : TendstoUniformlyOn (fun _ : ℝ => f) f p K := by
  intro v hv
  exact Filter.Eventually.of_forall fun _ y _ => refl_mem_uniformity hv

theorem isRegFamilyC2_const (A : FinHolAtlas e X) (s : X → X → ℂ) (u : X → ℝ) :
    IsRegFamilyC2 A s u (fun _ => u) := fun j K _ _ =>
  ⟨tendstoUniformlyOn_self _ _ _, tendstoUniformlyOn_self _ _ _, tendstoUniformlyOn_self _ _ _⟩

theorem isPsh_add_rsmul (A : FinHolAtlas e X) (Θ th : LocPot X) (u : X → ℝ) {ε : ℝ}
    (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ) (hth : IsPotential A th) (hu : A.Smooth u)
    (hε : 0 ≤ ε) (h : IsPsh A (th + LocPot.ofFun u)) :
    IsPsh A (th + LocPot.ofFun u + Θ.rsmul ε) := by
  refine GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono A Θ th u hΘ hΘp hth hu hε ?_
  intro x j y hy w
  have hfun : (th + LocPot.ofFun u + Θ.rsmul 0).φ x ∘ (A.chart j).symm =
      (th + LocPot.ofFun u).φ x ∘ (A.chart j).symm := by
    funext z
    show th.φ x _ + u _ + 0 * Θ.φ x _ = th.φ x _ + u _
    ring
  rw [hfun]
  exact h x j y ⟨hy.1, hy.2.1⟩ w

theorem smooth_member [CompactSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ)
    (hΘ : IsPotential A Θ) (hΘp : IsPsh A Θ) (hs : ∀ y, logNormSec L s y ≤ 0) (th : LocPot X)
    (u : X → ℝ) (hth : IsPotential A th) (hu : A.Smooth u) (hp : IsPsh A (th + LocPot.ofFun u)) :
    ∃ C₀, IsSingWeight A L s th u C₀ ∧
      IsRegFamily A Θ L s th u (fun _ => u) C₀ (Real.exp (-Real.exp 1)) ∧
        IsRegFamilyC2 A s u (fun _ => u) := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_of_smooth A u hu).continuousOn
  have hb : ∀ y, |u y| ≤ |M| + 1 := fun y => by
    have := hM y (Set.mem_univ y)
    rw [Real.norm_eq_abs] at this
    linarith [le_abs_self M]
  set C₀ : ℝ := |M| + 1 with hC₀
  have hC0 : 0 ≤ C₀ := by positivity
  refine ⟨C₀, ⟨hth, fun j => (hu j).mono ?_, fun x j y hy w => ?_, fun y _ => ?_⟩, ?_,
    isRegFamilyC2_const A s u⟩
  · exact fun z hz => ⟨hz.1, Set.mem_univ _⟩
  · exact hp x j y ⟨hy.1, hy.2.1⟩ w
  · have hl := one_le_log_rW L s hs y
    have h := abs_le.1 (hb y)
    constructor
    · nlinarith
    · exact h.2
  · have he : 0 < Real.exp 1 := Real.exp_pos 1
    refine ⟨Real.exp_pos _, ?_, fun t ht htt => ?_⟩
    · exact Real.exp_lt_one_iff.2 (by linarith)
    have hl := GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht htt
    have hq := GlobalTheory.CompanionTheory.Ar.Giv.loglog_quot_nonneg ht htt
    have hε : 0 ≤ epsT C₀ t := by
      rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
      exact mul_nonneg hC0 hq
    have hε' : ∀ t', 0 < t' → t' ≤ Real.exp (-Real.exp 1) → 0 ≤ C₀ * epsT C₀ t' := fun t' h0 h1 => by
      rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
      exact mul_nonneg hC0 (mul_nonneg hC0 (GlobalTheory.CompanionTheory.Ar.Giv.loglog_quot_nonneg h0 h1))
    have h3 : 0 ≤ t ^ ((1 : ℝ) / 3) := Real.rpow_nonneg ht.le _
    refine ⟨hu, fun y => (abs_le.1 (hb y)).2, fun y _ => le_rfl, fun y => ?_,
      isPsh_add_rsmul A Θ th u hΘ hΘp hth hu hε hp, fun y _ _ => by linarith, fun y _ => ?_,
      fun t' htt' ht' y => ?_⟩
    · have h := abs_le.1 (hb y)
      nlinarith [hl.2]
    · have := mul_nonneg hε (he.le.trans (exp_one_le_rW L s hs y))
      linarith
    · have := hε' t' (ht.trans_le htt') ht'
      linarith

end AnMono

theorem enlarging_constants_smooth_members :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
      (Θ : LocPot X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X),
      IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) →
      IsPotential A Θ → IsPosPot A Θ →
      (∀ th ph C₅ C₅', C₅ ≤ C₅' → IsSingWeight A L s th ph C₅ → IsSingWeight A L s th ph C₅') ∧
      (∀ th ph phT C t₀ C' t₀', |C| ≤ C' → 0 < t₀' → t₀' ≤ t₀ → t₀' ≤ Real.exp (-1) →
        IsRegFamily A Θ L s th ph phT C t₀ → IsPotential A th →
        IsRegFamily A Θ L s th ph phT C' t₀') ∧
      ∀ th u, IsPotential A th → A.Smooth u → IsPsh A (th + LocPot.ofFun u) →
        ∃ C₀, IsSingWeight A L s th u C₀ ∧
          IsRegFamily A Θ L s th u (fun _ => u) C₀ (Real.exp (-Real.exp 1)) ∧
            IsRegFamilyC2 A s u (fun _ => u) := by
  intro e X _ _ _ A Θ L s nb m W _ _ _ hs hΘ hΘpos
  have hΘp := AnMono.isPsh_of_isPosPot A Θ hΘpos
  refine ⟨fun th ph C₅ C₅' hC h => AnMono.isSingWeight_mono A L s hs th ph hC h,
    fun th ph phT C t₀ C' t₀' hC h0 h1 h2 hF hth => ?_,
    fun th u hth hu hp => AnMono.smooth_member A Θ L s hΘ hΘp hs th u hth hu hp⟩
  exact AnMono.isRegFamily_enlarge A Θ L s th ph phT hΘ hΘp hth hs hF hC h0 h1 h2

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistHeightIntegralDecompositionStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_height_integral_decomposition : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (Q : Ideal (MRing ι)) (e : ℕ) (Ψ : (((o : Option K) → Tb ι o) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L' : Fin e → HermLine (Tb ι)) (A' : HermLine (Tb ι)) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι) (v : Fin 2 → ℂ), p ≠ 0 → IsArithVar Q (e + 1) → IsArithVar (twist p Q) (e + 1) → IsGoodProj (twist p Q) Ψ → (∀ j, IsSmoothHerm (L' j)) → IsSmoothHerm A' → IsSectionOn (twist p Q) A' (inc s) → (v = vPlus p ∨ v = vMinus p) → (∀ j, ∀ z ∈ mcPts Q, (L' j).h (glue z v) = (L j).h z) → (∀ z ∈ mcPts Q, A'.h (glue z v) = A.h z) → ∀ᵐ y, ∀ w, sheetDensity (twist p Q) Ψ (pot L') (logNorm A' (inc s)) y (embL v w) = sheetDensity Q (pj v Ψ) (pot L) (logNorm A s) y w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.SheetD.density_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.SheetD.density_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.SheetD.density_twist <;> assumption)
end

