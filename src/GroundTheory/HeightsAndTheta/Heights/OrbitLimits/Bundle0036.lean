import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0102
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0112
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0104

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PRatChartChangeVar
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

namespace RatChartChangeVar

variable {n d : ℕ}

theorem ratDens_eq_posParts {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ)
    (hfin : (RatChart.ratFibre J p q y).Finite) :
    RatChart.ratAbsDens J p q f φ y = RatChart.ratPosDens J p q f φ y + RatChart.ratPosDens J p q (-f) φ y ∧
      RatChart.ratDens J p q f φ y = RatChart.ratPosDens J p q f φ y - RatChart.ratPosDens J p q (-f) φ y := by
  unfold RatChart.ratAbsDens RatChart.ratDens RatChart.ratPosDens RatChart.ratSheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine ⟨Finset.sum_congr rfl fun x _ => ?_, Finset.sum_congr rfl fun x _ => ?_⟩ <;>
    split_ifs <;> simp only [Pi.neg_apply, neg_mul, max_zero_add_max_neg_zero_eq_abs_self,
      max_zero_sub_max_neg_zero_eq_self, add_zero, sub_zero]

theorem ratPosDens_nonneg (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    0 ≤ RatChart.ratPosDens J p q f φ y := by
  unfold RatChart.ratPosDens RatChart.ratSheetSum
  exact finsum_nonneg fun x => finsum_nonneg fun _ => by split_ifs <;> simp

theorem measurable_ratPosDens (hM : RatSheetSumMeasurable.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ}
    (hfin : ∀ y, (RatChart.ratFibre J p q y).Finite) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) : Measurable (RatChart.ratPosDens J p q f φ) :=
  hM n d J p q (fun a b => max (a * b) 0) f φ hfin
    ((continuous_fst.mul continuous_snd).max continuous_const).measurable hf

theorem ratInt_eq_posParts (hM : RatSheetSumMeasurable.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ}
    (hfin : ∀ y, (RatChart.ratFibre J p q y).Finite) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) :
    (Integrable (RatChart.ratAbsDens J p q f φ) ↔
      (∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y)) +
        ∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q (-f) φ y) < ⊤) ∧
    (Integrable (RatChart.ratAbsDens J p q f φ) → ∫ y, RatChart.ratDens J p q f φ y =
      (∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y)).toReal -
        (∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q (-f) φ y)).toReal) := by
  have h0 := ratPosDens_nonneg J p q f φ
  have h1 := ratPosDens_nonneg J p q (-f) φ
  have m0 := measurable_ratPosDens hM hfin hf φ
  have m1 := measurable_ratPosDens hM hfin hf.neg φ
  have habs : RatChart.ratAbsDens J p q f φ =
      fun y => RatChart.ratPosDens J p q f φ y + RatChart.ratPosDens J p q (-f) φ y :=
    funext fun y => (ratDens_eq_posParts f φ y (hfin y)).1
  have hlin : ∫⁻ y, ENNReal.ofReal (RatChart.ratAbsDens J p q f φ y) =
      (∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y)) +
        ∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q (-f) φ y) := by
    rw [habs, ← lintegral_add_left m0.ennreal_ofReal]
    exact lintegral_congr fun y => ENNReal.ofReal_add (h0 y) (h1 y)
  have hint : Integrable (RatChart.ratAbsDens J p q f φ) ↔
      ∫⁻ y, ENNReal.ofReal (RatChart.ratAbsDens J p q f φ y) < ⊤ := by
    rw [habs, Integrable, hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun y => add_nonneg (h0 y) (h1 y))]
    exact and_iff_right (m0.add m1).aestronglyMeasurable
  refine ⟨hint.trans (by rw [hlin]), fun hi => ?_⟩
  have hi0 : Integrable (RatChart.ratPosDens J p q f φ) := hi.mono' m0.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (h0 y), habs]; linarith [h1 y])
  have hi1 : Integrable (RatChart.ratPosDens J p q (-f) φ) := hi.mono' m1.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (h1 y), habs]; linarith [h0 y])
  have hd : RatChart.ratDens J p q f φ =
      fun y => RatChart.ratPosDens J p q f φ y - RatChart.ratPosDens J p q (-f) φ y :=
    funext fun y => (ratDens_eq_posParts f φ y (hfin y)).2
  rw [hd, integral_sub hi0 hi1,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) m0.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h1) m1.aestronglyMeasurable]

theorem ratPosDens_split {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (E : ℕ → Set (Fin n → ℂ)) (y : Fin d → ℂ) (hfin : (RatChart.ratFibre J p q y).Finite)
    (hE : Pairwise (Function.onFun Disjoint E))
    (hcov : ∀ x ∈ RatChart.ratFibre J p q y, (∃ s, RatChart.IsRatSheetAt J p q x s) → ∃ k, x ∈ E k) :
    ENNReal.ofReal (RatChart.ratPosDens J p q f φ y) =
      ∑' k, ENNReal.ofReal (RatChart.ratPosDens J p q ((E k).indicator f) φ y) := by
  classical
  unfold RatChart.ratPosDens RatChart.ratSheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  set T : ((Fin n → ℂ) → ℝ) → (Fin n → ℂ) → ℝ := fun g x =>
    if h : ∃ s, RatChart.IsRatSheetAt J p q x s then
      max (g x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y) 0 else 0 with hT
  have hT0 : ∀ g x, 0 ≤ T g x := fun g x => by
    simp only [hT]; split_ifs <;> simp
  have hpt : ∀ x ∈ hfin.toFinset,
      ENNReal.ofReal (T f x) = ∑' k, ENNReal.ofReal (T ((E k).indicator f) x) := by
    intro x hx
    have hx' : x ∈ RatChart.ratFibre J p q y := hfin.mem_toFinset.mp hx
    by_cases hs : ∃ s, RatChart.IsRatSheetAt J p q x s
    · obtain ⟨k₀, hk₀⟩ := hcov x hx' hs
      rw [tsum_eq_single k₀]
      · simp only [hT, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : x ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [hT, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [hT, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 f x), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 _ x)).symm

theorem posPart_eq (hM : RatSheetSumMeasurable.Statement) (hN1 : RatSheetNoChartNull.Statement)
    (hN2 : ChartSheetNoRatNull.Statement) (hL : RatPosPartLocal.Statement)
    {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ}
    {f : (Fin n → ℂ) → ℝ} {φ : Fin d → (Fin n → ℂ) → ℝ}
    (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hA : IsFiniteProjection J A)
    (hq : q ∉ J) (hfin : ∀ y, (RatChart.ratFibre J p q y).Finite) (hf : Measurable f)
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k)) :
    ∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y) =
      ∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y) := by

  have key : ∀ x : Fin n → ℂ, ∃ W : Set (Fin n → ℂ), IsOpen W ∧
      ((∃ s, IsSheetAt J A x s) → (∃ s', RatChart.IsRatSheetAt J p q x s') → x ∈ W) ∧
      ∀ E : Set (Fin n → ℂ), MeasurableSet E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q (E.indicator f) φ y) =
          ∫⁻ y, ENNReal.ofReal (chartPosDens J A (E.indicator f) φ y) := by
    intro x
    by_cases hx : (∃ s, IsSheetAt J A x s) ∧ ∃ s', RatChart.IsRatSheetAt J p q x s'
    · obtain ⟨W, hW, hxW, hWE⟩ := hL n d J A p q f φ x hf hφ hx.1 hx.2
      exact ⟨W, hW, fun _ _ => hxW, fun E hE hEW => (hWE E hE hEW).symm⟩
    · refine ⟨∅, isOpen_empty, fun h1 h2 => absurd ⟨h1, h2⟩ hx, fun E _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.indicator_empty]
      simp [chartPosDens, sheetSum, RatChart.ratPosDens, RatChart.ratSheetSum]
  choose W hWo hxW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E : ℕ → Set (Fin n → ℂ) := fun k => zeroSet J ∩ disjointed (fun k => W (e k)) k with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (SheetSumMeasurable.isClosed_zeroSet J).measurableSet.inter
      (MeasurableSet.disjointed (fun k => (hWo (e k)).measurableSet) k)
  have hEW : ∀ k, E k ⊆ W (e k) := fun k x hx => disjointed_subset (fun k => W (e k)) k hx.2
  have hEd : Pairwise (Function.onFun Disjoint E) := fun i j hij =>
    ((disjoint_disjointed (fun k => W (e k))) hij).mono Set.inter_subset_right
      Set.inter_subset_right
  have hcov : ∀ x ∈ zeroSet J, (∃ s, IsSheetAt J A x s) → (∃ s', RatChart.IsRatSheetAt J p q x s') →
      ∃ k, x ∈ E k := by
    intro x hxZ h1 h2
    have : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x h1 h2⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    have : x ∈ ⋃ k, disjointed (fun k => W (e k)) k := by
      rw [iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hxi⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, hxZ, hk⟩

  have haeR : ∀ᵐ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y) =
      ∑' k, ENNReal.ofReal (RatChart.ratPosDens J p q ((E k).indicator f) φ y) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hN1 n d J A p q hJ hd hA hfin)] with y hy
    refine ratPosDens_split f φ E y (hfin y) hEd fun x hx hs => hcov x hx.1 ?_ hs
    by_contra hn
    exact hy ⟨x, ⟨hx.1, hs, hn⟩, hx.2.2⟩
  have haeA : ∀ᵐ y, ENNReal.ofReal (chartPosDens J A f φ y) =
      ∑' k, ENNReal.ofReal (chartPosDens J A ((E k).indicator f) φ y) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hN2 n d J A p q hJ hd hA hq hfin)] with y hy
    refine PosPartSplit.proof n d J A f φ E y hA hEd fun x hx hs => hcov x hx.1 hs ?_
    by_contra hn
    exact hy ⟨x, ⟨hx.1, hs, hn⟩, hx.2⟩
  rw [lintegral_congr_ae haeR, lintegral_congr_ae haeA,
    lintegral_tsum fun k => (measurable_ratPosDens hM hfin (hf.indicator (hEm k)) φ).ennreal_ofReal.aemeasurable,
    lintegral_tsum fun k =>
      (IntegralIndep.measurable_chartPosDens hA (hf.indicator (hEm k)) φ).ennreal_ofReal.aemeasurable]
  exact tsum_congr fun k => hWE (e k) (E k) (hEm k) (hEW k)

end RatChartChangeVar

theorem RatChartChangeVar.proof (hM : RatSheetSumMeasurable.Statement) (hN1 : RatSheetNoChartNull.Statement)
    (hN2 : ChartSheetNoRatNull.Statement) (hL : RatPosPartLocal.Statement) :
    RatChartChangeVar.Statement := by
  intro n d J A p q f φ hJ hd hA hq hfin hf hφ
  have m1 : Measurable (RatChart.ratDens J p q f φ) :=
    hM n d J p q (fun a b => a * b) f φ hfin (continuous_fst.mul continuous_snd).measurable hf
  have m2 : Measurable (RatChart.ratAbsDens J p q f φ) :=
    hM n d J p q (fun a b => |a * b|) f φ hfin (continuous_fst.mul continuous_snd).abs.measurable hf
  refine ⟨m1.aestronglyMeasurable, m2.aestronglyMeasurable, fun hi => ?_⟩
  have e0 := RatChartChangeVar.posPart_eq hM hN1 hN2 hL hJ hd hA hq hfin hf hφ
  have e1 := RatChartChangeVar.posPart_eq hM hN1 hN2 hL hJ hd hA hq hfin hf.neg hφ
  obtain ⟨iR, cR⟩ := RatChartChangeVar.ratInt_eq_posParts hM hfin hf φ
  obtain ⟨iA, cA⟩ := IntegralIndep.chartInt_eq_posParts hA hf φ
  have hi' : Integrable (chartAbsDens J A f φ) := iA.2 (by rw [← e0, ← e1]; exact iR.1 hi)
  exact ⟨hi', by rw [cR hi, cA hi', e0, e1]⟩

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PRatFibreAvoid
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

namespace RatFibreAvoid

theorem exists_poly_mem_span {L : Type} [CommRing L] [IsDomain L] [Algebra ℂ L] {d : ℕ}
    (htr : Algebra.trdeg ℂ L ≤ d) (t : Fin d → L) {g : L} (hg : g ≠ 0) :
    ∃ h : MvPolynomial (Fin d) ℂ, h ≠ 0 ∧ aeval t h ∈ Ideal.span {g} := by
  by_cases ht : AlgebraicIndependent ℂ t
  · have hgalg : IsAlgebraic (Algebra.adjoin ℂ (Set.range t)) g := by
      by_contra hna
      have hind := (AlgebraicIndependent.option_iff (x := t) (a := g)).2 ⟨ht, hna⟩
      have hle := le_trans hind.cardinalMk_le_trdeg htr
      rw [Cardinal.mk_option, Cardinal.mk_fin] at hle
      have : ((d + 1 : ℕ) : Cardinal.{0}) ≤ d := by exact_mod_cast hle
      have := Nat.cast_le.1 this
      omega
    have hne := Ideal.comap_ne_bot_of_algebraic_mem (R := Algebra.adjoin ℂ (Set.range t)) hg (Ideal.mem_span_singleton_self g) hgalg
    obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨h, hh⟩ : ∃ h, aeval (R := ℂ) t h = (s : L) := by
      have key : ∀ v ∈ Algebra.adjoin ℂ (Set.range t), ∃ h, aeval (R := ℂ) t h = v := by
        intro v hv
        rw [Algebra.adjoin_range_eq_range_aeval] at hv
        exact (AlgHom.mem_range _).1 hv
      exact key _ s.2
    refine ⟨h, ?_, ?_⟩
    · rintro rfl
      apply hs0
      ext
      simpa using hh.symm
    · rw [hh]
      exact Ideal.mem_comap.1 hs
  · rw [algebraicIndependent_iff] at ht
    push Not at ht
    obtain ⟨h, h0, hne⟩ := ht
    exact ⟨h, hne, by rw [h0]; exact zero_mem _⟩

theorem proof : RatFibreAvoid.Statement := by
  intro n d J p q f hJ hdim hf
  classical
  by_cases hq : q ∈ J
  · exact Filter.Eventually.of_forall fun y x hx => absurd (hx.1 q hq) hx.2.1
  set A := MvPolynomial (Fin n) ℂ ⧸ J with hA
  have hdom : IsDomain A := Ideal.Quotient.isDomain J
  set a : A := Ideal.Quotient.mk J q with ha_def
  have ha : a ≠ 0 := fun h => hq (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hpow : Submonoid.powers a ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors ha
  have hLdom : IsDomain (Localization.Away a) := IsLocalization.isDomain_localization hpow
  have htrA : Algebra.trdeg ℂ A = d := by
    obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℂ) (A := A)
    rw [hdim] at hs1
    have : s = d := by exact_mod_cast hs1.symm
    rw [hs2, this]
  have htrL : Algebra.trdeg ℂ (Localization.Away a) ≤ d := by
    have : FaithfulSMul ℂ A := (faithfulSMul_iff_algebraMap_injective ℂ A).2 (algebraMap ℂ A).injective
    have : FaithfulSMul A (Localization.Away a) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (IsLocalization.injective _ hpow)
    have : Algebra.IsAlgebraic A (Localization.Away a) := IsLocalization.isAlgebraic (Localization.Away a) (Submonoid.powers a)
    rw [← trdeg_add_eq ℂ A (A := Localization.Away a), trdeg_eq_zero (R := A) (A := Localization.Away a), add_zero, htrA]
  set T : Fin d → Localization.Away a := fun r =>
    algebraMap A _ (Ideal.Quotient.mk J (p r)) * IsLocalization.Away.invSelf a with hTdef
  have hg : algebraMap A (Localization.Away a) (Ideal.Quotient.mk J f) ≠ 0 := by
    intro h0
    apply hf
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact IsLocalization.injective _ hpow (by rw [h0, map_zero])
  obtain ⟨h, hne, hmem⟩ := exists_poly_mem_span htrL T hg
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  have key : ∀ x ∈ zeroSet J, eval x q ≠ 0 → eval x f = 0 → eval (RatChart.ratMap p q x) h = 0 := by
    intro x hx hqx hfx
    let ev : A →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ J (aeval x) (fun g hg => by simpa using hx g hg)
    have hev : ∀ g, ev (Ideal.Quotient.mk J g) = eval x g := fun g => by
      rfl
    have hea : ev a = eval x q := hev q
    have hu : IsUnit (ev a) := by
      rw [hea]
      exact hqx.isUnit
    let φ : Localization.Away a →ₐ[ℂ] ℂ := IsLocalization.Away.liftAlgHom a hu
    have hφ : ∀ z, φ (algebraMap A _ z) = ev z := fun z =>
      IsLocalization.Away.lift_eq (S := Localization.Away a) (g := (ev : A →+* ℂ)) a hu z
    have hinv : φ (IsLocalization.Away.invSelf a) = (eval x q)⁻¹ := by
      have := congrArg φ (IsLocalization.Away.mul_invSelf (S := Localization.Away a) a)
      rw [map_mul, map_one, hφ, hea] at this
      exact eq_inv_of_mul_eq_one_right this
    have hT : (fun r => φ (T r)) = RatChart.ratMap p q x := by
      funext r
      simp only [hTdef, map_mul, hφ, hev, hinv, RatChart.ratMap, div_eq_mul_inv]
    have := congrArg φ hc
    rw [comp_aeval_apply, hT, map_mul, hφ, hev, hfx, mul_zero] at this
    exact this.symm
  have hnull := DiscriminantSheetCover.volume_zero_set h hne
  have hae : ∀ᵐ y : Fin d → ℂ, eval y h ≠ 0 := by
    rw [ae_iff]
    simpa using hnull
  filter_upwards [hae] with y hy x hx hfx
  obtain ⟨hxZ, hqx, hxy⟩ := hx
  exact hy (hxy ▸ key x hxZ hqx hfx)

end RatFibreAvoid

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PRatPosPartLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace RatPosPartLocal

variable {n d : ℕ}

theorem isOpen_ne_zero (q : MvPolynomial (Fin n) ℂ) : IsOpen {x : Fin n → ℂ | eval x q ≠ 0} :=
  isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const

theorem continuousOn_ratMap (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    ContinuousOn (RatChart.ratMap p q) {x | eval x q ≠ 0} :=
  continuousOn_pi.2 fun r => ((MvPolynomial.continuous_eval (p r)).continuousOn).div
    (MvPolynomial.continuous_eval q).continuousOn fun _ hx => hx

theorem ratPosDens_eq {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} {U : Set (Fin d → ℂ)} {W E : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hsd : DifferentiableOn ℂ s U)
    (hsec : ∀ y ∈ U, s y ∈ zeroSet J ∧ eval (s y) q ≠ 0 ∧ RatChart.ratMap p q (s y) = y)
    (hW : IsOpen W)
    (hWs : ∀ x' ∈ zeroSet J ∩ W, eval x' q ≠ 0 ∧ RatChart.ratMap p q x' ∈ U ∧ s (RatChart.ratMap p q x') = x')
    (hEW : E ⊆ W) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    RatChart.ratPosDens J p q (E.indicator f) φ y = (U ∩ s ⁻¹' E).indicator
      (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y := by
  classical
  unfold RatChart.ratPosDens RatChart.ratSheetSum
  by_cases hy : y ∈ U ∩ s ⁻¹' E
  · rw [Set.indicator_of_mem hy]
    obtain ⟨hZ, hq, hR⟩ := hsec y hy.1
    have hfib : s y ∈ RatChart.ratFibre J p q y := ⟨hZ, hq, hR⟩
    have hsh : RatChart.IsRatSheetAt J p q (s y) s :=
      ⟨U, hU, by rw [hR]; exact hy.1, hsd, by rw [hR], hsec, W,
        hW.mem_nhds (hEW hy.2), fun x' hx' _ _ => (hWs x' hx').2.2.symm⟩
    have hex : ∃ s', RatChart.IsRatSheetAt J p q (s y) s' := ⟨s, hsh⟩
    rw [finsum_eq_single _ (s y) ?_, finsum_eq_if, if_pos hfib, dif_pos hex]
    · have hev : hex.choose =ᶠ[𝓝 y] s := by
        obtain ⟨U₁, hU₁, hxU₁, hsd₁, hsx₁, hsec₁, -⟩ := hex.choose_spec
        rw [hR] at hxU₁ hsx₁
        have hcont : ContinuousAt hex.choose y :=
          hsd₁.continuousOn.continuousAt (hU₁.mem_nhds hxU₁)
        have h1 : ∀ᶠ w in 𝓝 y, hex.choose w ∈ W :=
          hcont.preimage_mem_nhds (by rw [hsx₁]; exact hW.mem_nhds (hEW hy.2))
        filter_upwards [h1, hU₁.mem_nhds hxU₁] with w hwW hwU₁
        have h := (hWs _ ⟨(hsec₁ w hwU₁).1, hwW⟩).2.2
        rw [(hsec₁ w hwU₁).2.2] at h
        exact h.symm
      dsimp only
      rw [IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k => hev.fun_comp (φ k),
        Set.indicator_of_mem (show s y ∈ E from hy.2)]
    · intro x hne
      rw [finsum_eq_if]
      split_ifs with hx h
      · have hxE : x ∉ E := fun hxE => hne (by
          have h' := (hWs x ⟨hx.1, hEW hxE⟩).2.2
          rw [hx.2.2] at h'
          exact h'.symm)
        dsimp only
        rw [Set.indicator_of_notMem hxE, zero_mul, max_self]
      · rfl
      · rfl
  · rw [Set.indicator_of_notMem hy]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    split_ifs with h
    · have hxE : x ∉ E := fun hxE => hy (by
        obtain ⟨-, h1, h2⟩ := hWs x ⟨hx.1, hEW hxE⟩
        rw [hx.2.2] at h1 h2
        exact ⟨h1, by rw [Set.mem_preimage, h2]; exact hxE⟩)
      dsimp only
      rw [Set.indicator_of_notMem hxE, zero_mul, max_self]
    · rfl

end RatPosPartLocal

theorem RatPosPartLocal.proof : RatPosPartLocal.Statement := by
  rintro n d J A p q f φ x - hφ ⟨s, U, hU, hxU, hsd, -, hsec, V, hV, hVs⟩
    ⟨s', U', hU', hxU', hsd', hsx', hsec', V', hV', hVs'⟩
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  set Q := {z : Fin n → ℂ | eval z q ≠ 0} with hQdef
  have hD' : IsOpen (Q ∩ RatChart.ratMap p q ⁻¹' U') :=
    (RatPosPartLocal.continuousOn_ratMap p q).isOpen_inter_preimage (RatPosPartLocal.isOpen_ne_zero q) hU'
  set W := (interior V ∩ (fun z => A *ᵥ z) ⁻¹' U) ∩ (interior V' ∩ (Q ∩ RatChart.ratMap p q ⁻¹' U'))
    with hWdef
  have hW : IsOpen W :=
    (isOpen_interior.inter (hU.preimage hAc)).inter (isOpen_interior.inter hD')
  have hWs : ∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ s (A *ᵥ x') = x' :=
    by rintro x' ⟨hZ, ⟨hV1, hU1⟩, -⟩; exact ⟨hU1, (hVs x' ⟨hZ, interior_subset hV1⟩ hU1).symm⟩
  have hWs' : ∀ x' ∈ zeroSet J ∩ W,
      eval x' q ≠ 0 ∧ RatChart.ratMap p q x' ∈ U' ∧ s' (RatChart.ratMap p q x') = x' :=
    by
      rintro x' ⟨hZ, -, ⟨hV1, hq1, hU1⟩⟩
      exact ⟨hq1, hU1, (hVs' x' ⟨hZ, interior_subset hV1⟩ hq1 hU1).symm⟩
  have hxq : eval x q ≠ 0 := by
    have h := (hsec' _ hxU').2.1
    rwa [hsx'] at h
  refine ⟨W, hW, ⟨⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩, ⟨mem_interior_iff_mem_nhds.2 hV', hxq, hxU'⟩⟩,
    fun E _ hEW => ?_⟩
  simp_rw [PosPartLocal.chartPosDens_eq hU hsd hsec hW hWs hEW,
    RatPosPartLocal.ratPosDens_eq hU' hsd' hsec' hW hWs' hEW]

  set O' := U' ∩ s' ⁻¹' W with hO'def
  set τ : (Fin d → ℂ) → Fin d → ℂ := fun z => A *ᵥ s' z with hτdef
  have hO' : IsOpen O' := hsd'.continuousOn.isOpen_inter_preimage hU' hW
  have hτU : ∀ z ∈ O', τ z ∈ U ∧ s (τ z) = s' z := fun z hz => hWs _ ⟨(hsec' z hz.1).1, hz.2⟩
  have hτd : DifferentiableOn ℂ τ O' := by
    have hs'O : DifferentiableOn ℂ s' O' := hsd'.mono Set.inter_subset_left
    exact ((Matrix.mulVecLin A).toContinuousLinearMap.differentiable.comp_differentiableOn hs'O)
  have hτan : AnalyticOnNhd ℂ τ O' := IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hO' hτd
  have hτinj : Set.InjOn τ O' := fun z₁ h₁ z₂ h₂ h => by
    have h' := congrArg s h
    rw [(hτU z₁ h₁).2, (hτU z₂ h₂).2] at h'
    rw [← (hsec' z₁ h₁.1).2.2, ← (hsec' z₂ h₂.1).2.2, h']
  have hsan : AnalyticOnNhd ℂ s U := IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hU hsd
  calc _ = ∫⁻ y in τ '' O', ENNReal.ofReal ((U ∩ s ⁻¹' E).indicator
          (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) y) := by
        refine (setLIntegral_eq_of_support_subset fun y hy => ?_).symm
        have hyE : y ∈ U ∩ s ⁻¹' E := by
          by_contra h
          exact hy (by simp [Set.indicator_of_notMem h])
        have hZ : s y ∈ zeroSet J ∩ W := ⟨(hsec y hyE.1).2, hEW hyE.2⟩
        refine ⟨RatChart.ratMap p q (s y), ⟨(hWs' _ hZ).2.1, ?_⟩, ?_⟩
        · show s' (RatChart.ratMap p q (s y)) ∈ W
          rw [(hWs' _ hZ).2.2]
          exact hZ.2
        · show A *ᵥ s' (RatChart.ratMap p q (s y)) = y
          rw [(hWs' _ hZ).2.2, (hsec y hyE.1).1]
    _ = ∫⁻ z in O', ENNReal.ofReal (Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det) *
          ENNReal.ofReal ((U ∩ s ⁻¹' E).indicator
            (fun y => max (f (s y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) 0) (τ z)) :=
        ReciprocityTheory.AnForm.A.lintegral_image_eq_lintegral_normSq_det_mul τ O' hO' hτan hτinj _
    _ = ∫⁻ z in O', ENNReal.ofReal ((U' ∩ s' ⁻¹' E).indicator
          (fun y => max (f (s' y) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s') y) 0) z) := by
        refine setLIntegral_congr_fun hO'.measurableSet fun z hz => ?_
        by_cases hzE : s' z ∈ E
        · have hm : τ z ∈ U ∩ s ⁻¹' E :=
            ⟨(hτU z hz).1, by rw [Set.mem_preimage, (hτU z hz).2]; exact hzE⟩
          rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show z ∈ U' ∩ s' ⁻¹' E from ⟨hz.1, hzE⟩)]
          have h1 : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s') z =
              ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) z :=
            IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k => by
              filter_upwards [hO'.mem_nhds hz] with w hw
              show φ k (s' w) = φ k (s (τ w))
              rw [(hτU w hw).2]
          have h2 : ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ τ) z =
              ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (τ z) *
                Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ z).det := by
            refine ReciprocityTheory.AnForm.A.maDens_comp (fun k => φ k ∘ s) τ z (hτan z hz) fun k => ?_
            obtain ⟨Ok, hOk, hZOk, hφk⟩ := hφ k
            have hsZ : s (τ z) ∈ Ok := hZOk (by rw [(hτU z hz).2]; exact (hsec' z hz.1).1)
            have hφa : ContDiffAt ℝ 2 (φ k) (s (τ z)) :=
              (hφk.contDiffAt (hOk.mem_nhds hsZ)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
            have hsa : ContDiffAt ℝ 2 s (τ z) :=
              ((hsan (τ z) (hτU z hz).1).contDiffAt).restrict_scalars ℝ
            exact hφa.comp (τ z) hsa
          rw [h1, h2, (hτU z hz).2, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm,
            max_mul_of_nonneg _ _ (Complex.normSq_nonneg _), zero_mul, mul_assoc]
        · rw [Set.indicator_of_notMem (fun hm => hzE (by
              have := hm.2
              rw [Set.mem_preimage, (hτU z hz).2] at this
              exact this)),
            Set.indicator_of_notMem (show z ∉ U' ∩ s' ⁻¹' E from fun hm => hzE hm.2)]
          simp
    _ = _ := by
        refine setLIntegral_eq_of_support_subset fun z hz => ?_
        have hzE : z ∈ U' ∩ s' ⁻¹' E := by
          by_contra h
          exact hz (by simp [Set.indicator_of_notMem h])
        exact ⟨hzE.1, hEW hzE.2⟩

end

end GroundTheory.Heights₂.Heights
end

