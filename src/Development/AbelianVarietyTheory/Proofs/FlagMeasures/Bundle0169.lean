import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0136

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaWithCutoffSubgroup
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory

private theorem lintegral_eq_lintegral_weight_mul_lintegral {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν] [μ.IsMulLeftInvariant]
    (β : G → ENNReal) (hβ : Measurable β) (hone : ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1)
    (φ : G → ENNReal) (hφ : Measurable φ) :
    ∫⁻ y, φ y ∂μ = ∫⁻ y, β y * ∫⁻ m, φ (m * y) ∂ν ∂μ := by
  calc ∫⁻ y, φ y ∂μ = ∫⁻ y, (∫⁻ m, β (m⁻¹ * y) ∂ν) * φ y ∂μ := by
          simp only [hone, one_mul]
    _ = ∫⁻ y, ∫⁻ m, β (m⁻¹ * y) * φ y ∂ν ∂μ := by
          refine lintegral_congr (fun y => ?_)
          have hb : Measurable (fun m => β (m⁻¹ * y)) := hβ.comp (measurable_inv.mul_const y)
          exact (lintegral_mul_const _ hb).symm
    _ = ∫⁻ m, ∫⁻ y, β (m⁻¹ * y) * φ y ∂μ ∂ν := by
          have hm : Measurable (fun p : G × G => β (p.2⁻¹ * p.1) * φ p.1) :=
            (hβ.comp (measurable_snd.inv.mul measurable_fst)).mul (hφ.comp measurable_fst)
          exact lintegral_lintegral_swap (f := fun y m => β (m⁻¹ * y) * φ y) hm.aemeasurable
    _ = ∫⁻ m, ∫⁻ y, β y * φ (m * y) ∂μ ∂ν := by
          refine lintegral_congr (fun m => ?_)
          have h := lintegral_mul_left_eq_self (μ := μ) (fun y => β (m⁻¹ * y) * φ y) m
          simp only [inv_mul_cancel_left] at h
          exact h.symm
    _ = ∫⁻ y, ∫⁻ m, β y * φ (m * y) ∂ν ∂μ := by
          have hm : Measurable (fun p : G × G => β p.2 * φ (p.1 * p.2)) :=
            (hβ.comp measurable_snd).mul (hφ.comp (measurable_fst.mul measurable_snd))
          exact lintegral_lintegral_swap (f := fun m y => β y * φ (m * y)) hm.aemeasurable
    _ = ∫⁻ y, β y * ∫⁻ m, φ (m * y) ∂ν ∂μ := by
          refine lintegral_congr (fun y => ?_)
          have hb : Measurable (fun m => φ (m * y)) := hφ.comp (measurable_mul_const y)
          exact lintegral_const_mul _ hb

private theorem integrable_and_integral_eq_of_lintegral_weight_one {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν] [μ.IsMulLeftInvariant]
    (β : G → ENNReal) (hβ : Measurable β) (hfin : ∀ y, β y ≠ ⊤) (hone : ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1)
    (g : G → ℂ) (hg : Measurable g) (hgi : Integrable g μ) :
    Integrable (fun y => ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν) μ ∧
      ∫ y, g y ∂μ = ∫ y, ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν ∂μ := by
  have hkey := lintegral_eq_lintegral_weight_mul_lintegral μ ν β hβ hone
  have hgl : ∫⁻ y, ‖g y‖ₑ ∂μ < ⊤ := hgi.hasFiniteIntegral
  have hnorm : ∀ y (z : ℂ), ‖((β y).toReal : ℂ) * z‖ₑ = β y * ‖z‖ₑ := by
    intro y z
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin y)]
  have hHm : Measurable (fun p : G × G => ((β p.2).toReal : ℂ) * g (p.1 * p.2)) :=
    (Complex.measurable_ofReal.comp (hβ.comp measurable_snd).ennreal_toReal).mul
      (hg.comp (measurable_fst.mul measurable_snd))
  have hHi : Integrable (fun p : G × G => ((β p.2).toReal : ℂ) * g (p.1 * p.2)) (ν.prod μ) := by
    refine ⟨hHm.aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖((β p.2).toReal : ℂ) * g (p.1 * p.2)‖ₑ ∂(ν.prod μ) < ⊤
    rw [lintegral_prod_symm _ hHm.enorm.aemeasurable]
    simp only [hnorm]
    have h2 : ∀ y, ∫⁻ m, β y * ‖g (m * y)‖ₑ ∂ν = β y * ∫⁻ m, ‖g (m * y)‖ₑ ∂ν := fun y =>
      lintegral_const_mul _ (hg.enorm.comp (measurable_mul_const y))
    simp only [h2]
    rw [← hkey _ hg.enorm]
    exact hgl
  have heq : ∀ y, ∫ m, ((β y).toReal : ℂ) * g (m * y) ∂ν = ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν :=
    fun y => integral_const_mul _ _
  have hint0 : Integrable (fun y => ∫ m, ((β y).toReal : ℂ) * g (m * y) ∂ν) μ :=
    hHi.integral_prod_right
  have hint : Integrable (fun y => ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν) μ :=
    hint0.congr (ae_of_all _ heq)
  refine ⟨hint, ?_⟩
  have hKm : Measurable (fun p : G × G => ((β (p.1⁻¹ * p.2)).toReal : ℂ) * g p.2) :=
    (Complex.measurable_ofReal.comp
      (hβ.comp (measurable_fst.inv.mul measurable_snd)).ennreal_toReal).mul (hg.comp measurable_snd)
  have hKi : Integrable (fun p : G × G => ((β (p.1⁻¹ * p.2)).toReal : ℂ) * g p.2) (ν.prod μ) := by
    refine ⟨hKm.aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖((β (p.1⁻¹ * p.2)).toReal : ℂ) * g p.2‖ₑ ∂(ν.prod μ) < ⊤
    rw [lintegral_prod_symm _ hKm.enorm.aemeasurable]
    simp only [hnorm]
    have h3 : ∀ y, ∫⁻ m, β (m⁻¹ * y) * ‖g y‖ₑ ∂ν = ‖g y‖ₑ := by
      intro y
      have hb : Measurable (fun m => β (m⁻¹ * y)) := hβ.comp (measurable_inv.mul_const y)
      rw [lintegral_mul_const _ hb, hone, one_mul]
    simp only [h3]
    exact hgl
  have hβone : ∀ y, ∫ m, ((β (m⁻¹ * y)).toReal : ℂ) ∂ν = 1 := by
    intro y
    have hb : Measurable (fun m => β (m⁻¹ * y)) := hβ.comp (measurable_inv.mul_const y)
    rw [integral_complex_ofReal, integral_toReal hb.aemeasurable (ae_of_all _ fun m => (hfin _).lt_top),
      hone, ENNReal.toReal_one, Complex.ofReal_one]
  calc ∫ y, g y ∂μ = ∫ y, (∫ m, ((β (m⁻¹ * y)).toReal : ℂ) ∂ν) * g y ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        show g y = (∫ m, ((β (m⁻¹ * y)).toReal : ℂ) ∂ν) * g y
        rw [hβone y, one_mul]
    _ = ∫ y, ∫ m, ((β (m⁻¹ * y)).toReal : ℂ) * g y ∂ν ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        exact (integral_mul_const _ _).symm
    _ = ∫ m, ∫ y, ((β (m⁻¹ * y)).toReal : ℂ) * g y ∂μ ∂ν :=
        (integral_prod_symm _ hKi).symm.trans (integral_prod _ hKi)
    _ = ∫ m, ∫ y, ((β y).toReal : ℂ) * g (m * y) ∂μ ∂ν := by
        refine integral_congr_ae (ae_of_all _ fun m => ?_)
        have h := integral_mul_left_eq_self (μ := μ) (fun y => ((β (m⁻¹ * y)).toReal : ℂ) * g y) m
        simp only [inv_mul_cancel_left] at h
        exact h.symm
    _ = ∫ y, ∫ m, ((β y).toReal : ℂ) * g (m * y) ∂ν ∂μ :=
        (integral_prod _ hHi).symm.trans (integral_prod_symm _ hHi)
    _ = ∫ y, ((β y).toReal : ℂ) * ∫ m, g (m * y) ∂ν ∂μ :=
        integral_congr_ae (ae_of_all _ heq)

theorem weil_formula_cutoff : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) (ν : Measure G), IsClosed (N : Set G) → IsHaarSub (N : Set G) ν → ∀ β : G → ENNReal, Measurable β → (∀ y, β y ≠ ⊤) → (∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) → (∀ f : G → ENNReal, Measurable f → ∫⁻ y, f y ∂μ = ∫⁻ y, β y * ∫⁻ m, f (m * y) ∂ν ∂μ) ∧ ∀ f : G → ℂ, Integrable f μ → Integrable (fun y => ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν) μ ∧ ∫ y, f y ∂μ = ∫ y, ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν ∂μ := by
  intro G _ _ _ _ _ _ _ _ μ _ N ν _hN hH β hβ hfin hone
  have hH' := hH
  unfold IsHaarSub at hH'
  haveI : IsFiniteMeasureOnCompacts ν := hH'.2.1
  haveI : SigmaFinite ν := inferInstance
  have hkey := lintegral_eq_lintegral_weight_mul_lintegral μ ν β hβ hone
  refine ⟨hkey, fun f hf => ?_⟩
  have hgm : Measurable (hf.aestronglyMeasurable.mk f) :=
    hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[μ] hf.aestronglyMeasurable.mk f := hf.aestronglyMeasurable.ae_eq_mk
  obtain ⟨hgi, hgeq⟩ := integrable_and_integral_eq_of_lintegral_weight_one μ ν β hβ hfin hone _ hgm (hf.congr hfg)
  have hEm : MeasurableSet (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}) :=
    measurableSet_toMeasurable _ _
  have hE0 : μ (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}) = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.mp hfg
  have hsub : {y | f y ≠ hf.aestronglyMeasurable.mk f y} ⊆
      toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y} := subset_toMeasurable _ _
  have hind : Measurable ((toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}).indicator
      (1 : G → ENNReal)) := measurable_one.indicator hEm
  have h0 := hkey _ hind
  rw [lintegral_indicator_one hEm, hE0] at h0
  have hIm : Measurable (fun y => β y * ∫⁻ m, (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}).indicator
      (1 : G → ENNReal) (m * y) ∂ν) :=
    hβ.mul (hind.comp measurable_mul).lintegral_prod_left'
  have hae := (lintegral_eq_zero_iff' hIm.aemeasurable).mp h0.symm
  have hcong : (fun y => ((β y).toReal : ℂ) * ∫ m, f (m * y) ∂ν) =ᵐ[μ]
      (fun y => ((β y).toReal : ℂ) * ∫ m, hf.aestronglyMeasurable.mk f (m * y) ∂ν) := by
    filter_upwards [hae] with y hy
    have hy' : β y * ∫⁻ m, (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}).indicator
        (1 : G → ENNReal) (m * y) ∂ν = 0 := hy
    rcases mul_eq_zero.mp hy' with hb | hI
    · simp [hb]
    · congr 1
      have hmy : Measurable (fun m => (toMeasurable μ {y | f y ≠ hf.aestronglyMeasurable.mk f y}).indicator
          (1 : G → ENNReal) (m * y)) := hind.comp (measurable_mul_const y)
      have hae2 := (lintegral_eq_zero_iff hmy).mp hI
      refine integral_congr_ae ?_
      filter_upwards [hae2] with m hm
      by_contra hne
      have hmE := hsub hne
      simp [Set.indicator_of_mem hmE] at hm
  refine ⟨hgi.congr hcong.symm, ?_⟩
  rw [integral_congr_ae hfg, hgeq, integral_congr_ae hcong]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilIntegralVanishingOfFibreIntegrals
section
open MeasureTheory GlobalTheory.Dec

namespace GlobalTheory.Dec

theorem integral_mul_eq_zero_of_cutoff {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ ν : Measure G) [SFinite μ] [SFinite ν] [μ.IsMulLeftInvariant]
    (β : G → ENNReal) (hβ : Measurable β) (hβt : ∀ y, β y ≠ ⊤) (hβ1 : ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1)
    (F φ : G → ℂ) (hF : Measurable F) (hφ : Measurable φ) (hinv : ∀ᵐ m ∂ν, ∀ y, F (m * y) = F y)
    (hint : Integrable (fun y => F y * φ y) μ) (h0 : ∀ y, ∫ m, φ (m * y) ∂ν = 0) :
    ∫ y, F y * φ y ∂μ = 0 := by
  set f : G × G → ℂ := fun p => ((β (p.1⁻¹ * p.2)).toReal : ℂ) * (F p.2 * φ p.2) with hf_def
  have hβm : Measurable fun p : G × G => β (p.1⁻¹ * p.2) :=
    hβ.comp (measurable_fst.inv.mul measurable_snd)
  have hfm : Measurable f :=
    (Complex.measurable_ofReal.comp hβm.ennreal_toReal).mul
      ((hF.comp measurable_snd).mul (hφ.comp measurable_snd))

  have hβy : ∀ y, Measurable fun m : G => β (m⁻¹ * y) := fun y =>
    hβ.comp (measurable_inv.mul_const y)
  have hfib : ∀ y, ∫ m, (β (m⁻¹ * y)).toReal ∂ν = 1 := by
    intro y
    rw [integral_toReal (hβy y).aemeasurable (Filter.Eventually.of_forall fun m => (hβt _).lt_top),
      hβ1 y, ENNReal.toReal_one]
  have hfibI : ∀ y, Integrable (fun m => (β (m⁻¹ * y)).toReal) ν := fun y =>
    integrable_toReal_of_lintegral_ne_top (hβy y).aemeasurable (by rw [hβ1 y]; exact ENNReal.one_ne_top)

  have hA : ∫ y, F y * φ y ∂μ = ∫ y, ∫ m, f (m, y) ∂ν ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hf_def]
    rw [integral_mul_const, integral_complex_ofReal, hfib y]
    simp

  have hfI : Integrable f (ν.prod μ) := by
    rw [integrable_prod_iff' hfm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · simp only [hf_def]
      exact (hfibI y).ofReal.mul_const _
    · have hn : (fun y => ∫ m, ‖f (m, y)‖ ∂ν) = fun y => ‖F y * φ y‖ := by
        funext y
        simp only [hf_def, norm_mul, Complex.norm_real, Real.norm_eq_abs, ENNReal.abs_toReal]
        rw [integral_mul_const, hfib y, one_mul]
      rw [hn]
      exact hint.norm

  have hmp : MeasurePreserving (fun p : G × G => (p.1, p.1 * p.2)) (ν.prod μ) (ν.prod μ) :=
    measurePreserving_prod_mul ν μ
  have hemb : MeasurableEmbedding (fun p : G × G => (p.1, p.1 * p.2)) :=
    (MeasurableEquiv.shearMulRight G).measurableEmbedding
  have hae : ∀ᵐ p ∂(ν.prod μ),
      f (p.1, p.1 * p.2) = ((β p.2).toReal : ℂ) * (F p.2 * φ (p.1 * p.2)) := by
    have h1 : ∀ᵐ p ∂(ν.prod μ), ∀ y, F (p.1 * y) = F y :=
      Measure.quasiMeasurePreserving_fst.ae hinv
    filter_upwards [h1] with p hp
    simp only [hf_def, inv_mul_cancel_left, hp]
  have hgI : Integrable (fun p : G × G => ((β p.2).toReal : ℂ) * (F p.2 * φ (p.1 * p.2)))
      (ν.prod μ) :=
    ((hmp.integrable_comp_emb hemb).2 hfI).congr hae
  calc ∫ y, F y * φ y ∂μ
      = ∫ p, ((β p.2).toReal : ℂ) * (F p.2 * φ (p.1 * p.2)) ∂(ν.prod μ) := by
        rw [hA, ← integral_prod_symm f hfI, ← hmp.integral_comp hemb f]
        exact integral_congr_ae hae
    _ = ∫ z, ∫ m, ((β z).toReal : ℂ) * (F z * φ (m * z)) ∂ν ∂μ := integral_prod_symm _ hgI
    _ = 0 := by
        have hz : ∀ z, ∫ m, ((β z).toReal : ℂ) * (F z * φ (m * z)) ∂ν = 0 := by
          intro z
          simp_rw [← mul_assoc]
          rw [integral_const_mul, h0 z, mul_zero]
        simp only [hz, integral_zero]

theorem weilVanish : WeilVanish := by
  unfold WeilVanish
  intro G _ _ _ _ _ _ _ _ μ _ N ν hN hν F φ hF hφ hinv hint h0
  obtain ⟨β, hβ, hβt, hβ1⟩ := exists_measurable_cutoff_fibre_integral_one G N ν hN hν
  haveI : IsFiniteMeasureOnCompacts ν := hν.2.1
  have hN' : ∀ᵐ m ∂ν, m ∈ (N : Set G) := mem_ae_iff.2 hν.2.2.1
  have hae : ∀ᵐ m ∂ν, ∀ y, F (m * y) = F y := hN'.mono fun m hm y => hinv m hm y
  exact integral_mul_eq_zero_of_cutoff μ ν β hβ hβt hβ1 F φ hF hφ hae hint h0

end GlobalTheory.Dec
end

