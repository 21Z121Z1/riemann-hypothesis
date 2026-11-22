import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0195
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1823
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOrientedVacuumIsometryMovedLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1827
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilDatumSignedHomPairTransportIsometries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelHalfChainNumbersAnyLevelPrime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicPureTensorEqProductLocal
section
open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.AdelicHaarPure

theorem measurableSet_box (F : Type) [Field F] [NumberField F] (κ : Type) [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSet {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} := by
  have : {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} =
      ⋂ v, ⋂ (_ : v ∉ S), ⋂ i, (fun y : κ → Af F => evalV F v (y i)) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y; simp
  rw [this]
  refine IsClosed.measurableSet (isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_iInter fun i => ?_)
  exact (Valued.isClosed_integer (v.adicCompletion F)).preimage ((GlobalTheory.GaugeGlue.continuous_evalV v).comp (continuous_apply i))

theorem evalV_add_singleFin_ne {F : Type} [Field F] [NumberField F] {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w)
    (a : Af F) (t : Fv F w) : evalV F v (a + singleFin w t) = evalV F v a := by
  rw [map_add, evalV_singleFin_ne h, add_zero]

theorem finPart (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (κ → Fv F v)] [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (κ → Fv F v)]
    (μf : Measure (κ → Af F)) [μf.IsAddHaarMeasure]
    (hμf : μf {y | ∀ i (v : HeightOneSpectrum (𝓞 F)), evalV F v (y i) ∈ v.adicCompletionIntegers F} = 1)
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (κ → Fv F v)) [∀ v, (μv v).IsAddHaarMeasure]
    (hμv : ∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (f : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℝ≥0∞)
    (hf : ∀ v, Measurable (f v)) :
    ∫⁻ y, {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y *
        ∏ v ∈ S, f v (fun i => evalV F v (y i)) ∂μf = ∏ v ∈ S, ∫⁻ t, f v t ∂(μv v) := by
  classical
  have hcw : ∀ v, Measurable fun y : κ → Af F => fun i => evalV F v (y i) := fun v =>
    (continuous_pi fun i => (GlobalTheory.GaugeGlue.continuous_evalV v).comp (continuous_apply i)).measurable
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, mul_one]
    rw [lintegral_indicator_one (measurableSet_box F κ ∅), ← hμf]
    congr 1
    ext y
    simp only [Finset.notMem_empty, not_false_eq_true, forall_const, Set.mem_setOf_eq]
    exact forall_comm
  | insert w S hw ih =>
    set K : (κ → Af F) → ℝ≥0∞ := fun y =>
      {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y *
        ∏ v ∈ S, f v (fun i => evalV F v (y i)) with hK
    have hKm : Measurable K :=
      (measurable_one.indicator (measurableSet_box F κ _)).mul
        (Finset.measurable_prod _ fun v _ => (hf v).comp (hcw v))
    have hKi : ∀ (y : κ → Af F) (t : κ → Fv F w), K (fun i => y i + singleFin w (t i)) = K y := by
      intro y t
      have h1 : ∀ v ∈ S, (fun i => evalV F v (y i + singleFin w (t i))) = fun i => evalV F v (y i) := fun v hv =>
        funext fun i => evalV_add_singleFin_ne (by rintro rfl; exact hw hv) _ _
      have h2 : ({y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1
          (fun i => y i + singleFin w (t i)) : ℝ≥0∞) =
          {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y := by
        have : ((fun i => y i + singleFin w (t i)) ∈
            {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}) ↔
            (y ∈ {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}) := by
          simp only [Set.mem_setOf_eq]
          refine forall_congr' fun v => imp_congr_right fun hv => forall_congr' fun i => ?_
          rw [evalV_add_singleFin_ne (by rintro rfl; exact hv (Finset.mem_insert_self _ S))]
        by_cases hy : y ∈ {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (this.2 hy)]; rfl
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (this.1 h))]
      simp only [hK, h2]
      congr 1
      exact Finset.prod_congr rfl fun v hv => by rw [h1 v hv]
    have hstep := GlobalTheory.T.lintegral_finiteAdelic_factor_offPlace F κ w μf (μv w) (hμv w) K hKm hKi (f w) (hf w)
    have e1 : ∀ y : κ → Af F,
        {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y *
          ∏ v ∈ insert w S, f v (fun i => evalV F v (y i)) = f w (fun i => evalV F w (y i)) * K y := by
      intro y
      rw [Finset.prod_insert hw, hK]
      ring
    have hiff : ∀ y : κ → Af F, (∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F) ↔
        (∀ i, evalV F w (y i) ∈ w.adicCompletionIntegers F) ∧
          ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F := by
      intro y
      constructor
      · intro h
        exact ⟨h w hw, fun v hv => h v fun h' => hv (Finset.mem_insert_of_mem h')⟩
      · rintro ⟨h1, h2⟩ v hv
        by_cases hvw : v = w
        · subst hvw; exact h1
        · exact h2 v (by simp [hvw, hv])
    have e2 : ∀ y : κ → Af F, {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F}.indicator 1
        (fun i => evalV F w (y i)) * K y =
        {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y *
          ∏ v ∈ S, f v (fun i => evalV F v (y i)) := by
      intro y
      rw [hK, ← mul_assoc]
      congr 1
      by_cases h : y ∈ {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}
      · have h' := (hiff y).1 h
        rw [Set.indicator_of_mem h, Set.indicator_of_mem (show (fun i => evalV F w (y i)) ∈
          {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F} from h'.1),
          Set.indicator_of_mem (show y ∈ {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}
            from h'.2)]
        simp
      · rw [Set.indicator_of_notMem h]
        by_cases h1 : ∀ i, evalV F w (y i) ∈ w.adicCompletionIntegers F
        · have h2 : y ∉ {y : κ → Af F | ∀ v ∉ insert w S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} :=
            fun h2 => h ((hiff y).2 ⟨h1, h2⟩)
          rw [Set.indicator_of_notMem h2, mul_zero]
        · rw [Set.indicator_of_notMem (show (fun i => evalV F w (y i)) ∉
            {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F} from h1), zero_mul]
    simp_rw [e1]
    rw [hstep, Finset.prod_insert hw]
    simp_rw [e2]
    rw [ih]

theorem integral_pure_haar : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)] [BorelSpace (κ → mixedEmbedding.mixedSpace F)]
    [∀ v : Pl F, MeasurableSpace (κ → Fv F v)] [∀ v : Pl F, BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure] (μi : Measure (κ → mixedEmbedding.mixedSpace F)) [μi.IsAddHaarMeasure]
    (μv : ∀ v : Pl F, Measure (κ → Fv F v)) [∀ v, (μv v).IsAddHaarMeasure],
    (∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1) → ∃ c : ℂ, c ≠ 0 ∧
      ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), Continuous f → Integrable f μi → IsFam φ →
        Integrable (fun x : κ → AF F => f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) μ ∧
        ∫ x, f (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i)) ∂μ = c * (∫ x, f x ∂μi) * ∏ᶠ v, ∫ x, φ v x ∂(μv v) := by
  intro F _ _ κ _ _ _ _ _ _ _ μ _ μi _ μv _ hμv
  classical
  letI : MeasurableSpace (κ → Af F) := borel _
  haveI : BorelSpace (κ → Af F) := ⟨rfl⟩
  haveI : ∀ v : Pl F, ProperSpace (Fv F v) := fun v => GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  obtain ⟨μf, hμfH, hμf1⟩ := GlobalTheory.T.exists_finiteAdelicHaar_integralPoints_one F κ
  obtain ⟨c, hc0, hctop, hc⟩ := GlobalTheory.T.lintegral_adelicHaar_split_archimedean_finite F κ μ μi μf
  refine ⟨(c.toReal : ℂ), Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hc0, hctop⟩), fun f φ hfc hfi hφ => ?_⟩
  have hfinS := Filter.eventually_cofinite.1 hφ.2
  set S := hfinS.toFinset with hS
  have hout : ∀ v ∉ S, φ v = ind κ v := by
    intro v hv
    by_contra hne
    exact hv (by simpa [hS] using hne)
  have hpi : Continuous fun x : κ → AF F => fun i => evI F (x i) :=
    continuous_pi fun i => (GlobalTheory.Core.Rk.RapidInt.continuous_toMixed F).comp (continuous_fst.comp (continuous_apply i))
  have hpv : ∀ v : Pl F, Continuous fun x : κ → AF F => fun i => evFin F v (x i) := fun v =>
    continuous_pi fun i => (GlobalTheory.GaugeGlue.continuous_evalV v).comp (continuous_snd.comp (continuous_apply i))
  set B : Set (κ → AF F) := {x | ∀ v ∉ S, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F} with hB
  have hBm : MeasurableSet B := by
    have : B = (fun x : κ → AF F => fun i => sndA F (x i)) ⁻¹'
        {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} := rfl
    rw [this]
    have hsnd : Continuous (fun x : κ → AF F => fun i => sndA F (x i)) :=
      continuous_pi fun i => continuous_snd.comp (continuous_apply i)
    exact hsnd.measurable (measurableSet_box F κ S)
  have hlin : ∀ (fi : (κ → mixedEmbedding.mixedSpace F) → ℝ≥0∞) (fv : ∀ v : Pl F, (κ → Fv F v) → ℝ≥0∞),
      Measurable fi → (∀ v, Measurable (fv v)) →
      ∫⁻ x, fi (fun i => evI F (x i)) * ∏ v ∈ S, fv v (fun i => evFin F v (x i)) ∂(μ.restrict B) =
        (∫⁻ z, fi z ∂μi) * (∏ v ∈ S, ∫⁻ t, fv v t ∂(μv v)) * c := by
    intro fi fv hfi hfv
    rw [← lintegral_indicator hBm]
    have e : ∀ x : κ → AF F, B.indicator (fun x => fi (fun i => evI F (x i)) * ∏ v ∈ S, fv v (fun i => evFin F v (x i))) x =
        fi (fun i => evI F (x i)) *
          ({y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 (fun i => sndA F (x i)) *
            ∏ v ∈ S, fv v (fun i => evalV F v (sndA F (x i)))) := by
      intro x
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show (fun i => sndA F (x i)) ∈
          {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} from hx)]
        simp only [Pi.one_apply, one_mul]
        rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show (fun i => sndA F (x i)) ∉
          {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F} from hx)]
        simp
    simp_rw [e]
    have hcw : ∀ v, Measurable fun y : κ → Af F => fun i => evalV F v (y i) := fun v =>
      (continuous_pi fun i => (GlobalTheory.GaugeGlue.continuous_evalV v).comp (continuous_apply i)).measurable
    have hgm : Measurable fun y : κ → Af F =>
        {y : κ → Af F | ∀ v ∉ S, ∀ i, evalV F v (y i) ∈ v.adicCompletionIntegers F}.indicator 1 y *
          ∏ v ∈ S, fv v (fun i => evalV F v (y i)) :=
      (measurable_one.indicator (measurableSet_box F κ S)).mul
        (Finset.measurable_prod _ fun v _ => (hfv v).comp (hcw v))
    rw [hc fi _ hfi hgm,
      finPart F κ μf hμf1 μv hμv S fv hfv]
    ring
  have hint : ∀ v, Integrable (φ v) (μv v) := fun v =>
    (hφ.1 v).1.continuous.integrable_of_hasCompactSupport (hφ.1 v).2
  obtain ⟨h1, h2⟩ := GlobalTheory.GaugeEx.ProdInt.integral_tensor (μ.restrict B) μi μv (fun x : κ → AF F => fun i => evI F (x i))
    (fun v x i => evFin F v (x i)) hpi.measurable (fun v => (hpv v).measurable) S c hctop hlin f φ hfi hint
  have hΦB : (fun x : κ → AF F => f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) =
      B.indicator fun x => f (fun i => evI F (x i)) * ∏ v ∈ S, φ v (fun i => evFin F v (x i)) := by
    funext x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, finprod_eq_prod_of_mulSupport_subset (s := S)]
      intro v hv
      by_contra hvS
      apply hv
      simp only [hout v hvS, ind]
      exact Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        hx v hvS) _
    · rw [Set.indicator_of_notMem hx]
      simp only [hB, Set.mem_setOf_eq, not_forall] at hx
      obtain ⟨v, hvS, i, hv⟩ := hx
      have hev : ∀ᶠ v in Filter.cofinite, φ v (fun i => evFin F v (x i)) = 1 := by
        have h1 : ∀ᶠ v in Filter.cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
          Filter.eventually_all.2 fun i => (sndA F (x i)).2
        filter_upwards [hφ.2, h1] with w h2 h3
        rw [h2]
        exact Set.indicator_of_mem (show (fun i => evFin F w (x i)) ∈ {x | ∀ i, x i ∈ w.adicCompletionIntegers F} from h3) _
      rw [finprod_eq_zero _ v (by rw [hout v hvS]; exact Set.indicator_of_notMem (show (fun i => evFin F v (x i)) ∉
          {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun h => hv (h i)) _)
        (Filter.eventually_cofinite.1 hev), mul_zero]
  have hprod : ∏ᶠ v, ∫ x, φ v x ∂(μv v) = ∏ v ∈ S, ∫ x, φ v x ∂(μv v) := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    intro v hv
    by_contra hvS
    apply hv
    have hm : MeasurableSet {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
      have : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} =
          ⋂ i, (fun x : κ → Fv F v => x i) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by ext; simp
      rw [this]
      exact (isClosed_iInter fun i => (Valued.isClosed_integer (v.adicCompletion F)).preimage (continuous_apply i)).measurableSet
    have := integral_indicator_const (μ := μv v) (1 : ℂ) hm
    simp only [hout v hvS, ind]
    simpa [Measure.real, Pi.one_def, hμv v] using this
  rw [hΦB, hprod]
  refine ⟨(integrable_indicator_iff hBm).2 h1, ?_⟩
  rw [integral_indicator hBm, h2]
  ring

end GlobalTheory.AdelicHaarPure

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSeesawTripleTransportIsometries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open MeasureTheory GlobalTheory.TriMove GlobalTheory.Mem.Isom

namespace GlobalTheory.TriMoveConst

variable {D : D7}

def kapME {V V' : HSp D} (I : IsoMat V V') : GA D V ≃ᵐ GA D V' :=
  (Homeomorph.mk I.kap.toEquiv I.continuous_kap I.continuous_kap_symm).toMeasurableEquiv

theorem kapME_apply {V V' : HSp D} (I : IsoMat V V') (g : GA D V) : kapME I g = I.kap g := rfl

theorem preimage_kapME {V V' : HSp D} (I : IsoMat V V') (s : Set (GA D V)) : kapME I ⁻¹' (I.kap.symm ⁻¹' s) = s := by
  ext g
  simp only [Set.mem_preimage, kapME_apply, MulEquiv.symm_apply_apply]

theorem trH_symm_trH {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (F : WO S T → ℂ) :
    trH IS.symm IT.symm (trH IS IT F) = F := by
  funext w
  show F ((homMap IS IT).symm (homMap IS IT w)) = F w
  rw [AddEquiv.symm_apply_apply]

theorem thetaKO_omH {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T')
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T) (F : WO S T → ℂ) :
    thetaKO (omH IS IT om) (IS.kap g) (IT.kap h) (trH IS IT F) = thetaKO om g h F := by
  unfold thetaKO
  rw [omH_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, trH_symm_trH]
  show (om (g, h) F) ((homMap IS IT).symm 0) = _
  rw [map_zero]

variable {T₀ : Type} {A A' WW B B' WW₁ : HSp D}

theorem ker_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B.rank)
    (h : GA D WW₁) (g : GA D B) :
    (triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) (IA.kap g) = Y.ker ψ θ t P h g := by
  have hF := GlobalTheory.T.fockPureTensor_isometry_moved_orthonormal ψ θ hθ true IA IW Y.rA.s Y.rA.B Y.rW.s Y.rW.B (Y.f t) P
  have hs : ∀ {k : ℕ} (s : Matrix (Fin k) (Fin k) ℂ), GlobalTheory.Grid.sgnM true s = -s := fun _ => rfl
  simp only [hs] at hF
  exact (congrArg (thetaKO (omH IA IW (Y.ω t)) (IA.kap g) (IW.kap h)) hF).trans (thetaKO_omH IA IW (Y.ω t) g h _)

theorem ker'_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B'.rank)
    (h : GA D WW₁) (g : GA D B') :
    (triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) (IA'.kap g) = Y.ker' ψ θ t P h g := by
  have hF := GlobalTheory.T.fockPureTensor_isometry_moved_orthonormal ψ θ hθ false IA' IW Y.rA'.s Y.rA'.B Y.rW.s Y.rW.B (Y.f' t) P
  show thetaKO (omH IA' IW (Y.ω' t)) (IA'.kap g) (IW.kap h) (pureTensorO ψ θ (GlobalTheory.Grid.sgn false A') WW
      (fun τ => GlobalTheory.Grid.sgnM false (cartMove IA' τ (Y.rA'.s τ))) (fun τ => cartMove IW τ (Y.rW.s τ))
      (fun τ => basMove IA' τ (Y.rA'.B τ)) (fun τ => basMove IW τ (Y.rW.B τ)) (trH IA' IW (Y.f' t))
      (polMove IW.rank_eq IA'.rank_eq P)) =
    thetaKO (Y.ω' t) g h (pureTensorO ψ θ (GlobalTheory.Grid.sgn false B') WW₁ (fun τ => GlobalTheory.Grid.sgnM false (Y.rA'.s τ)) Y.rW.s Y.rA'.B
      Y.rW.B (Y.f' t) P)
  rw [hF, thetaKO_omH]

theorem I_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B.rank)
    (h : GA D WW₁) :
    (triMove IA IA' IW Y).I ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) = Y.I ψ θ t P h := by
  show ∫ g in IA.kap.symm ⁻¹' Y.fd, (triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) g
      ∂(Y.m.map (kapME IA)) = _
  rw [setIntegral_map_equiv (kapME IA), preimage_kapME]
  exact congrArg (fun F => ∫ g in Y.fd, F g ∂Y.m) (funext fun g => ker_move IA IA' IW Y ψ θ hθ t P h g)

theorem I'_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B'.rank)
    (h : GA D WW₁) :
    (triMove IA IA' IW Y).I' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) = Y.I' ψ θ t P h := by
  show ∫ g in IA'.kap.symm ⁻¹' Y.fd', (triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) g
      ∂(Y.m'.map (kapME IA')) = _
  rw [setIntegral_map_equiv (kapME IA'), preimage_kapME]
  exact congrArg (fun F => ∫ g in Y.fd', F g ∂Y.m') (funext fun g => ker'_move IA IA' IW Y ψ θ hθ t P h g)

theorem integrableOn_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B.rank)
    (h : GA D WW₁) :
    IntegrableOn ((triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h)) (triMove IA IA' IW Y).fd
      (triMove IA IA' IW Y).m ↔ IntegrableOn (Y.ker ψ θ t P h) Y.fd Y.m := by
  show IntegrableOn ((triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h)) (IA.kap.symm ⁻¹' Y.fd)
      (Y.m.map (kapME IA)) ↔ _
  rw [IntegrableOn, (kapME IA).restrict_map, integrable_map_equiv, preimage_kapME]
  have e : (triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) ∘ kapME IA = Y.ker ψ θ t P h :=
    funext fun g => ker_move IA IA' IW Y ψ θ hθ t P h g
  rw [e]
  rfl

theorem integrableOn'_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B'.rank)
    (h : GA D WW₁) :
    IntegrableOn ((triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h)) (triMove IA IA' IW Y).fd'
      (triMove IA IA' IW Y).m' ↔ IntegrableOn (Y.ker' ψ θ t P h) Y.fd' Y.m' := by
  show IntegrableOn ((triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h)) (IA'.kap.symm ⁻¹' Y.fd')
      (Y.m'.map (kapME IA')) ↔ _
  rw [IntegrableOn, (kapME IA').restrict_map, integrable_map_equiv, preimage_kapME]
  have e : (triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) ∘ kapME IA' = Y.ker' ψ θ t P h :=
    funext fun g => ker'_move IA IA' IW Y ψ θ hθ t P h g
  rw [e]
  rfl

theorem isConst_triMove : ∀ {D : D7} {T₀ : Type} {A A' WW B B' WW₁ : HSp D} (IA : GlobalTheory.Mem.Isom.IsoMat B A) (IA' : GlobalTheory.Mem.Isom.IsoMat B' A') (IW : GlobalTheory.Mem.Isom.IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁) (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D), IsInfFam θ →
  ∀ c : T₀ → ℂ, Y.IsConst ψ θ c → (GlobalTheory.TriMove.triMove IA IA' IW Y).IsConst ψ θ c := by
  intro D T₀ A A' WW B B' WW₁ IA IA' IW Y ψ θ hθ c hY
  obtain ⟨hc, P, P', H⟩ := hY
  refine ⟨hc, polMove IW.rank_eq IA.rank_eq P, polMove IW.rank_eq IA'.rank_eq P', fun t => ?_⟩
  obtain ⟨hint, ⟨h0, hne⟩, heq⟩ := H t
  refine ⟨fun h' => ?_, ⟨IW.kap h0, ?_⟩, fun h' => ?_⟩
  · obtain ⟨h, rfl⟩ := IW.kap.surjective h'
    exact ⟨(integrableOn_move IA IA' IW Y ψ θ hθ t P h).2 (hint h).1,
      (integrableOn'_move IA IA' IW Y ψ θ hθ t P' h).2 (hint h).2⟩
  · rw [I'_move IA IA' IW Y ψ θ hθ t P' h0]
    exact hne
  · obtain ⟨h, rfl⟩ := IW.kap.surjective h'
    rw [I_move IA IA' IW Y ψ θ hθ t P h, I'_move IA IA' IW Y ψ θ hθ t P' h]
    exact heq h

end GlobalTheory.TriMoveConst

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOrientedVacuumIsometryMovedLatticesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOrientedVacuum_isometry_moved_lattices : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (ε : Bool) {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f : WO S T → ℂ),
  IsVacO ψ θ (GlobalTheory.Grid.sgn ε S) T (fun τ => GlobalTheory.Grid.sgnM ε (sS τ)) sT LS LT f →
  IsVacO ψ θ (GlobalTheory.Grid.sgn ε S') T' (fun τ => GlobalTheory.Grid.sgnM ε (GlobalTheory.TriMove.cartMove (S' := S') IS τ (sS τ))) (fun τ => GlobalTheory.TriMove.cartMove (S' := T') IT τ (sT τ)) (GlobalTheory.TriMove.latMove (S' := S') IS LS) (GlobalTheory.TriMove.latMove (S' := T') IT LT) (GlobalTheory.TriMove.trH (S := S) (S' := S') (T := T) (T' := T') IS IT f) := by
  first | exact @GlobalTheory.VacMove.isVacO_move | exact GlobalTheory.VacMove.isVacO_move | (intros; apply GlobalTheory.VacMove.isVacO_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfManyTorsionPointsCharZeroStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_many_torsion_points_charZero : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  first | exact @GlobalTheory.ManyTorsionProper.isProper_of_many_torsion_charZero | exact GlobalTheory.ManyTorsionProper.isProper_of_many_torsion_charZero | (intros; apply GlobalTheory.ManyTorsionProper.isProper_of_many_torsion_charZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalFormalPathOfIntegralAllPlacesStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRationalFormalPath_of_integral_allPlaces : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G] (ξ : Sp (PowerSeries E) ⟶ G.left) (u : Place k E → E), (∀ p, u p ≠ 0) → {p | ord p (u p) ≠ 0}.Finite → 0 < ∑ᶠ p, ord p (u p) → (∀ p : Place k E, ∃ (b : Sp p.O ⟶ C) (ζ : Sp (PowerSeries p.O) ⟶ G.left), spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ IsPath G 2 b ζ ∧ ξ = spMap (sc p (u p)) ≫ ζ) → IsRatPath ξ := by
  first | exact @GlobalTheory.Nef.isRatPath_of_integral_at_places | exact GlobalTheory.Nef.isRatPath_of_integral_at_places | (intros; apply GlobalTheory.Nef.isRatPath_of_integral_at_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilDatumSignedHomPairTransportIsometriesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isWeilDatumSignedHomPair_transport_isometries : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
  GlobalTheory.Grid.IsWeil ψ ε S T χS χT om → GlobalTheory.Grid.IsWeil ψ ε S' T' χS χT (GlobalTheory.TriMove.omH IS IT om) := by
  first | exact @GlobalTheory.IsoBoth.isWeil_omH | exact GlobalTheory.IsoBoth.isWeil_omH | (intros; apply GlobalTheory.IsoBoth.isWeil_omH <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMovedRiggingIsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometryMovedRigging_is : ∀ {D : D7} {S S' : HSp D} (I : GlobalTheory.Mem.Isom.IsoMat S S') (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig S), r.Is → (GlobalTheory.TriMove.rigMove I r).Is := by
  first | exact @GlobalTheory.TriMove.rigMove_is | exact GlobalTheory.TriMove.rigMove_is | (intros; apply GlobalTheory.TriMove.rigMove_is <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelHalfChainNumbersAnyLevelPrimeStatement
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelHalf_chainNumbers_any_levelPrime : ∀ CY : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (N : NumDatum) (X : Fields) [IsTotallyComplex X.K] (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b) (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch)) (hF : ∀ j, (chF W sel mu I u j).Ok) (hE : (evGSD W Ch sel mu (rPsymF Ch) u).Ok) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)), HostTie N s Pr → WeightTie N W pl u δ → CharTie N s W Ch G sel → AnalyticTie D dl χ cD → mu = 1 → cst.sharp = true → I.Ok Ch sel mu cst G (N.R.m - 2) → FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Reads N eJ δ (Pr.T u) R → KerSide R (InfinitePlace X.K) C (FactorBounds (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) fun l => (eJ l).1) := by
  first | exact @GlobalTheory.KernelHalfS.kerSide_chainS | exact GlobalTheory.KernelHalfS.kerSide_chainS | (intros; apply GlobalTheory.KernelHalfS.kerSide_chainS <;> assumption)
end

