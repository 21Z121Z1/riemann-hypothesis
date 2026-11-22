import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentials
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace SamePotInt

variable {D : ℕ}

theorem exists_fderiv_fderiv_re {H : (Fin D → ℂ) → ℂ} {y : Fin D → ℂ} (hH : AnalyticAt ℂ H y) :
    ∃ B : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) →L[ℂ] ℂ, ∀ v w,
      fderiv ℝ (fderiv ℝ fun z => (H z).re) y v w = (B v w).re := by
  let Φ : ((Fin D → ℂ) →L[ℂ] ℂ) →L[ℝ] ((Fin D → ℂ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM).comp
      (ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ)
  have hev : (fderiv ℝ fun z => (H z).re) =ᶠ[𝓝 y] fun z => Φ (fderiv ℂ H z) := by
    filter_upwards [hH.eventually_analyticAt] with z hz
    have h1 : HasFDerivAt H ((fderiv ℂ H z).restrictScalars ℝ) z :=
      hz.differentiableAt.hasFDerivAt.restrictScalars ℝ
    exact (Complex.reCLM.hasFDerivAt.comp z h1).fderiv
  have hd : DifferentiableAt ℂ (fderiv ℂ H) y := hH.fderiv.differentiableAt
  refine ⟨fderiv ℂ (fderiv ℂ H) y, fun v w => ?_⟩
  have h2 : HasFDerivAt (fun z => Φ (fderiv ℂ H z))
      (Φ.comp ((fderiv ℂ (fderiv ℂ H) y).restrictScalars ℝ)) y :=
    Φ.hasFDerivAt.comp y (hd.hasFDerivAt.restrictScalars ℝ)
  rw [hev.fderiv_eq, h2.fderiv]
  rfl

theorem hessC_re_eq_zero {H : (Fin D → ℂ) → ℂ} {y : Fin D → ℂ} (hH : AnalyticAt ℂ H y) :
    hessC (fun z => (H z).re) y = 0 := by
  obtain ⟨B, hB⟩ := exists_fderiv_fderiv_re hH
  ext i j
  simp only [hessC, Matrix.zero_apply, hB, map_smul, _root_.smul_apply, smul_eq_mul,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  push_cast
  ring

theorem hessC_eq_of_eventuallyEq_add_re {a a' : (Fin D → ℂ) → ℝ} {H : (Fin D → ℂ) → ℂ}
    {y : Fin D → ℂ} (ha : ContDiffAt ℝ 2 a y) (hH : AnalyticAt ℂ H y)
    (hev : a' =ᶠ[𝓝 y] fun z => a z + (H z).re) : hessC a' y = hessC a y := by
  have hb : ContDiffAt ℝ 2 (fun z => (H z).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hH.contDiffAt.restrict_scalars ℝ)
  have h2 : fderiv ℝ (fderiv ℝ a') y =
      fderiv ℝ (fderiv ℝ a) y + fderiv ℝ (fderiv ℝ fun z => (H z).re) y := by
    have hda : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ a z :=
      (ha.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
    have hdb : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (fun z => (H z).re) z :=
      (hb.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
    have h1 : fderiv ℝ a' =ᶠ[𝓝 y] fun z => fderiv ℝ a z + fderiv ℝ (fun z => (H z).re) z := by
      filter_upwards [hev.eventuallyEq_nhds, hda, hdb] with z hz hza hzb
      rw [hz.fderiv_eq]
      exact fderiv_add hza hzb
    rw [h1.fderiv_eq]
    exact fderiv_add ((ha.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      ((hb.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have h0 := hessC_re_eq_zero hH
  rw [← add_zero (hessC a y), ← h0]
  ext i j
  simp only [hessC, Matrix.add_apply, h2, _root_.add_apply]
  push_cast
  ring

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem locDens_eq_of_samePot (A : FinHolAtlas e X) {U : Set X} {P Q : Fin e → LocPot X}
    (hPQ : ∀ i, SamePot A U (P i) (Q i)) (hC : ∀ i, ∀ x ∈ U, IsTwiceDifferentiableAt A (Q i) x) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hU : (A.chart j).symm y ∈ U) :
    locDens A P j y = locDens A Q j y := by
  have key : ∀ i, hessC (fun y' => (P i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      hessC (fun y' => (Q i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
    intro i
    obtain ⟨V, hVo, hxV, G, hG, hPQV⟩ := hPQ i _ hU
    have hsrc : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hy
    have ha : ContDiffAt ℝ 2 (fun y' => (Q i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
      have h := hC i _ hU j hsrc
      rw [(A.chart j).right_inv hy] at h
      exact h
    have hH : AnalyticAt ℂ (fun y' => G ((A.chart j).symm y')) y := hG j y ⟨hy, hxV⟩
    refine hessC_eq_of_eventuallyEq_add_re ha hH ?_
    have hV : (A.chart j).symm ⁻¹' V ∈ 𝓝 y :=
      ((A.chart j).continuousAt_symm hy).preimage_mem_nhds (hVo.mem_nhds hxV)
    filter_upwards [hV] with z hz
    exact sub_eq_iff_eq_add'.mp (hPQV _ hz)
  simp only [locDens, maDens, key]

end SamePotInt

theorem mInt_congr_samePot : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (U : Set X) (P Q : Fin e → LocPot X) (g g' : X → ℝ), IsNull A Uᶜ →
    (∀ i, SamePot A U (P i) (Q i)) → (∀ i, ∀ x ∈ U, IsTwiceDifferentiableAt A (Q i) x) → (∀ x ∈ U, g x = g' x) →
    mInt A P g = mInt A Q g' ∧ (MIntegrable A P g ↔ MIntegrable A Q g') := by
  intro e X _ _ _ A U P Q g g' hN hPQ hC hg
  have hpt : ∀ (j : Fin A.n) (y : Fin e → ℂ), y ∈ (A.chart j).target → (A.chart j).symm y ∈ U →
      g ((A.chart j).symm y) = g' ((A.chart j).symm y) ∧ locDens A P j y = locDens A Q j y :=
    fun j y hy hU => ⟨hg _ hU, SamePotInt.locDens_eq_of_samePot A hPQ hC j hy hU⟩
  have hae : ∀ (j : Fin A.n), ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin e → ℂ)),
      y ∈ (A.chart j).target → (A.chart j).symm y ∈ U := by
    intro j
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (hN j)
    intro y hy
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hy
    exact ⟨hy.1, hy.2⟩
  constructor
  · by_cases h : Nonempty (ChartPartition A)
    · simp only [mInt, dif_pos h, integralWith]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine MeasureTheory.setIntegral_congr_ae (A.chart j).open_target.measurableSet ?_
      filter_upwards [hae j] with y hy hyt
      obtain ⟨h1, h2⟩ := hpt j y hyt (hy hyt)
      simp only [h1, h2]
    · simp only [mInt, dif_neg h]
  · unfold MIntegrable
    refine forall_congr' fun j => forall_congr' fun K => forall_congr' fun hK =>
      forall_congr' fun hKc => ?_
    refine MeasureTheory.integrableOn_congr_fun_ae ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hKc.isClosed.measurableSet]
    filter_upwards [hae j] with y hy hyK
    obtain ⟨h1, h2⟩ := hpt j y (hK hyK) (hy (hK hyK))
    simp only [h1, h2]

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonReproducesHarmonic
section
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem pker_eq {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) (t : ℝ) :
    pker ρ w t = (ρ ^ 2 - ‖w‖ ^ 2) / ‖circleMap 0 ρ t - w‖ ^ 2 := by
  have h : ‖circleMap (0 : ℂ) ρ t‖ = ρ := by simp [abs_of_pos hρ]
  simp only [pker, poissonKernel_def, sub_zero, h]

theorem sub_le_norm_circleMap_sub {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) (t : ℝ) :
    ρ - ‖w‖ ≤ ‖circleMap 0 ρ t - w‖ := by
  have h : ‖circleMap (0 : ℂ) ρ t‖ = ρ := by simp [abs_of_pos hρ]
  have h2 := norm_sub_norm_le (circleMap (0 : ℂ) ρ t) w
  rwa [h] at h2

theorem continuous_pker {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : ‖w‖ < ρ) :
    Continuous (pker ρ w) := by
  have h : pker ρ w = fun t => (ρ ^ 2 - ‖w‖ ^ 2) / ‖circleMap 0 ρ t - w‖ ^ 2 :=
    funext (pker_eq hρ w)
  rw [h]
  refine continuous_const.div
    (((continuous_circleMap 0 ρ).sub continuous_const).norm.pow 2) ?_
  intro t
  have h1 := sub_le_norm_circleMap_sub hρ w t
  have h2 : 0 < ‖circleMap (0 : ℂ) ρ t - w‖ := by linarith
  positivity

theorem exists_abs_pker_le {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : ‖w‖ < ρ) :
    ∃ K : ℝ, ∀ t, |pker ρ w t| ≤ K := by
  refine ⟨(ρ ^ 2 - ‖w‖ ^ 2) / (ρ - ‖w‖) ^ 2, fun t => ?_⟩
  have h1 := sub_le_norm_circleMap_sub hρ w t
  have h0 : 0 < ρ - ‖w‖ := by linarith
  have hn : 0 ≤ ρ ^ 2 - ‖w‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg w) hw.le 2
    linarith
  rw [pker_eq hρ, abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_left hn (by positivity) (pow_le_pow_left₀ h0.le h1 2)

theorem continuous_torusPt {n : ℕ} (ρ : ℝ) : Continuous (torusPt (n := n) ρ) :=
  continuous_pi fun i => (continuous_circleMap 0 ρ).comp (continuous_apply i)

theorem circleMap_mem {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (t : ℝ) :
    circleMap (0 : ℂ) ρ t ≠ 0 ∧ ‖circleMap (0 : ℂ) ρ t‖ < R := by
  refine ⟨circleMap_ne_center hρ.ne', ?_⟩
  have h : ‖circleMap (0 : ℂ) ρ t‖ = ρ := by simp [abs_of_pos hρ]
  rwa [h]

theorem torusPt_mem_punct {n : ℕ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (θ : Fin n → ℝ) :
    torusPt ρ θ ∈ punct R := fun i => circleMap_mem hρ hρR (θ i)

theorem cons_mem_punct {n : ℕ} {R : ℝ} {c : ℂ} {y : Fin n → ℂ} (hc : c ≠ 0 ∧ ‖c‖ < R)
    (hy : y ∈ punct R) : (Fin.cons c y : Fin (n + 1) → ℂ) ∈ punct R := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hc
  · simpa using hy j

theorem continuous_cons_pair {n : ℕ} {α : Type*} [TopologicalSpace α] :
    Continuous (fun p : α × (Fin n → α) => (Fin.cons p.1 p.2 : Fin (n + 1) → α)) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using continuous_fst
  · simp only [Fin.cons_succ]
    exact (continuous_apply j).comp continuous_snd

theorem integral_pi_cons {n : ℕ} (F : (Fin (n + 1) → ℝ) → ℝ)
    (hF : Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2))
      (angMeas.prod (Measure.pi fun _ : Fin n => angMeas))) :
    ∫ θ, F θ ∂(Measure.pi fun _ : Fin (n + 1) => angMeas) =
      ∫ t, ∫ θ', F (Fin.cons t θ') ∂(Measure.pi fun _ : Fin n => angMeas) ∂angMeas := by
  have mp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
      (angMeas.prod (Measure.pi fun _ : Fin n => angMeas))
      (Measure.pi fun _ : Fin (n + 1) => angMeas) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => angMeas) 0).symm _
  have he : ∀ p : ℝ × (Fin n → ℝ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p =
        Fin.cons p.1 p.2 := by
    rintro ⟨a, b⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove]
  rw [← mp.integral_comp']
  simp only [he]
  exact integral_prod _ hF

theorem polyPoisson_eq_self : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℝ) (ρ R M : ℝ), 0 < ρ → ρ < R →
    ContinuousOn f (punct R) → SepHarm R f → (∀ z ∈ punct R, |f z| ≤ M) →
    ∀ z ∈ punct ρ, polyPoisson ρ f z = f z := by
  intro n
  induction n with
  | zero =>
    intro f ρ R M _ _ _ _ _ z _
    have h : ∀ θ : Fin 0 → ℝ, (∏ i, pker ρ (z i) (θ i)) * f (torusPt ρ θ) = f z := by
      intro θ
      simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
      rw [Subsingleton.elim (torusPt ρ θ) z]
    simp only [polyPoisson, h]
    simp
  | succ n ih =>
    intro f ρ R M hρ hρR hc hs hb z hz
    have hz0 := hz 0
    have hzt : Fin.tail z ∈ punct ρ := fun i => hz i.succ
    have hztR : Fin.tail z ∈ punct R := fun i => ⟨(hzt i).1, (hzt i).2.trans hρR⟩
    have hslice : ∀ t, polyPoisson ρ (fun y => f (Fin.cons (circleMap 0 ρ t) y)) (Fin.tail z) =
        f (Fin.cons (circleMap 0 ρ t) (Fin.tail z)) := by
      intro t
      have hcm := circleMap_mem (t := t) hρ hρR
      refine ih _ ρ R M hρ hρR ?_ ?_ ?_ _ hzt
      · have hcont : Continuous (fun y : Fin n → ℂ =>
            (Fin.cons (circleMap 0 ρ t) y : Fin (n + 1) → ℂ)) :=
          continuous_cons_pair.comp (continuous_const.prodMk continuous_id)
        exact hc.comp hcont.continuousOn (fun y hy => cons_mem_punct hcm hy)
      · intro y hy i
        have h := hs _ (cons_mem_punct hcm hy) i.succ
        simp only [Fin.cons_succ] at h
        simpa only [Fin.cons_update] using h
      · exact fun y hy => hb _ (cons_mem_punct hcm hy)
    have hone := GlobalTheory.CompanionTheory.Ar.PuncturedDisc.poisson_formula_punctured (fun w => f (Fin.cons w (Fin.tail z))) ρ R M hρ hρR
      (fun w hw0 hwR => by
        have h := hs _ (cons_mem_punct ⟨hw0, hwR⟩ hztR) 0
        simpa only [Fin.update_cons_zero, Fin.cons_zero] using h)
      (fun w hw0 hwR => hb _ (cons_mem_punct ⟨hw0, hwR⟩ hztR))
      (z 0) hz0.1 hz0.2
    simp only [Fin.cons_self_tail] at hone
    set F : (Fin (n + 1) → ℝ) → ℝ :=
      fun θ => (∏ i, pker ρ (z i) (θ i)) * f (torusPt ρ θ) with hFdef
    have hFc : Continuous F :=
      (continuous_finsetProd _ fun i _ =>
        (continuous_pker hρ (hz i).2).comp (continuous_apply i)).mul
      (hc.comp_continuous (continuous_torusPt ρ) (torusPt_mem_punct hρ hρR))
    have hFb : ∃ K, ∀ θ, |F θ| ≤ K := by
      choose K hK using fun i => exists_abs_pker_le hρ (hz i).2
      refine ⟨(∏ i, K i) * M, fun θ => ?_⟩
      rw [hFdef]
      simp only [abs_mul, Finset.abs_prod]
      have hM : 0 ≤ M := (abs_nonneg _).trans (hb _ (torusPt_mem_punct hρ hρR θ))
      have hK0 : 0 ≤ ∏ i, K i :=
        Finset.prod_nonneg fun i _ => (abs_nonneg _).trans (hK i 0)
      exact mul_le_mul
        (Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hK i _))
        (hb _ (torusPt_mem_punct hρ hρR θ)) (abs_nonneg _) hK0
    obtain ⟨K, hK⟩ := hFb
    have hint : Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2))
        (angMeas.prod (Measure.pi fun _ : Fin n => angMeas)) :=
      Integrable.of_bound (hFc.comp continuous_cons_pair).aestronglyMeasurable K
        (ae_of_all _ fun p => hK _)
    have hFcons : ∀ t θ', F (Fin.cons t θ') = pker ρ (z 0) t *
        ((∏ i, pker ρ (Fin.tail z i) (θ' i)) *
          f (Fin.cons (circleMap 0 ρ t) (torusPt ρ θ'))) := by
      intro t θ'
      have ht : torusPt ρ (Fin.cons t θ' : Fin (n + 1) → ℝ) =
          Fin.cons (circleMap 0 ρ t) (torusPt ρ θ') := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [torusPt]
      simp only [hFdef, ht, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail, mul_assoc]
    calc polyPoisson ρ f z
        = ∫ t, ∫ θ', F (Fin.cons t θ') ∂(Measure.pi fun _ : Fin n => angMeas) ∂angMeas :=
          integral_pi_cons F hint
      _ = ∫ t, pker ρ (z 0) t * f (Fin.cons (circleMap 0 ρ t) (Fin.tail z)) ∂angMeas := by
          refine integral_congr_ae (ae_of_all _ fun t => ?_)
          have h : ∫ θ', F (Fin.cons t θ') ∂(Measure.pi fun _ : Fin n => angMeas) =
              pker ρ (z 0) t *
                polyPoisson ρ (fun y => f (Fin.cons (circleMap 0 ρ t) y)) (Fin.tail z) := by
            simp only [hFcons]
            rw [integral_const_mul]
            rfl
          simp only [h, hslice t]
      _ = f z := hone

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RingKrullDimTwistSucc
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def baseD (p : ℕ) (W : Ideal (MRing ι)) : (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
  Ideal.Quotient.lift W ((Ideal.Quotient.mk (twist p W)).comp inc) fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))

def baseP (p : ℕ) (W : Ideal (MRing ι)) :
    Polynomial (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
  Polynomial.eval₂RingHom (baseD p W) (Ideal.Quotient.mk (twist p W) yN)

def quadP (p : ℕ) (W : Ideal (MRing ι)) : Polynomial (Polynomial (MRing ι ⧸ W)) :=
  Polynomial.X ^ 2 + Polynomial.C (Polynomial.C ((p : ℤ) : MRing ι ⧸ W) * Polynomial.X ^ 2)

theorem quadraticPolynomial_monic (p : ℕ) (W : Ideal (MRing ι)) : (quadP p W).Monic := by
  exact Polynomial.monic_X_pow_add_C _ two_ne_zero

theorem quadraticPolynomial_natDegree (p : ℕ) (W : Ideal (MRing ι)) [Nontrivial (MRing ι ⧸ W)] : (quadP p W).natDegree = 2 := by
  exact Polynomial.natDegree_X_pow_add_C

def coordA (p : ℕ) (W : Ideal (MRing ι)) : (Σ o, Tb ι o) → AdjoinRoot (quadP p W)
  | ⟨none, j⟩ => (![AdjoinRoot.root _, AdjoinRoot.of _ Polynomial.X] : Fin 2 → _) j
  | ⟨some k, i⟩ => AdjoinRoot.of _ (Polynomial.C (Ideal.Quotient.mk W (X ⟨k, i⟩)))

def toA (p : ℕ) (W : Ideal (MRing ι)) : MRing (Tb ι) →+* AdjoinRoot (quadP p W) :=
  (aeval (coordA p W) : MRing (Tb ι) →ₐ[ℤ] AdjoinRoot (quadP p W)).toRingHom

theorem toA_inc (p : ℕ) (W : Ideal (MRing ι)) (f : MRing ι) :
    toA p W (inc f) = AdjoinRoot.of _ (Polynomial.C (Ideal.Quotient.mk W f)) := by
  have h : (toA p W).comp inc =
      (AdjoinRoot.of (quadP p W)).comp (Polynomial.C.comp (Ideal.Quotient.mk W)) := by
    apply MvPolynomial.ringHom_ext'
    · exact RingHom.ext_int _ _
    · intro i
      simp only [RingHom.comp_apply, toA, inc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X,
        aeval_X]
      rfl
  exact RingHom.congr_fun h f

theorem toA_xN (p : ℕ) (W : Ideal (MRing ι)) : toA p W xN = AdjoinRoot.root _ := by
  simp only [toA, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem toA_yN (p : ℕ) (W : Ideal (MRing ι)) : toA p W yN = AdjoinRoot.of _ Polynomial.X := by
  simp only [toA, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem toA_quad (p : ℕ) (W : Ideal (MRing ι)) : toA p W (quad p) = 0 := by
  have h : AdjoinRoot.mk (quadP p W) (Polynomial.X ^ 2 +
      Polynomial.C (Polynomial.C ((p : ℤ) : MRing ι ⧸ W) * Polynomial.X ^ 2)) = 0 :=
    AdjoinRoot.mk_self
  simp only [map_add, map_pow, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_intCast,
    Int.cast_natCast, map_natCast] at h
  have hC : toA p W (MvPolynomial.C (p : ℤ)) = (p : AdjoinRoot (quadP p W)) := by
    rw [map_natCast MvPolynomial.C p, map_natCast]
  simp only [quad, map_add, map_mul, map_pow, toA_xN, toA_yN, hC]
  linear_combination h

theorem twist_le_ker_toA (p : ℕ) (W : Ideal (MRing ι)) : twist p W ≤ RingHom.ker (toA p W) := by
  unfold twist
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, toA_inc, Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero,
      map_zero]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (RingHom.mem_ker).2 (toA_quad p W)

def quotA (p : ℕ) (W : Ideal (MRing ι)) : (MRing (Tb ι) ⧸ twist p W) →+* AdjoinRoot (quadP p W) :=
  Ideal.Quotient.lift _ (toA p W) fun _ ha => twist_le_ker_toA p W ha

theorem quotA_mk (p : ℕ) (W : Ideal (MRing ι)) (f : MRing (Tb ι)) :
    quotA p W (Ideal.Quotient.mk _ f) = toA p W f := by
  exact Ideal.Quotient.lift_mk _ _ _

theorem baseD_mk (p : ℕ) (W : Ideal (MRing ι)) (f : MRing ι) :
    baseD p W (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (inc f) := by
  exact Ideal.Quotient.lift_mk _ _ _

theorem baseP_C (p : ℕ) (W : Ideal (MRing ι)) (a : MRing ι ⧸ W) :
    baseP p W (Polynomial.C a) = baseD p W a := by
  simp [baseP]

theorem baseP_X (p : ℕ) (W : Ideal (MRing ι)) :
    baseP p W Polynomial.X = Ideal.Quotient.mk _ yN := by
  simp [baseP]

theorem quotA_baseP (p : ℕ) (W : Ideal (MRing ι)) (g : Polynomial (MRing ι ⧸ W)) :
    quotA p W (baseP p W g) = AdjoinRoot.of _ g := by
  have h : (quotA p W).comp (baseP p W) = AdjoinRoot.of (quadP p W) := by
    apply Polynomial.ringHom_ext
    · intro a
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [RingHom.comp_apply, baseP_C, baseD_mk, quotA_mk, toA_inc]
    · rw [RingHom.comp_apply, baseP_X, quotA_mk, toA_yN]
  exact RingHom.congr_fun h g

theorem baseMap_injective (p : ℕ) (W : Ideal (MRing ι)) [Nontrivial (MRing ι ⧸ W)] :
    Function.Injective (baseP p W) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  have h0 : AdjoinRoot.of (quadP p W) g = 0 := by
    rw [← quotA_baseP, hg, map_zero]
  rw [← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_zero] at h0
  obtain ⟨q, hq⟩ := h0
  by_cases hq0 : q = 0
  · rw [hq0, mul_zero, Polynomial.C_eq_zero] at hq
    exact hq
  · have h1 := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_C, (quadraticPolynomial_monic p W).natDegree_mul' hq0, quadraticPolynomial_natDegree] at h1
    omega

theorem mk_quad_eq_zero (p : ℕ) (W : Ideal (MRing ι)) :
    Ideal.Quotient.mk (twist p W) (quad p) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

theorem baseMap_isIntegralElem_xN (p : ℕ) (W : Ideal (MRing ι)) :
    (baseP p W).IsIntegralElem (Ideal.Quotient.mk (twist p W) xN) := by
  refine ⟨quadP p W, quadraticPolynomial_monic p W, ?_⟩
  rw [← mk_quad_eq_zero p W]
  have hp : (Ideal.Quotient.mk (twist p W)) (MvPolynomial.C (p : ℤ)) =
      (p : MRing (Tb ι) ⧸ twist p W) := by
    rw [map_natCast MvPolynomial.C p, map_natCast]
  simp only [quadP, quad, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, map_mul, map_pow, map_add, baseP_X, map_intCast,
    Int.cast_natCast, hp, map_natCast, Polynomial.eval₂_natCast]

theorem baseMap_isIntegralElem_X (p : ℕ) (W : Ideal (MRing ι)) (q : Σ o, Tb ι o) :
    (baseP p W).IsIntegralElem (Ideal.Quotient.mk (twist p W) (X q)) := by
  obtain ⟨o, j⟩ := q
  cases o with
  | none =>
    revert j
    change ∀ j : Fin 2, _
    intro j
    fin_cases j
    · exact baseMap_isIntegralElem_xN p W
    · have h := RingHom.isIntegralElem_map (baseP p W) (x := Polynomial.X)
      rw [baseP_X] at h
      exact h
  | some k =>
    have h : Ideal.Quotient.mk (twist p W) (X ⟨some k, j⟩ : MRing (Tb ι)) =
        baseP p W (Polynomial.C (Ideal.Quotient.mk W (X ⟨k, j⟩))) := by
      rw [baseP_C, baseD_mk]
      simp [inc, oldIdx]
    rw [h]
    exact RingHom.isIntegralElem_map _

theorem baseMap_isIntegral (p : ℕ) (W : Ideal (MRing ι)) (b : MRing (Tb ι) ⧸ twist p W) :
    (baseP p W).IsIntegralElem b := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction f using MvPolynomial.induction_on
  · rw [eq_intCast MvPolynomial.C, map_intCast, ← map_intCast (baseP p W)]
    exact RingHom.isIntegralElem_map _
  · rw [map_add]
    exact RingHom.IsIntegralElem.add _ ‹_› ‹_›
  · rw [map_mul]
    exact RingHom.IsIntegralElem.mul _ ‹_› (baseMap_isIntegralElem_X p W _)

theorem ringKrullDim_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (W : Ideal (MRing ι)) (hW : W.IsPrime) :
    ringKrullDim (MRing (Tb ι) ⧸ twist p W) = ringKrullDim (MRing ι ⧸ W) + 1 := by
  haveI : W.IsPrime := hW
  haveI : Nontrivial (MRing ι ⧸ W) := inferInstance
  haveI : IsNoetherianRing (MRing ι) :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial ((k : K) × ι k) ℤ))
  letI : Algebra (Polynomial (MRing ι ⧸ W)) (MRing (Tb ι) ⧸ twist p W) := (baseP p W).toAlgebra
  haveI : Algebra.IsIntegral (Polynomial (MRing ι ⧸ W)) (MRing (Tb ι) ⧸ twist p W) :=
    ⟨fun b => baseMap_isIntegral p W b⟩
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (baseMap_injective p W),
    Polynomial.ringKrullDim_of_isNoetherianRing]

end GlobalTheory.CompanionTheory.Ar.Tw
end
end

