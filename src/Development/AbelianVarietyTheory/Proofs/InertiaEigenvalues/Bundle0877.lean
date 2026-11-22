import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousColConvIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import GroundTheory.AutomorphicForms.ReductionFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0871

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurableCompInfGLProd
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host GlobalTheory.Published GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.Petersson
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.MspanROrth

open GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {ω : HChar E}

theorem measurable_chart_prod {F : GA E a → ℂ} (hF : Continuous F) :
    Measurable fun p : GA E a × Lie E a => chart F p.1 p.2 := by
  classical
  have h1 := GlobalTheory.ConstTermSmooth.continuousOn_chart (E := E) (a := a) hF
  have e : (fun p : GA E a × Lie E a => chart F p.1 p.2) =
      (Set.univ ×ˢ invSet E a).piecewise (fun p : GA E a × Lie E a => chart F p.1 p.2) (fun _ => 0) := by
    funext p
    by_cases hp : p ∈ (Set.univ ×ˢ invSet E a : Set (GA E a × Lie E a))
    · rw [Set.piecewise_eq_of_mem _ _ _ hp]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hp]
      exact dif_neg fun h => hp ⟨Set.mem_univ _, h⟩
  rw [e]
  exact h1.measurable_piecewise continuousOn_const (isOpen_univ.prod isOpen_invSet).measurableSet

theorem measurable_comp_infGL_prod {F : GA E a → ℂ} (hF : Continuous F) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun p : GA E a × X => F (p.1 * infGL E a (γ p.2)) := by
  have h : Measurable fun x => toL (γ x).val := hγ
  have e : (fun p : GA E a × X => F (p.1 * infGL E a (γ p.2))) =
      (fun q : GA E a × Lie E a => chart F q.1 q.2) ∘ fun p : GA E a × X => (p.1, toL (γ p.2).val) :=
    funext fun p => (chart_val F p.1 (γ p.2)).symm
  rw [e]
  exact (measurable_chart_prod hF).comp (measurable_fst.prodMk (h.comp measurable_snd))

theorem measurable_comp_infGL' {F : GA E a → ℂ} (hF : Continuous F) (g : GA E a) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun x => F (g * infGL E a (γ x)) :=
  by
  have h := (measurable_comp_infGL_prod hF hγ).comp (measurable_prodMk_left (x := g) (β := X))
  exact h

theorem integrable_of_isRapidInf {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) : Integrable k ν := by
  have h := hk.2.2 0
  simp only [pow_zero, mul_one] at h
  exact (integrable_norm_iff hk.1.aestronglyMeasurable).1 h

theorem kerInf_mem_bddForms {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) {F : GA E a → ℂ} (h : F ∈ bddForms E a ω) :
    (fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) ∈ bddForms E a ω := by
  obtain ⟨C, hC⟩ := h.2.2.2
  have hki := integrable_of_isRapidInf hk
  refine ⟨?_, fun γ' g => ?_, fun z g => ?_, ∫ x, ‖k x‖ * C ∂ν, fun g => ?_⟩
  · refine continuous_of_dominated (bound := fun x => ‖k x‖ * C)
      (fun g => (hk.1.mul (measurable_comp_infGL' h.1 g hk.2.1)).aestronglyMeasurable)
      (fun g => .of_forall fun x => ?_) (hki.norm.mul_const C)
      (.of_forall fun x => continuous_const.mul (h.1.comp (continuous_id.mul continuous_const)))
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · simp only [mul_assoc, h.2.1]
  · rw [← integral_const_mul]
    beta_reduce
    congr 1; funext x; rw [mul_assoc, h.2.2.1]; ring
  · exact norm_integral_le_of_norm_le (hki.norm.mul_const C)
      (.of_forall fun x => (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)))

section Lemmas

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

theorem pet_kerInf_left (hω : ω.IsUnitary) {X : Type} [MeasurableSpace X] {ν : Measure X} [SFinite ν] {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) {F ψ : GA E a → ℂ}
    (h : F ∈ bddForms E a ω) (h' : ψ ∈ bddForms E a ω) :
    pet (latticeGL E a) μ (fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) ψ =
      ∫ x, k x * pet (latticeGL E a) μ (fun g => F (g * infGL E a (γ x))) ψ ∂ν := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have hD := isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI : IsFiniteMeasure (μ.restrict (stdDom (latticeGL E a))) :=
    ⟨by rw [Measure.restrict_apply_univ, ← quotMeasure_univ hD]; exact measure_lt_top _ _⟩
  obtain ⟨C, hC⟩ := h.2.2.2
  obtain ⟨D, hD'⟩ := h'.2.2.2
  have hki := integrable_of_isRapidInf hk
  have hm : Measurable fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) * conj (ψ p.1) :=
    ((hk.1.comp measurable_snd).mul (measurable_comp_infGL_prod h.1 hk.2.1)).mul
      ((Complex.continuous_conj.comp h'.1).measurable.comp measurable_fst)
  have hi : Integrable (fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) * conj (ψ p.1))
      ((μ.restrict (stdDom (latticeGL E a))).prod ν) := by
    refine ((integrable_const (C * D)).mul_prod hki.norm).mono' hm.aestronglyMeasurable
      (.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, mul_assoc, Complex.norm_conj, mul_comm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hD' _) (norm_nonneg _)
      ((norm_nonneg _).trans (hC 1))) (norm_nonneg _)
  rw [(pet_eq_setIntegral hω (kerInf_mem_bddForms hk h) h' hD).2]
  simp only [← integral_mul_const]
  rw [integral_integral_swap hi]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [(pet_eq_setIntegral hω (mul_right_mem_bddForms h _) h' hD).2, ← integral_const_mul, mul_assoc]

theorem mul_right_mem_mspanR {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ mspanR π) (h : GA E a) :
    (fun g => F (g * h)) ∈ mspanR π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h

theorem mspanR_pet_eq_zero (hω : ω.IsUnitary) {π : CuspSub E a} (hπ : π.HasCentChar ω) (T : Set (GA E a → ℂ))
    (hT : ∀ G ∈ T, G ∈ bddForms E a ω) (hTr : ∀ G ∈ T, ∀ h : GA E a, (fun g => G (g * h)) ∈ T)
    (h0 : ∀ φ ∈ π.V, ∀ G ∈ T, pet (latticeGL E a) μ φ.1 G = 0) {F : GA E a → ℂ} (hF : F ∈ mspanR π) :
    F ∈ bddForms E a ω ∧ ∀ G ∈ T, pet (latticeGL E a) μ F G = 0 := by
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | F ∈ bddForms E a ω ∧ ∀ G ∈ T, pet (latticeGL E a) μ F G = 0}
      add_mem' := fun {F F'} hF hF' => ⟨add_mem hF.1 hF'.1, fun G hG => by
        rw [pet_add_left μ hω hF.1 hF'.1 (hT G hG), hF.2 G hG, hF'.2 G hG, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun G _ => by simp [pet, descend]⟩
      smul_mem' := fun c F hF => ⟨Submodule.smul_mem _ c hF.1, fun G hG => by
        rw [pet_smul_left, hF.2 G hG, mul_zero]⟩ }
  have htr : ∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S := fun F hF h =>
    ⟨mul_right_mem_bddForms hF.1 h, fun G hG => by
      rw [pet_mul_right_left μ hω hF.1 (hT G hG) h]; exact hF.2 _ (hTr G hG h⁻¹)⟩
  refine Submodule.mem_sInf.1 hF S ⟨fun φ hφ => ⟨mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ,
    fun G hG => h0 φ hφ G hG⟩, htr, fun F hF X _ ν _ k γ hk => ⟨kerInf_mem_bddForms hk hF.1, fun G hG => ?_⟩⟩
  rw [pet_kerInf_left μ hω hk hF.1 (hT G hG)]
  exact integral_eq_zero_of_ae (.of_forall fun x => mul_eq_zero_of_right _ ((htr F hF _).2 G hG))

end Lemmas

theorem setIntegral_mspanR_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (π π'' : CuspSub E a) (ω : HChar E), ω.IsUnitary → π.HasCentChar ω → π''.HasCentChar ω →
    ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure],
    (∀ φ ∈ π.V, ∀ φ'' ∈ π''.V, GlobalTheory.AutomorphicL2Unitary.pet (latticeGL E a) μ φ.1 φ''.1 = 0) →
    ∀ 𝓕' : Set (GA E a), IsFundamentalDomain (latticeGL E a) 𝓕' μ →
    ∀ F ∈ GlobalTheory.JSW.mspanR π, ∀ F'' ∈ GlobalTheory.JSW.mspanR π'', ∫ g in 𝓕', F g * starRingEnd ℂ (F'' g) ∂μ = 0 := by
  intro E _ _ _ a _ π π'' ω hω hπ hπ'' μ _ h0 𝓕' h𝓕 F hF F'' hF''
  have hB := GlobalTheory.CuspOrth.cuspFormsBounded
  have base : ∀ φ ∈ π.V, ∀ ψ ∈ π''.V, ∀ h : GA E a, pet (latticeGL E a) μ φ.1 (fun g => ψ.1 (g * h)) = 0 := by
    intro φ hφ ψ hψ h
    have e := pet_mul_right_left μ hω (mem_bddForms_of_cuspSub hB hω hπ hφ) (mem_bddForms_of_cuspSub hB hω hπ'' hψ) h⁻¹
    rw [inv_inv] at e
    rw [← e]
    obtain ⟨y, k, e'⟩ : ∃ y k, h⁻¹ = infGL E a y * finGL E a k := ⟨_, _, (infGL_mul_finGL h⁻¹).symm⟩
    rw [e']
    have H := (GlobalTheory.KeepOrth.pet_eq_zero_of_orthogonal hB E a π π'' ω hω hπ hπ'' μ h0).1 (act (.fin k) φ)
      (π.stable (.fin k) φ hφ) ψ hψ y
    refine Eq.trans (congrArg (fun F => pet (latticeGL E a) μ F ψ.1) (funext fun g => ?_)) H
    show φ.1 (g * (infGL E a y * finGL E a k)) = (act (.fin k) φ).1 (g * infGL E a y)
    rw [← mul_assoc]; rfl
  have A1 := fun {F} (hF : F ∈ mspanR π) => mspanR_pet_eq_zero μ hω hπ
    {G | ∃ ψ ∈ π''.V, ∃ h : GA E a, G = fun g => ψ.1 (g * h)}
    (by rintro _ ⟨ψ, hψ, h, rfl⟩; exact mul_right_mem_bddForms (mem_bddForms_of_cuspSub hB hω hπ'' hψ) h)
    (by rintro _ ⟨ψ, hψ, h, rfl⟩ k; exact ⟨ψ, hψ, k * h, funext fun g => by simp only [mul_assoc]⟩)
    (by rintro φ hφ _ ⟨ψ, hψ, h, rfl⟩; exact base φ hφ ψ hψ h) hF
  have A2 := fun {G} (hG : G ∈ mspanR π'') => mspanR_pet_eq_zero μ hω hπ'' (mspanR π : Set (GA E a → ℂ))
    (fun F hF => (A1 hF).1) (fun F hF h => mul_right_mem_mspanR hF h)
    (fun ψ hψ F hF => by
      rw [← conj_pet, (A1 hF).2 _ ⟨ψ, hψ, 1, funext fun g => by rw [mul_one]⟩, map_zero]) hG
  obtain ⟨bF'', h2⟩ := A2 hF''
  rw [← (pet_eq_setIntegral hω (A1 hF).1 bF'' h𝓕).2, ← conj_pet, h2 F hF, map_zero]

end GlobalTheory.MspanROrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralSmoothSpanEqToRealLint
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.RSPoleToc

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem eq_ofReal_norm {z : ℂ} (h1 : 0 ≤ z.re) (h2 : z.im = 0) : z = ((‖z‖ : ℝ) : ℂ) := by
  have hz : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h2])
  rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1]

theorem rsPsi_self_eq (ℓ : Fin a) (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ)
    (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (g : GA E a)
    (y : Fin a → Ad E) :
    GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g y = ((‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g y‖ : ℝ) : ℂ) := by
  set u : Fin a → Cinf E := fun i => pInf E (y i)
  set w := g * (infGL E a (GlobalTheory.RSTheta.rowGL ℓ u))⁻¹
  set s : ℝ := (GlobalTheory.ThetaPoisson.latt a J).indicator 1 ((fun i => pFin E (y i)) - η)
  have hs : (GlobalTheory.ThetaPoisson.latt a J).indicator (1 : (Fin a → Af E) → ℂ) ((fun i => pFin E (y i)) - η) = (s : ℂ) := by
    classical
    simp only [s]; rw [Set.indicator_apply, Set.indicator_apply]; split_ifs <;> simp
  have hs0 : 0 ≤ s := Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hΦu : Φ u = (((Φ u).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [(hΦ u).2])
  have e : GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g y = ((Complex.normSq (F w) * (Φ u).re * s : ℝ) : ℂ) := by
    simp only [GlobalTheory.RSTheta.rsPsi, GlobalTheory.ThetaPoisson.thetaFn, GlobalTheory.RSTheta.rsInf]
    rw [hs, Complex.mul_conj, hΦu]
    push_cast
    rfl
  refine eq_ofReal_norm ?_ ?_
  · rw [e, Complex.ofReal_re]
    exact mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) (hΦ u).1) hs0
  · rw [e, Complex.ofReal_im]

theorem tsum_eq_toReal {ι : Type} (f : ι → ℂ) (hf : ∀ i, f i = ((‖f i‖ : ℝ) : ℂ)) :
    ∑' i, f i = (((∑' i, ‖f i‖ₑ).toReal : ℝ) : ℂ) := by
  rw [ENNReal.tsum_toReal_eq fun _ => enorm_ne_top, Complex.ofReal_tsum]
  exact tsum_congr fun i => by rw [toReal_enorm, ← hf i]

theorem thetaZ_eq_toReal (ℓ : Fin a) (F : GA E a → ℂ) (hF : Continuous F) (Φ : (Fin a → Cinf E) → ℂ)
    (hΦc : Continuous Φ) (hΦs : tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ) (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) (𝓕 : Set (GA E a)) (x : ℝ)
    (hfin : ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) *
        ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ ≠ ⊤) :
    GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ F F Φ J η x = (((∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
                 ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) *
                 ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ).toReal : ℝ) : ℂ) := by
  set G : GA E a → ℝ≥0∞ := fun g => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) *
        ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) with hG

  have hcont : ∀ ξ : {ξ : Fin a → E // ξ ≠ 0}, Continuous fun g : GA E a => GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g
      ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val) := by
    intro ξ
    have h1 : Continuous fun g : GA E a =>
        (g, (fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g.val : Matrix (Fin a) (Fin a) (Ad E))) :=
      continuous_id.prodMk (continuous_const.matrix_vecMul Units.continuous_val)
    have h2 := GlobalTheory.RSTheta.continuous_rsPsi hF hF hΦc hΦs J η
    have h3 := h2.comp h1
    exact h3
  have hdet : Continuous fun g : GA E a => ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) := by
    have h : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
      continuous_subtype_val.comp (continuous_ideleModule.comp (GroundTheory.Automorphic.AdelicGLn.continuous_det E a))
    exact h.rpow_const fun g => Or.inl (ideleModule E (GeneralLinearGroup.det g)).2.ne'
  have hGm : Measurable G := by
    refine Measurable.mul ?_ (ENNReal.measurable_ofReal.comp hdet.measurable)
    exact (lowerSemicontinuous_tsum fun ξ => (hcont ξ).enorm.lowerSemicontinuous).measurable

  have hpt : ∀ g : GA E a, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g
      ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
      ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) = (((G g).toReal : ℝ) : ℂ) := by
    intro g
    rw [tsum_eq_toReal _ fun ξ => rsPsi_self_eq ℓ F Φ hΦ J η g _, hG]
    simp only
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (Real.rpow_nonneg (ideleModule E (GeneralLinearGroup.det g)).2.le x), Complex.ofReal_mul]
  have hae : ∀ᵐ g ∂μ.restrict 𝓕, G g < ⊤ := ae_lt_top hGm hfin
  calc GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ F F Φ J η x = ∫ g in 𝓕, (((G g).toReal : ℝ) : ℂ) ∂μ := by
        rw [GlobalTheory.RSPole.thetaZ]; exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ((∫ g in 𝓕, (G g).toReal ∂μ : ℝ) : ℂ) := integral_ofReal
    _ = _ := by rw [integral_toReal hGm.aemeasurable hae]

theorem thetaZ_eq_toReal_lintegral : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (π : CuspSub E a)
    (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π → Continuous F →
    ∀ (Φ : (Fin a → Cinf E) → ℂ), Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ x : ℝ,
    ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ ≠ ⊤ →
    GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ F F Φ J η x = (((∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ).toReal : ℝ) : ℂ) := by
  intro E _ _ _ a ℓ π F _ hF Φ hΦc hΦs hΦ J η μ _ 𝓕 _ x hfin
  exact thetaZ_eq_toReal ℓ F hF Φ hΦc hΦs hΦ J η μ 𝓕 x hfin

end GlobalTheory.RSPoleToc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidKernelIntegralConjLieDerivativeMemSpan
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MSpanDecay.RapidLie

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

theorem norm_entry_le (A : Matrix (Fin a) (Fin a) (Cinf E)) (i j : Fin a) : ‖A i j‖ ≤ ‖toL A‖ :=
  (norm_le_pi_norm (toL A i) j).trans (norm_le_pi_norm (toL A) i)

omit [IsTotallyComplex E] in

theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL (A * B)‖ ≤ a * (‖toL A‖ * ‖toL B‖) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL A‖ * ‖toL B‖) fun k _ => ?_).trans ?_)
  · exact (norm_mul_le _ _).trans (mul_le_mul (norm_entry_le A i k) (norm_entry_le B k j) (norm_nonneg _) (norm_nonneg _))
  · simp

omit [IsTotallyComplex E] in

theorem measurable_comp_of_continuousOn {X : Type} [MeasurableSpace X] {f : Lie E a → ℂ}
    (hf : ContinuousOn f (invSet E a)) {φ : X → Lie E a} (hφ : Measurable φ) (hφ' : ∀ x, φ x ∈ invSet E a) :
    Measurable fun x => f (φ x) := by
  have e : (fun x => f (φ x)) = (invSet E a).restrict f ∘ fun x => (⟨φ x, hφ' x⟩ : invSet E a) := rfl
  rw [e]
  exact hf.restrict.measurable.comp (hφ.subtype_mk)

omit [IsTotallyComplex E] in

theorem measurable_inv {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (hγ : Measurable fun x => toL (γ x).val) : Measurable fun x => toL ((γ x)⁻¹).val := by
  have key : ∀ y : GL (Fin a) (Cinf E), ((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) =
      (fun w => ((y : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹) • (y : Matrix (Fin a) (Fin a) (Cinf E)).adjugate := by
    intro y
    refine Units.inv_eq_of_mul_eq_one_left ?_
    have hu : IsUnit (y : Matrix (Fin a) (Fin a) (Cinf E)).det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    have h1 : (fun w => ((y : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹) * (y : Matrix (Fin a) (Fin a) (Cinf E)).det = 1 := by
      funext w
      have hw : (y : Matrix (Fin a) (Fin a) (Cinf E)).det w ≠ 0 :=
        ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).isUnit_map hu).ne_zero
      exact inv_mul_cancel₀ hw
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, h1, one_smul]
  have e : (fun x => toL ((γ x)⁻¹).val) = fun x => toL ((fun w => ((γ x : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹) •
      (γ x : Matrix (Fin a) (Fin a) (Cinf E)).adjugate) := funext fun x => congrArg toL (key (γ x))
  rw [e]
  have hdet : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)).det :=
    (contDiff_det (E := E) (a := a)).continuous.measurable.comp hγ
  have hadjc : Continuous fun m : Lie E a => (toL (Matrix.of m).adjugate : Lie E a) :=
    Continuous.matrix_adjugate continuous_id
  have hadj : Measurable fun x => toL (γ x : Matrix (Fin a) (Fin a) (Cinf E)).adjugate :=
    hadjc.measurable.comp hγ
  have hc : Measurable fun x => (fun w => ((γ x : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹ : Cinf E) :=
    measurable_pi_lambda _ fun w => ((measurable_pi_apply w).comp hdet).inv
  exact (continuous_smul (M := Cinf E) (X := Lie E a)).measurable.comp (hc.prodMk hadj)

end GlobalTheory.MSpanDecay.RapidLie

namespace GlobalTheory.MSpanDecay.RapidLie

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem measurable_mul {X : Type} [MeasurableSpace X] {A B : X → Lie E a} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => toL (Matrix.of (A x) * Matrix.of (B x)) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun w => ?_
  have e : (fun x => toL (Matrix.of (A x) * Matrix.of (B x)) i j w) = fun x => ∑ k, A x i k w * B x k j w := by
    funext x; simp [Matrix.mul_apply, Finset.sum_apply]
  rw [e]
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply w).comp ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hA))).mul
      ((measurable_pi_apply w).comp ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hB)))

theorem measurable_conj {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (hγ : Measurable fun x => toL (γ x).val) (Y : Lie E a) :
    Measurable fun x => toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val) :=
  measurable_mul (measurable_mul (measurable_inv hγ) measurable_const) hγ

end GlobalTheory.MSpanDecay.RapidLie

namespace GlobalTheory.MSpanDecay.RapidLie

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

theorem norm_conj_le (y : GL (Fin a) (Cinf E)) (Y : Lie E a) :
    ‖toL ((y⁻¹).val * Matrix.of Y * y.val)‖ ≤ a * a * ‖Y‖ * height y ^ 2 := by
  have h1 : ‖toL y.val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have h2 : ‖toL (y⁻¹).val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL y.val)]
  have h3 : ‖toL ((y⁻¹).val * Matrix.of Y)‖ ≤ a * (‖toL (y⁻¹).val‖ * ‖Y‖) := norm_toL_mul_le _ _
  calc ‖toL ((y⁻¹).val * Matrix.of Y * y.val)‖ ≤ a * (‖toL ((y⁻¹).val * Matrix.of Y)‖ * ‖toL y.val‖) :=
        norm_toL_mul_le _ _
    _ ≤ a * ((a * (height y * ‖Y‖)) * height y) := by
        have h4 : ‖toL ((y⁻¹).val * Matrix.of Y)‖ ≤ a * (height y * ‖Y‖) :=
          h3.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) (Nat.cast_nonneg a))
        exact mul_le_mul_of_nonneg_left (mul_le_mul h4 h1 (norm_nonneg _) ((norm_nonneg _).trans h4)) (Nat.cast_nonneg a)
    _ = a * a * ‖Y‖ * height y ^ 2 := by ring

theorem lieD_eq_sum {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (Lie E a)) (W : Lie E a) (G : GA E a → ℂ)
    (g : GA E a) : lieD W G g = ∑ j, ((b.repr W j : ℝ) : ℂ) * lieD (b j) G g := by
  unfold lieD
  conv_lhs => rw [← b.sum_repr W]
  rw [map_sum]
  simp only [map_smul, Complex.real_smul]

theorem measurable_height {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (hγ : Measurable fun x => toL (γ x).val) : Measurable fun x => height (γ x) := by
  have e : (fun x => height (γ x)) = fun x => 1 + ‖toL (γ x).val‖ + ‖toL ((γ x)⁻¹).val‖ := rfl
  rw [e]
  exact (measurable_const.add hγ.norm).add (measurable_inv hγ).norm

end GlobalTheory.MSpanDecay.RapidLie

namespace GlobalTheory.MSpanDecay

open RapidLie in

theorem integral_lieD_conj_mem_kSpan : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (G : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (Y : Lie E a), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Good G → (fun g : GA E a => ∫ x, k x * lieD (toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)) G (g * infGL E a (γ x)) ∂ν) ∈ GlobalTheory.MSpanDecay.kSpan E a := by
  intro E _ _ _ a G X _ ν _ k γ Y hk hG
  obtain ⟨hkm, hγm, hint⟩ := hk
  have hγ : Measurable fun x => toL (γ x).val := hγm
  let b := Module.finBasis ℝ (Lie E a)
  let L : Fin (Module.finrank ℝ (Lie E a)) → Lie E a →L[ℝ] ℝ := fun j => LinearMap.toContinuousLinearMap (b.coord j)
  let W : X → Lie E a := fun x => toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)
  let c : Fin (Module.finrank ℝ (Lie E a)) → X → ℂ := fun j x => ((L j (W x) : ℝ) : ℂ)
  have hW : Measurable W := measurable_conj hγ Y
  have hc : ∀ j, Measurable (c j) := fun j => Complex.measurable_ofReal.comp ((L j).continuous.measurable.comp hW)
  set D : Fin (Module.finrank ℝ (Lie E a)) → ℝ := fun j => ‖L j‖ * (a * a * ‖Y‖) with hD
  have hD0 : ∀ j, 0 ≤ D j := fun j => by positivity
  have hcb : ∀ j x, ‖c j x‖ ≤ D j * height (γ x) ^ 2 := by
    intro j x
    have h := (L j).le_opNorm (W x)
    rw [Complex.norm_real]
    refine h.trans ?_
    rw [hD, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_conj_le (γ x) Y) (norm_nonneg _)
  have hG' : ∀ j, Good (lieD (b j) G) := fun j => hG.derivative _
  have hrap : ∀ j, GlobalTheory.JSW.IsRapidInf ν (fun x => k x * c j x) γ := by
    intro j
    refine ⟨hkm.mul (hc j), hγm, fun N => ?_⟩
    refine Integrable.mono' ((hint (N + 2)).const_mul (D j))
      (((hkm.mul (hc j)).norm.mul ((measurable_height hγ).pow_const N)).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    have h1 := one_le_height (γ x)
    have hp : 0 ≤ height (γ x) ^ N := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
    calc ‖k x‖ * ‖c j x‖ * height (γ x) ^ N ≤ ‖k x‖ * (D j * height (γ x) ^ 2) * height (γ x) ^ N := by
          gcongr; exact hcb j x
      _ = D j * (‖k x‖ * height (γ x) ^ (N + 2)) := by ring
  have hmeasG : ∀ j g, Measurable fun x => lieD (b j) G (g * infGL E a (γ x)) := by
    intro j g
    have e : (fun x => lieD (b j) G (g * infGL E a (γ x))) = fun x => chart (lieD (b j) G) g (toL (γ x).val) :=
      funext fun x => (chart_val _ g (γ x)).symm
    rw [e]
    exact measurable_comp_of_continuousOn (((hG' j).mem_Sm g).continuousOn) hγ fun x => val_mem_invSet (γ x)
  have hintj : ∀ j g, Integrable (fun x => k x * c j x * lieD (b j) G (g * infGL E a (γ x))) ν := by
    intro j g
    obtain ⟨C, N, hCN⟩ := (hG' j).growth g
    refine Integrable.mono' ((hint (N + 2)).const_mul (D j * |C|))
      (((hkm.mul (hc j)).mul (hmeasG j g)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    have h1 := one_le_height (γ x)
    have hp : 0 ≤ height (γ x) ^ N := by positivity
    have hg : ‖lieD (b j) G (g * infGL E a (γ x))‖ ≤ |C| * height (γ x) ^ N :=
      (hCN (γ x)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)
    rw [norm_mul, norm_mul]
    calc ‖k x‖ * ‖c j x‖ * ‖lieD (b j) G (g * infGL E a (γ x))‖
        ≤ ‖k x‖ * (D j * height (γ x) ^ 2) * (|C| * height (γ x) ^ N) := by
          gcongr
          · exact hcb j x
      _ = D j * |C| * (‖k x‖ * height (γ x) ^ (N + 2)) := by ring
  have e : (fun g : GA E a => ∫ x, k x * lieD (toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)) G
      (g * infGL E a (γ x)) ∂ν) =
      ∑ j, fun g : GA E a => ∫ x, k x * c j x * lieD (b j) G (g * infGL E a (γ x)) ∂ν := by
    funext g
    rw [Finset.sum_apply, ← integral_finset_sum _ fun j _ => hintj j g]
    congr 1
    funext x
    rw [lieD_eq_sum b, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (mul_assoc (k x) (c j x) _).symm
  rw [e]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨X, inferInstance, ν, inferInstance, _, γ, _, hrap j, hG' j, rfl⟩

end GlobalTheory.MSpanDecay
end
end

