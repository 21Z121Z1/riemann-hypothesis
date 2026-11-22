import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0007
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0010
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0011
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MobiusChangeOfVariablesPair
section
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq

variable (g : Matrix (Fin 2) (Fin 2) ℂ)

def dom : Set ℂ := {a | den g a ≠ 0}

def cod : Set ℂ := {b | g 1 1 - g 0 1 * b ≠ 0}

variable {g}

theorem det_eq : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g

theorem isOpen_dom : IsOpen (dom g) := by
  have hc : Continuous fun a : ℂ => GlobalTheory.CompanionTheory.Ar.PB.FibPt.den g a := by
    show Continuous fun a : ℂ => g 0 0 + g 0 1 * a
    fun_prop
  exact isOpen_ne_fun hc continuous_const

theorem hasDerivAt_mob {a : ℂ} (ha : a ∈ dom g) : HasDerivAt (mob g) (mobD g a) a := by
  have hden : g 0 0 + g 0 1 * a ≠ 0 := ha
  have h1 : HasDerivAt (fun z : ℂ => g 1 0 + g 1 1 * z) (g 1 1) a := by
    simpa using ((hasDerivAt_id a).const_mul (g 1 1)).const_add (g 1 0)
  have h2 : HasDerivAt (fun z : ℂ => g 0 0 + g 0 1 * z) (g 0 1) a := by
    simpa using ((hasDerivAt_id a).const_mul (g 0 1)).const_add (g 0 0)
  have h := h1.div h2 hden
  have heq : GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g
      = (fun z : ℂ => g 1 0 + g 1 1 * z) / (fun z : ℂ => g 0 0 + g 0 1 * z) := by
    funext z
    rfl
  have hval : GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g a
      = (g 1 1 * (g 0 0 + g 0 1 * a) - (g 1 0 + g 1 1 * a) * g 0 1) / (g 0 0 + g 0 1 * a) ^ 2 := by
    rw [show GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g a = g.det / (g 0 0 + g 0 1 * a) ^ 2 from rfl,
      GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq]
    ring
  rw [heq, hval]
  exact h

theorem injOn_mob (hg : IsUnit g.det) : Set.InjOn (mob g) (dom g) := by
  intro a ha b hb hab
  have ha' : g 0 0 + g 0 1 * a ≠ 0 := ha
  have hb' : g 0 0 + g 0 1 * b ≠ 0 := hb
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
    rw [← GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq]
    exact hg.ne_zero
  have h : (g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)
      = (g 1 0 + g 1 1 * b) / (g 0 0 + g 0 1 * b) := hab
  rw [div_eq_div_iff ha' hb'] at h
  have h2 : (g 0 0 * g 1 1 - g 0 1 * g 1 0) * (a - b) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 hdet
  · exact sub_eq_zero.1 h3

theorem image_mob (hg : IsUnit g.det) : mob g '' dom g = cod g := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
    rw [← GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq]
    exact hg.ne_zero
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : g 0 0 + g 0 1 * a ≠ 0 := ha
    show g 1 1 - g 0 1 * ((g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)) ≠ 0
    have hval : g 1 1 - g 0 1 * ((g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a))
        = (g 0 0 * g 1 1 - g 0 1 * g 1 0) / (g 0 0 + g 0 1 * a) := by
      field_simp
      ring
    rw [hval]
    exact div_ne_zero hdet ha'
  · intro hb
    have hb' : g 1 1 - g 0 1 * b ≠ 0 := hb
    have hx : (g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b) * (g 1 1 - g 0 1 * b)
        = g 0 0 * b - g 1 0 := div_mul_cancel₀ _ hb'
    have hden : g 0 0 + g 0 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b))
        = (g 0 0 * g 1 1 - g 0 1 * g 1 0) / (g 1 1 - g 0 1 * b) := by
      rw [eq_div_iff hb']
      linear_combination g 0 1 * hx
    have hnum : g 1 0 + g 1 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b))
        = b * (g 0 0 * g 1 1 - g 0 1 * g 1 0) / (g 1 1 - g 0 1 * b) := by
      rw [eq_div_iff hb']
      linear_combination g 1 1 * hx
    refine ⟨(g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b), ?_, ?_⟩
    · show g 0 0 + g 0 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b)) ≠ 0
      rw [hden]
      exact div_ne_zero hdet hb'
    · show (g 1 0 + g 1 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b))) /
          (g 0 0 + g 0 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b))) = b
      rw [hnum, hden, div_div_div_cancel_right₀ hb', mul_div_assoc, div_self hdet, mul_one]

theorem null_affine {c d : ℂ} (h : c ≠ 0 ∨ d ≠ 0) : volume {a : ℂ | c + d * a = 0} = 0 := by
  refine Set.Subsingleton.measure_zero ?_ _
  intro x hx y hy
  have hx' : c + d * x = 0 := hx
  have hy' : c + d * y = 0 := hy
  have hd : d ≠ 0 := by
    rintro rfl
    rcases h with hc | hd
    · exact hc (by simpa using hx')
    · exact hd rfl
  have hxy : d * (x - y) = 0 := by
    linear_combination hx' - hy'
  exact sub_eq_zero.1 ((mul_eq_zero.1 hxy).resolve_left hd)

theorem ae_prod_self {V : Set ℂ} (hV : volume Vᶜ = 0) :
    (V ×ˢ V : Set (ℂ × ℂ)) =ᵐ[(volume : Measure (ℂ × ℂ))] (Set.univ : Set (ℂ × ℂ)) := by
  rw [ae_eq_univ]
  have h1 : (volume : Measure (ℂ × ℂ)) (Prod.fst ⁻¹' Vᶜ) = 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.preimage_null hV
  have h2 : (volume : Measure (ℂ × ℂ)) (Prod.snd ⁻¹' Vᶜ) = 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.preimage_null hV
  refine measure_mono_null (fun p hp => ?_) (measure_union_null h1 h2)
  simp only [Set.mem_compl_iff, Set.mem_prod, not_and_or] at hp
  simpa only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff] using hp

theorem null_dom (hg : IsUnit g.det) : volume (dom g)ᶜ = 0 := by
  have hne : g 0 0 ≠ 0 ∨ g 0 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hg.ne_zero
    rw [GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq, h.1, h.2]
    ring
  refine measure_mono_null (fun a ha => ?_) (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.null_affine hne)
  have ha' : ¬ (g 0 0 + g 0 1 * a ≠ 0) := ha
  exact not_not.1 ha'

theorem null_cod (hg : IsUnit g.det) : volume (cod g)ᶜ = 0 := by
  have hne : g 1 1 ≠ 0 ∨ -g 0 1 ≠ 0 := by
    by_contra h
    push_neg at h
    have h01 : g 0 1 = 0 := neg_eq_zero.1 h.2
    apply hg.ne_zero
    rw [GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq, h.1, h01]
    ring
  refine measure_mono_null (fun b hb => ?_) (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.null_affine hne)
  have hb' : ¬ (g 1 1 - g 0 1 * b ≠ 0) := hb
  show g 1 1 + -g 0 1 * b = 0
  linear_combination not_not.1 hb'

theorem det_smul_one (z : ℂ) :
    LinearMap.det ((z • (1 : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = Complex.normSq z := by
  have hmul : ((z • (1 : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = Algebra.lmul ℝ ℂ z := by
    refine LinearMap.ext fun w => ?_
    rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    simp
  rw [hmul, ← Algebra.norm_apply, Algebra.norm_complex_apply]

theorem det_prodMap (z w : ℂ) :
    ((z • (1 : ℂ →L[ℝ] ℂ)).prodMap (w • (1 : ℂ →L[ℝ] ℂ))).det
      = Complex.normSq z * Complex.normSq w := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap,
    GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_smul_one, GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_smul_one]

theorem integral_mob_sq (hg : IsUnit g.det) (f : ℂ × ℂ → ℝ) :
    ∫ p : ℂ × ℂ, (Complex.normSq (mobD g p.1) * Complex.normSq (mobD g p.2)) * f (mob g p.1, mob g p.2)
      = ∫ q : ℂ × ℂ, f q := by
  haveI : Measure.IsAddHaarMeasure (volume : Measure (ℂ × ℂ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hUo : IsOpen (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g) := GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.isOpen_dom
  have hUm : MeasurableSet (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g ×ˢ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g) :=
    hUo.measurableSet.prod hUo.measurableSet
  have hderiv : ∀ p ∈ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g ×ˢ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g,
      HasFDerivWithinAt (Prod.map (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g) (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g))
        ((GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.1 • (1 : ℂ →L[ℝ] ℂ)).prodMap
          (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.2 • (1 : ℂ →L[ℝ] ℂ)))
        (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g ×ˢ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g) p := by
    intro p hp
    exact (HasFDerivAt.prodMap p
      (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.hasDerivAt_mob hp.1).complexToReal_fderiv
      (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.hasDerivAt_mob hp.2).complexToReal_fderiv).hasFDerivWithinAt
  have hinj : Set.InjOn (Prod.map (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g) (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g))
      (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g ×ˢ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g) := by
    intro p hp q hq hpq
    exact Prod.ext (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.injOn_mob hg hp.1 hq.1 (congrArg Prod.fst hpq))
      (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.injOn_mob hg hp.2 hq.2 (congrArg Prod.snd hpq))
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hUm hderiv hinj f
  rw [Set.prodMap_image_prod, GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.image_mob hg,
    setIntegral_congr_set (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.ae_prod_self (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.null_cod hg)),
    setIntegral_congr_set (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.ae_prod_self (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.null_dom hg)),
    setIntegral_univ, setIntegral_univ] at hcv
  rw [hcv]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_prodMap, Prod.map_apply, smul_eq_mul]
  rw [abs_of_nonneg (mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]
  rfl

end GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_mob_sq_main :
    ∀ (g : Matrix (Fin 2) (Fin 2) ℂ), IsUnit g.det → ∀ f : ℂ × ℂ → ℝ, ∫ p : ℂ × ℂ, (Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.1) * Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.2)) * f (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g p.1, GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g p.2) = ∫ q : ℂ × ℂ, f q :=
  fun _ hg f => GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.integral_mob_sq hg f
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MobiusPairAnalyticDetJacobianEq
section
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem det_eq_mul_minor_of_col_zero {n : ℕ} (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (h : ∀ i : Fin n, J i.succ 0 = 0) : J.det = J 0 0 * (J.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h]

theorem hasDerivAt_mob_line (G : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) (h : den G a ≠ 0) :
    HasDerivAt (fun t : ℂ => mob G (a + t)) (mobD G a) 0 := by
  have hl : HasDerivAt (fun t : ℂ => a + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_add a
  have hn : HasDerivAt (fun t : ℂ => G 1 0 + G 1 1 * (a + t)) (G 1 1) 0 := by
    simpa using (hl.const_mul (G 1 1)).const_add (G 1 0)
  have hd : HasDerivAt (fun t : ℂ => den G (a + t)) (G 0 1) 0 := by
    simpa [den] using (hl.const_mul (G 0 1)).const_add (G 0 0)
  have h0 : den G (a + 0) ≠ 0 := by simpa using h
  have key := hn.div hd h0
  have e : mobD G a = (G 1 1 * den G (a + 0) - (G 1 0 + G 1 1 * (a + 0)) * G 0 1) / den G (a + 0) ^ 2 := by
    simp only [add_zero]
    unfold mobD
    rw [Matrix.det_fin_two]
    congr 1
    unfold den
    ring
  rw [e]
  exact key

theorem jacC_apply_of_line {D E : ℕ} (F : (Fin D → ℂ) → Fin E → ℂ) (z : Fin D → ℂ)
    (hF : DifferentiableAt ℂ F z) (a : Fin E) (k : Fin D) (c : ℂ)
    (h : HasDerivAt (fun t : ℂ => F (z + t • (Pi.single k 1 : Fin D → ℂ)) a) c 0) :
    ReciprocityTheory.AnForm.A.jacC F z a k = c := by
  have hl : HasDerivAt (fun t : ℂ => z + t • (Pi.single k 1 : Fin D → ℂ)) (Pi.single k 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single k 1 : Fin D → ℂ)).const_add z
  have hF' : HasFDerivAt F (fderiv ℂ F z) (z + (0 : ℂ) • (Pi.single k 1 : Fin D → ℂ)) := by
    simpa using hF.hasFDerivAt
  have h2 := hF'.comp_hasDerivAt (0 : ℂ) hl
  have h3 := (hasDerivAt_pi.1 h2) a
  exact h3.unique h

theorem mobius_pair_line_first_axis {d : ℕ} (y : Fin d → ℂ) (a₀ a₁ t : ℂ) :
    (Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ) + t • (Pi.single 0 1 : Fin (d + 2) → ℂ) =
      Fin.cons (a₀ + t) (Fin.cons a₁ y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Pi.single_apply, Fin.succ_ne_zero]

theorem mobius_pair_line_second_axis {d : ℕ} (y : Fin d → ℂ) (a₀ a₁ t : ℂ) :
    (Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ) + t • (Pi.single 1 1 : Fin (d + 2) → ℂ) =
      Fin.cons a₀ (Fin.cons (a₁ + t) y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Pi.single_apply]
  · refine Fin.cases ?_ (fun l => ?_) j
    · simp [Pi.single_apply]
    · have : (l.succ.succ : Fin (d + 2)) ≠ 1 := by
        intro h
        have := congrArg Fin.val h
        simp at this
      simp [Pi.single_apply, this]

theorem mobius_pair_cons {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ) (b₀ b₁ : ℂ) :
    mob2 g (Fin.cons b₀ (Fin.cons b₁ y)) = Fin.cons (mob (g y) b₀) (Fin.cons (mob (g y) b₁) y) := rfl

theorem analyticAt_mobius_pair {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (y : Fin d → ℂ) (a₀ a₁ : ℂ)
    (h₀ : den (g y) a₀ ≠ 0) (h₁ : den (g y) a₁ ≠ 0) :
    AnalyticAt ℂ (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) := by
  set z₀ : Fin (d + 2) → ℂ := Fin.cons a₀ (Fin.cons a₁ y) with hz₀
  have hcoord : ∀ i : Fin (d + 2), AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => z i) z₀ := fun i =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 2) => ℂ) i).analyticAt z₀
  have hT : AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => Fin.tail (Fin.tail z)) z₀ := by
    rw [analyticAt_pi_iff]
    intro i
    exact hcoord i.succ.succ
  have hTz : Fin.tail (Fin.tail z₀) = y := by
    simp [hz₀]
  have hga : ∀ p q, AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => g (Fin.tail (Fin.tail z)) p q) z₀ := by
    intro p q
    have h1 : AnalyticAt ℂ (fun y' => g y' p q) (Fin.tail (Fin.tail z₀)) :=
      ReciprocityTheory.AnForm.Osgood.osgood d Set.univ _ isOpen_univ (hg p q).differentiableOn _ (Set.mem_univ _)
    exact AnalyticAt.comp (f := fun z : Fin (d + 2) → ℂ => Fin.tail (Fin.tail z)) h1 hT
  have hm : ∀ i : Fin (d + 2), den (g y) (z₀ i) ≠ 0 →
      AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => mob (g (Fin.tail (Fin.tail z))) (z i)) z₀ := by
    intro i hi
    unfold mob den
    refine AnalyticAt.div ?_ ?_ ?_
    · exact (hga 1 0).add ((hga 1 1).mul (hcoord i))
    · exact (hga 0 0).add ((hga 0 1).mul (hcoord i))
    · rw [hTz]
      exact hi
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hm 0 (by simpa [hz₀] using h₀)
  · refine Fin.cases ?_ (fun l => ?_) j
    · exact hm 1 (by simpa [hz₀] using h₁)
    · exact hcoord l.succ.succ

theorem det_jacobian_mobius_pair {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (y : Fin d → ℂ) (a₀ a₁ : ℂ)
    (h₀ : den (g y) a₀ ≠ 0) (h₁ : den (g y) a₁ ≠ 0) :
    (ReciprocityTheory.AnForm.A.jacC (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y))).det =
      mobD (g y) a₀ * mobD (g y) a₁ := by
  have hdiff : DifferentiableAt ℂ (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) :=
    (analyticAt_mobius_pair g hg y a₀ a₁ h₀ h₁).differentiableAt
  set J := ReciprocityTheory.AnForm.A.jacC (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) with hJ
  have hJ00 : J 0 0 = mobD (g y) a₀ := by
    refine jacC_apply_of_line _ _ hdiff 0 0 _ ?_
    simp only [mobius_pair_line_first_axis, mobius_pair_cons]
    simpa using hasDerivAt_mob_line (g y) a₀ h₀
  have hJ11 : J 1 1 = mobD (g y) a₁ := by
    refine jacC_apply_of_line _ _ hdiff 1 1 _ ?_
    simp only [mobius_pair_line_second_axis, mobius_pair_cons]
    simpa using hasDerivAt_mob_line (g y) a₁ h₁
  have hJ10 : J 1 0 = 0 := by
    refine jacC_apply_of_line _ _ hdiff 1 0 _ ?_
    simp only [mobius_pair_line_first_axis, mobius_pair_cons]
    simpa using hasDerivAt_const (0 : ℂ) (mob (g y) a₁)
  have hJss : ∀ (i : Fin d) (k : Fin (d + 2)), J i.succ.succ k = (Pi.single k 1 : Fin (d + 2) → ℂ) i.succ.succ := by
    intro i k
    refine jacC_apply_of_line _ _ hdiff _ _ _ ?_
    have e : (fun t : ℂ => mob2 g ((Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ) +
        t • (Pi.single k 1 : Fin (d + 2) → ℂ)) i.succ.succ) =
        fun t : ℂ => y i + t * (Pi.single k 1 : Fin (d + 2) → ℂ) i.succ.succ := by
      funext t
      simp [mob2, Fin.tail]
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const ((Pi.single k 1 : Fin (d + 2) → ℂ) i.succ.succ)).const_add (y i)
  have hc0 : ∀ i : Fin (d + 1), J i.succ 0 = 0 := by
    intro i
    refine Fin.cases ?_ (fun l => ?_) i
    · exact hJ10
    · rw [hJss]
      simp [Pi.single_apply, Fin.succ_ne_zero]
  have hc1 : ∀ i : Fin d, (J.submatrix Fin.succ Fin.succ) i.succ 0 = 0 := by
    intro i
    simp only [Matrix.submatrix_apply]
    rw [hJss]
    have : (i.succ.succ : Fin (d + 2)) ≠ 1 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [Pi.single_apply, this]
  have hlast : ((J.submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ) = 1 := by
    ext i j
    simp only [Matrix.submatrix_apply]
    rw [hJss]
    simp [Pi.single_apply, Matrix.one_apply]
  rw [det_eq_mul_minor_of_col_zero J hc0, det_eq_mul_minor_of_col_zero _ hc1, hlast, Matrix.det_one, mul_one,
    hJ00]
  simp only [Matrix.submatrix_apply]
  congr 1

theorem mobius_pair_analyticAt_and_det_jacobian : ∀ (d : ℕ) (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ p q, Differentiable ℂ fun y' => g y' p q) → ∀ (y : Fin d → ℂ) (a₀ a₁ : ℂ),
    GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₀ ≠ 0 → GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₁ ≠ 0 →
    AnalyticAt ℂ (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) ∧
    (ReciprocityTheory.AnForm.A.jacC (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob2 g) (Fin.cons a₀ (Fin.cons a₁ y))).det =
      GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₀ * GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₁ :=
  fun _ g hg y a₀ a₁ h₀ h₁ => ⟨analyticAt_mobius_pair g hg y a₀ a₁ h₀ h₁, det_jacobian_mobius_pair g hg y a₀ a₁ h₀ h₁⟩

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnOfChartCompositionStatement
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOn_of_chart_composition : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (G : (Fin e → ℂ) → ℝ), IsCompatChart A ψ → IsOpen O → O ⊆ ψ.target → ContDiffOn ℝ ∞ G O → A.SmoothOn (ψ.source ∩ ψ ⁻¹' O) (G ∘ ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' | exact GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' | (intros; apply GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncBoundaryCoordinateChartStatement
section
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_boundary_coordinate_chart : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → ∀ x, ∃ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∃ S : Finset (Fin e), ∀ y ∈ ψ.source, (y ∈ bdry s ↔ ∃ i ∈ S, ψ y i = 0) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.bdry_snc_chart | exact GlobalTheory.CompanionTheory.Metric.bdry_snc_chart | (intros; apply GlobalTheory.CompanionTheory.Metric.bdry_snc_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsMultiHomogIdeal
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem oldIdx_injective {K : Type} {ι : K → Type} :
    Function.Injective (oldIdx (ι := ι)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  change (⟨some a, b⟩ : (o : Option K) × Tb ι o) = ⟨some c, d⟩ at h
  cases h
  rfl

theorem isMultiHomog_inc {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {f : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    IsMultiHomog (inc f : MRing (Tb ι)) (fun o => o.elim 0 a) := by
  classical
  intro m hm o
  have hinj : Function.Injective (oldIdx (ι := ι)) := oldIdx_injective
  change m ∈ (MvPolynomial.rename oldIdx f).support at hm
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  cases o with
  | none =>
    simp only [Option.elim_none]
    apply Finset.sum_eq_zero
    intro i _
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨q, hq⟩
    have h0 := congrArg (fun z : (o : Option K) × Tb ι o => z.1) hq
    simp [oldIdx] at h0
  | some k =>
    simp only [Option.elim_some]
    refine (Fintype.sum_equiv (show Tb ι (some k) ≃ ι k from Equiv.refl _) _
      (fun i => m' ⟨k, i⟩) (fun i => ?_)).trans (hf m' hm' k)
    exact Finsupp.mapDomain_apply hinj m' ⟨k, i⟩

theorem sum_single_none {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (j : Fin 2) (o : Option K) :
    ∑ i, (Finsupp.single (⟨none, j⟩ : Σ o, Tb ι o) 2) ⟨o, i⟩ = o.elim 2 (fun _ => 0) := by
  classical
  cases o with
  | none =>
    simp only [Option.elim_none]
    refine (Fintype.sum_equiv (show Tb ι none ≃ Fin 2 from Equiv.refl _) _
      (fun i : Fin 2 => (Finsupp.single (⟨none, j⟩ : Σ o, Tb ι o) 2) ⟨none, i⟩) (fun _ => rfl)).trans ?_
    rw [Fin.sum_univ_two]
    fin_cases j <;> simp [Finsupp.single_apply] <;>
      (intro h
       have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
       have h3 := congrArg (fun t : Fin 2 => (t : ℕ)) h2
       exact absurd h3 (by decide))
  | some k =>
    simp only [Option.elim_some]
    apply Finset.sum_eq_zero
    intro i _
    rw [Finsupp.single_apply, if_neg]
    intro h
    have h0 := congrArg (fun z : (o : Option K) × Tb ι o => z.1) h
    simp at h0

theorem isMultiHomog_quad {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (p : ℕ) :
    IsMultiHomog (quad p : MRing (Tb ι)) (fun o => o.elim 2 (fun _ => 0)) := by
  classical
  intro m hm o
  have h1 : (xN ^ 2 : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (0 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (1 : ℤ) := by
    simp only [xN, MvPolynomial.X_pow_eq_monomial]
  have h2 : (MvPolynomial.C (p : ℤ) * yN ^ 2 : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (1 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (p : ℤ) := by
    simp only [yN, MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
  have hq : (quad p : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (0 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (1 : ℤ) +
      MvPolynomial.monomial (Finsupp.single (⟨none, (1 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (p : ℤ) := by
    unfold quad
    rw [h1, h2]
  rw [hq] at hm
  have hm2 := Finset.mem_union.mp (MvPolynomial.support_add hm)
  rcases hm2 with h | h
  · have h' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)
    subst h'
    exact sum_single_none (ι := ι) 0 o
  · have h' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)
    subst h'
    exact sum_single_none (ι := ι) 1 o

theorem isMultiHomogIdeal_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (W : Ideal (MRing ι)) (hW : IsMultiHomogIdeal W) : IsMultiHomogIdeal (twist p W) := by
  obtain ⟨S, hS, rfl⟩ := hW
  refine ⟨(inc '' S) ∪ {quad p}, ?_, ?_⟩
  · rintro f (⟨g, hg, rfl⟩ | hf)
    · obtain ⟨a, ha⟩ := hS g hg
      exact ⟨_, isMultiHomog_inc ha⟩
    · rw [Set.mem_singleton_iff] at hf
      subst hf
      exact ⟨_, isMultiHomog_quad p⟩
  · rw [twist, Ideal.map_span, Ideal.span_union]

end GlobalTheory.CompanionTheory.Ar.Tw
end
end

