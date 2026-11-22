import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.IntegralMonoInnerEqZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace NumberField GroundTheory.Arith.SchemeCoh
  MeasureTheory MvPolynomial TensorProduct
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

namespace L2MonomialOrthogonality

variable {N : ℕ}

def monoInner (n : ℕ) (a b : Fin (N + 1) →₀ ℕ) (v : Fin (N + 1) → ℂ) : ℂ :=
  starRingEnd ℂ (eval v (monomial a (1 : ℂ))) * eval v (monomial b (1 : ℂ)) /
    ((norm2 v ^ (2 * n) : ℝ) : ℂ)

lemma monoInner_smul {n : ℕ} {a b : Fin (N + 1) →₀ ℕ} (ha : a.degree = n) (hb : b.degree = n)
    (t : ℂ) (ht : t ≠ 0) (v : Fin (N + 1) → ℂ) :
    monoInner n a b (t • v) = monoInner n a b v := by
  have hea : eval (t • v) (monomial a (1 : ℂ)) = t ^ n * eval v (monomial a 1) :=
    evalAt_smul (RingHom.id ℂ) (isHomogeneous_monomial 1 ha) t v
  have heb : eval (t • v) (monomial b (1 : ℂ)) = t ^ n * eval v (monomial b 1) :=
    evalAt_smul (RingHom.id ℂ) (isHomogeneous_monomial 1 hb) t v
  have htn : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr ht).ne'
  have e : starRingEnd ℂ t ^ n * t ^ n = ((‖t‖ : ℂ) ^ 2) ^ n := by
    rw [← mul_pow, Complex.conj_mul']
  unfold monoInner
  rw [hea, heb, euclideanNorm_smul, map_mul, map_pow]
  push_cast
  calc _ = (starRingEnd ℂ t ^ n * t ^ n) * (starRingEnd ℂ (eval v (monomial a (1 : ℂ))) *
        eval v (monomial b (1 : ℂ))) / (((‖t‖ : ℂ) ^ 2) ^ n * (norm2 v : ℂ) ^ (2 * n)) := by ring
    _ = _ := by rw [e, mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ htn))]

lemma monoInner_mk {n : ℕ} {a b : Fin (N + 1) →₀ ℕ} (ha : a.degree = n) (hb : b.degree = n)
    (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    monoInner n a b (Projectivization.mk ℂ v hv).rep = monoInner n a b v := by
  obtain ⟨t, ht⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  rw [← ht, Units.smul_def]
  exact monoInner_smul ha hb t t.ne_zero v

lemma continuous_monoInner_rep {n : ℕ} {a b : Fin (N + 1) →₀ ℕ} (ha : a.degree = n)
    (hb : b.degree = n) : Continuous fun x : CP N => monoInner n a b x.rep := by
  rw [ProjTopology.continuous_iff]
  have : (fun x : CP N => monoInner n a b x.rep) ∘ Projectivization.mk' ℂ =
      fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} => monoInner n a b v.1 := by
    funext ⟨v, hv⟩
    exact monoInner_mk ha hb v hv
  rw [this]
  have hc : Continuous fun v : Fin (N + 1) → ℂ => norm2 v :=
    Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ =>
      (continuous_norm.comp (continuous_apply j)).pow 2)
  unfold monoInner
  refine Continuous.div ?_ ?_ ?_
  · exact (Complex.continuous_conj.comp ((continuous_eval _).comp continuous_subtype_val)).mul
      ((continuous_eval _).comp continuous_subtype_val)
  · exact Complex.continuous_ofReal.comp ((hc.comp continuous_subtype_val).pow _)
  · intro v
    exact_mod_cast (pow_pos (euclideanNorm_pos v.2) _).ne'

lemma integral_fsMeasure_eq (f : CP N → ℂ) (hf : Continuous f) :
    ∫ x, f x ∂CP.fsMeasure N = ∫ z, (CP.fsVolumeDensity 0 z : ℂ) * f (CP.chartInv 0 z) := by
  rw [CP.fsMeasure, integral_map (CP.measurable_chartInv 0).aemeasurable hf.aestronglyMeasurable,
    CP.fsChartMeasure]
  have hd : (fun z => ENNReal.ofReal (CP.fsVolumeDensity (N := N) 0 z)) =
      fun z => (((CP.fsVolumeDensity (N := N) 0 z).toNNReal : NNReal) : ENNReal) := rfl
  rw [hd, integral_withDensity_eq_integral_smul (CP.measurable_fsVolumeDensity 0).real_toNNReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (CP.fsVolumeDensity_pos 0 z).le, Complex.real_smul]

lemma eval_chartVec_monomial (a : Fin (N + 1) →₀ ℕ) (w : Fin N → ℂ) :
    eval (CP.chartVec 0 w) (monomial a (1 : ℂ)) = ∏ j, w j ^ a j.succ := by
  rw [eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_succ,
    CP.chartVec_self, one_pow, one_mul]
  simp only [CP.chartVec_zero_succ]

theorem integral_monoInner_eq_zero {a b : Fin (N + 1) →₀ ℕ} (hab : a ≠ b)
    (hb : b.degree = a.degree) :
    ∫ x, monoInner a.degree a b x.rep ∂CP.fsMeasure N = 0 := by

  obtain ⟨k, hk⟩ : ∃ k : Fin N, a k.succ ≠ b k.succ := by
    by_contra! h
    apply hab
    have hdeg : ∀ c : Fin (N + 1) →₀ ℕ, c.degree = c 0 + ∑ j : Fin N, c j.succ := fun c => by
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ]
    have h0 : a 0 = b 0 := by
      have h1 := hdeg a
      have h2 := hdeg b
      simp only [h] at h1
      omega
    ext i
    exact Fin.cases h0 (fun j => h j) i
  set p := a k.succ with hp
  set q := b k.succ with hq
  set θ : ℝ := Real.pi / ((q : ℝ) - p) with hθ
  set u : Circle := Circle.exp θ with hu
  have hlam : starRingEnd ℂ (u : ℂ) ^ p * (u : ℂ) ^ q = -1 := by
    have hqp : ((q : ℂ) - p) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hk))
    rw [hu, Circle.coe_exp, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      ← Complex.exp_add]
    have h1 : (θ : ℂ) * ((q : ℂ) - p) = Real.pi := by
      rw [hθ]
      push_cast
      field_simp
    have h2 : (p : ℂ) * (starRingEnd ℂ) (↑θ * Complex.I) + (q : ℂ) * (↑θ * Complex.I) =
        Real.pi * Complex.I := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      linear_combination Complex.I * h1
    rw [h2, Complex.exp_pi_mul_I]

  let c : Fin N → Circle := fun j => if j = k then u else 1
  have hc : ∀ j, (c j : ℂ) = if j = k then (u : ℂ) else 1 := fun j => by
    by_cases hj : j = k <;> simp [c, hj]
  let T : (Fin N → ℂ) ≃ₜ (Fin N → ℂ) :=
    Homeomorph.piCongrRight fun j => (rotation (c j)).toHomeomorph
  have hT : ∀ z j, T z j = c j * z j := fun z j => rfl
  have hTm : MeasurePreserving T volume volume :=
    measurePreserving_pi (fun _ => volume) (fun _ => volume)
      fun j => (rotation (c j)).measurePreserving
  have hnorm : ∀ z j, ‖T z j‖ = ‖z j‖ := fun z j => by
    rw [hT, norm_mul, Circle.norm_coe, one_mul]
  have hprod : ∀ (m : Fin (N + 1) →₀ ℕ) (z : Fin N → ℂ),
      eval (CP.chartVec 0 (T z)) (monomial m (1 : ℂ)) =
        (u : ℂ) ^ m k.succ * eval (CP.chartVec 0 z) (monomial m (1 : ℂ)) := fun m z => by
    rw [eval_chartVec_monomial, eval_chartVec_monomial]
    simp only [hT, mul_pow, Finset.prod_mul_distrib, hc, ite_pow, one_pow, Finset.prod_ite_eq',
      Finset.mem_univ, if_true]

  set G : (Fin N → ℂ) → ℂ := fun z =>
    (CP.fsVolumeDensity 0 z : ℂ) * monoInner a.degree a b (CP.chartVec 0 z) with hG
  have hGT : ∀ z, G (T z) = -G z := fun z => by
    have hdens : CP.fsVolumeDensity (N := N) 0 (T z) = CP.fsVolumeDensity 0 z := by
      rw [CP.fsVolumeDensity_eq, CP.fsVolumeDensity_eq, normSqSum, normSqSum]
      simp only [hnorm]
    have hn2 : norm2 (CP.chartVec 0 (T z)) = norm2 (CP.chartVec 0 z) := by
      rw [norm2, norm2, CP.normSq2_chartVec, CP.normSq2_chartVec]
      simp only [hnorm]
    simp only [hG, hdens, monoInner, hn2, hprod, map_mul, map_pow]
    rw [← hp, ← hq]
    linear_combination (CP.fsVolumeDensity 0 z : ℂ) *
      (starRingEnd ℂ (eval (CP.chartVec 0 z) (monomial a (1 : ℂ))) *
        eval (CP.chartVec 0 z) (monomial b (1 : ℂ)) /
          ((norm2 (CP.chartVec 0 z) ^ (2 * a.degree) : ℝ) : ℂ)) * hlam
  have hint : ∫ x, monoInner a.degree a b x.rep ∂CP.fsMeasure N = ∫ z, G z := by
    rw [integral_fsMeasure_eq _ (continuous_monoInner_rep rfl hb)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hG, CP.chartInv, monoInner_mk rfl hb]
  have hinv : ∫ z, G z = -∫ z, G z := by
    calc ∫ z, G z = ∫ z, G (T z) := (hTm.integral_comp T.measurableEmbedding G).symm
      _ = ∫ z, -G z := by simp only [hGT]
      _ = -∫ z, G z := integral_neg _
  rw [hint]
  linear_combination hinv / 2

theorem integral_monoInner_self (a : Fin (N + 1) →₀ ℕ) :
    ∫ x, monoInner a.degree a a x.rep ∂CP.fsMeasure N =
      (((∏ i, ((a i).factorial : ℝ)) * N.factorial / (a.degree + N).factorial : ℝ) : ℂ) := by
  have hpt : ∀ v : CP N, monoInner a.degree a a v.rep =
      ((CP.fsNormPoly a.degree (monomial a (1 : ℂ)) v ^ 2 : ℝ) : ℂ) := fun v => by
    have e := Complex.conj_mul' (eval v.rep (monomial a (1 : ℂ)))
    unfold monoInner CP.fsNormPoly
    push_cast
    rw [div_pow, ← e]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_complex_ofReal]
  congr 1
  change CP.sectionL2NormSq (N := N) a.degree (monomial a (1 : ℂ)) = _
  rw [← CP.fubiniStudy_l2Norm_sq_eq, CP.fubiniStudy_l2Norm_monomial_sq]

end L2MonomialOrthogonality

lemma fsFibreInner_eq {K : Type} [Field K] [NumberField K] {N : ℕ} (n : ℕ) {ρ : 𝓞 K →+* ℂ}
    (x : (self (𝓞 K) N).complexPoints ρ) (s t : (self (𝓞 K) N).Fibre (twistN (𝓞 K) N n) x) :
    fsFibreInner n x s t = starRingEnd ℂ (fsFrameCoord n ρ x s) * fsFrameCoord n ρ x t *
      (((‖x.1.rep (CP.chartIndex x.1)‖ ^ n / norm2 x.1.rep ^ n) ^ 2 : ℝ) : ℂ) := by
  set κ := ‖x.1.rep (CP.chartIndex x.1)‖ ^ n / norm2 x.1.rep ^ n with hκ
  have hN : ∀ w, fsFibreNorm n ρ x w = ‖fsFrameCoord n ρ x w‖ * κ := fun w => by
    rw [fsFibreNorm, hκ, mul_div_assoc]
  unfold fsFibreInner
  simp only [hN, map_add, map_sub, map_smul, smul_eq_mul]
  set p := fsFrameCoord n ρ x s
  set q := fsFrameCoord n ρ x t
  push_cast
  simp only [mul_pow, ← Complex.conj_mul', map_add, map_sub, map_mul, Complex.conj_I]
  linear_combination ((κ : ℂ) ^ 2 * (starRingEnd ℂ q * p - starRingEnd ℂ p * q) / 2) * Complex.I_sq

theorem fsFibreInner_monomial (h : FSCoord.Statement.{0}) {K : Type} [Field K] [NumberField K]
    {N : ℕ} (σ : K →+* ℂ) (a b : Fin (N + 1) →₀ ℕ) (hb : b.degree = a.degree)
    (x : (self (𝓞 K) N).complexPoints (intEmb σ)) :
    fsFibreInner a.degree x
        ((self (𝓞 K) N).evalFibre (twistN (𝓞 K) N a.degree) σ x
          ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] polySection (monomial_mem_grading (A := 𝓞 K) a rfl)))
        ((self (𝓞 K) N).evalFibre (twistN (𝓞 K) N a.degree) σ x
          ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] polySection (monomial_mem_grading (A := 𝓞 K) b hb))) =
      L2MonomialOrthogonality.monoInner a.degree a b x.1.rep := by
  rw [evalFibre_tmul, evalFibre_tmul, map_one, one_smul, one_smul, fsFibreInner_eq]
  have hca := h (𝓞 K) N a.degree (intEmb σ) _ (monomial_mem_grading (A := 𝓞 K) a rfl) x
    (CP.chartIndex x.1) (rep_chartIndex_ne_zero x.1)
  have hcb := h (𝓞 K) N a.degree (intEmb σ) _ (monomial_mem_grading (A := 𝓞 K) b hb) x
    (CP.chartIndex x.1) (rep_chartIndex_ne_zero x.1)
  change fsFrameCoord _ _ x _ * _ = _ at hca hcb
  have ev : ∀ m : Fin (N + 1) →₀ ℕ, evalAt (intEmb σ) x.1.rep (monomial m (1 : 𝓞 K)) =
      eval x.1.rep (monomial m (1 : ℂ)) := fun m => by
    simp [evalAt, eval₂_monomial, eval_monomial]
  rw [ev] at hca hcb
  set vj := x.1.rep (CP.chartIndex x.1)
  have hn : (norm2 x.1.rep : ℂ) ≠ 0 := by exact_mod_cast (euclideanNorm_pos x.1.rep_nonzero).ne'
  have e : starRingEnd ℂ vj ^ a.degree * vj ^ a.degree = ((‖vj‖ : ℂ) ^ 2) ^ a.degree := by
    rw [← mul_pow, Complex.conj_mul']
  rw [L2MonomialOrthogonality.monoInner, ← hca, ← hcb]
  push_cast
  rw [map_mul, map_pow]
  linear_combination (-(starRingEnd ℂ (fsFrameCoord a.degree (intEmb σ) x
    ((self (𝓞 K) N).evalGlobalSection (twistN (𝓞 K) N a.degree) x
      (polySection (monomial_mem_grading (A := 𝓞 K) a rfl)))) *
    fsFrameCoord a.degree (intEmb σ) x ((self (𝓞 K) N).evalGlobalSection (twistN (𝓞 K) N a.degree) x
      (polySection (monomial_mem_grading (A := 𝓞 K) b hb))) /
      (norm2 x.1.rep : ℂ) ^ (2 * a.degree))) * e

theorem L2MonomialOrthogonality.proof (h : FSCoord.Statement.{0}) (_h' : FSIndex.Statement.{0}) :
    L2MonomialOrthogonality.Statement := by
  intro K _ _ N σ a b hb
  unfold fubiniStudyL2Inner
  refine (integral_congr_ae (g := fun v : CP N => L2MonomialOrthogonality.monoInner a.degree a b v.rep)
    (Filter.Eventually.of_forall fun v => ?_)).trans ?_
  · have hv : v ∈ (self (𝓞 K) N).complexPoints (intEmb σ) := by
      rw [complexPoints_self]; trivial
    simp only [dif_pos hv]
    exact fsFibreInner_monomial h σ a b hb ⟨v, hv⟩
  · split_ifs with hab
    · subst hab
      exact L2MonomialOrthogonality.integral_monoInner_self a
    · exact L2MonomialOrthogonality.integral_monoInner_eq_zero hab hb

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSConjInvariant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

namespace SectionsLatticeFS

theorem FSConjInvariant.proof : FSConjInvariant.Statement := by
  intro N
  let cv : (Fin N → ℂ) → (Fin N → ℂ) := fun z k => starRingEnd ℂ (z k)
  have hc : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume :=
    LinearIsometryEquiv.measurePreserving Complex.conjLIE
  have hcv : MeasurePreserving cv volume volume := volume_preserving_pi fun _ => hc
  have hchart : CP.conj ∘ CP.chartInv 0 = CP.chartInv 0 ∘ cv := by
    funext z
    simp only [Function.comp, CP.chartInv, CP.conj_mk]
    congr 1
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [CP.conjVec_apply]
    · have h1 := CP.chartVec_succAbove (0 : Fin (N + 1)) z j
      have h2 := CP.chartVec_succAbove (0 : Fin (N + 1)) (cv z) j
      simp only [Fin.succAbove_zero] at h1 h2
      rw [CP.conjVec_apply, h1, h2]
  have hdens : ∀ z, CP.fsVolumeDensity (0 : Fin (N + 1)) (cv z) = CP.fsVolumeDensity 0 z := by
    intro z
    simp only [CP.fsVolumeDensity_eq, normSqSum, cv, Complex.norm_conj]
  have hmeas : Measurable fun z => ENNReal.ofReal (CP.fsVolumeDensity (0 : Fin (N + 1)) z) :=
    ENNReal.measurable_ofReal.comp (CP.measurable_fsVolumeDensity 0)
  have hmap : (CP.fsChartMeasure (N := N) 0).map cv = CP.fsChartMeasure 0 := by
    ext s hs
    rw [Measure.map_apply hcv.measurable hs, CP.fsChartMeasure,
      withDensity_apply _ (hcv.measurable hs), withDensity_apply _ hs,
      ← hcv.setLIntegral_comp_preimage hs hmeas]
    simp only [hdens]
  rw [CP.fsMeasure, Measure.map_map CP.continuous_conj.measurable (CP.measurable_chartInv 0), hchart,
    ← Measure.map_map (CP.measurable_chartInv 0) hcv.measurable, hmap]

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSContinuousFrame
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

lemma rep_ne_zero_of_mem_chartDomain {N : ℕ} {j : Fin (N + 1)} {v : CP N}
    (hv : v ∈ CP.chartDomain j) : v.rep j ≠ 0 := by
  have h := CP.mk_mem_chartDomain j v.rep v.rep_nonzero
  rw [Projectivization.mk_rep] at h
  exact h.mp hv

lemma norm_rep_pow_div {N : ℕ} (n : ℕ) (j : Fin (N + 1)) (v : CP N) :
    ‖v.rep j‖ ^ n / norm2 v.rep ^ n =
      CP.fsNormPoly n ((MvPolynomial.X j : MvPolynomial (Fin (N + 1)) ℂ) ^ n) v := by
  simp [CP.fsNormPoly, norm_pow]

theorem continuousOn_chart (h₁ : FSIndex.Statement.{u}) (h₂ : ComplexMetric.RegularContinuous.Statement.{u})
    {A : Type u} [CommRing A] {N n : ℕ} (ρ : A →+* ℂ) {U : (self A N).X.Opens}
    (e : ((preMod (self A N).X).obj (twistN A N n)).obj (op U)) (j : Fin (N + 1)) :
    ContinuousOn (fun y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} =>
        fsFibreNorm n ρ y.1 ((self A N).sectionValue y.1 y.2 e))
      {y | y.1.1 ∈ CP.chartDomain j} := by
  let V : (self A N).X.Opens := U ⊓ ProjSpace.stdOpen A N j
  have hVU : V ≤ U := inf_le_left
  have hVj : V ≤ ProjSpace.stdOpen A N j := inf_le_right

  obtain ⟨f, hf⟩ := (isBasisOn_frame (A := A) j n V hVj).2 (resM _ hVU e)
  have hV : ∀ y : {y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} //
      y.1.1 ∈ CP.chartDomain j}, (self A N).point y.1.1 ∈ V := fun y =>
    ⟨y.1.2, point_mem_stdOpen y.1.1 (rep_ne_zero_of_mem_chartDomain y.2)⟩
  let ι := fun y : {y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} //
      y.1.1 ∈ CP.chartDomain j} => (⟨y.1.1, hV y⟩ : {x : (self A N).complexPoints ρ // (self A N).point x ∈ V})
  have hι : Continuous ι :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

  have hval : ∀ y : {y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} //
      y.1.1 ∈ CP.chartDomain j},
      fsFibreNorm n ρ y.1.1 ((self A N).sectionValue y.1.1 y.1.2 e) =
        ‖(self A N).evalAtPoint y.1.1 (germR (hV y) f)‖ *
          CP.fsNormPoly n ((MvPolynomial.X j : MvPolynomial (Fin (N + 1)) ℂ) ^ n) y.1.1.1 := by
    intro y
    have hyj := rep_ne_zero_of_mem_chartDomain y.2
    have hp := point_mem_stdOpen y.1.1 hyj
    rw [h₁ A N n ρ y.1.1 j hyj, mul_div_assoc, norm_rep_pow_div]
    congr 2
    change (Via.ofComplex ((self A N).evalAtPoint y.1.1)).symm
      (fibreEquiv (X := (self A N).X) (L := twistN A N n) ((self A N).evalAtPoint y.1.1) hp
        (isBasisOn_frame (A := A) j n)
        (fibreMk (X := (self A N).X) (twistN A N n) ((self A N).evalAtPoint y.1.1) 1
          (germM (X := (self A N).X) (L := twistN A N n) y.1.2 e))) = _
    rw [← germM_resM hVU (hV y) e, ← hf, germM_smul, germM_resM hVj (hV y)]
    have key := fibreEquiv_fibreMk (φ := (self A N).evalAtPoint y.1.1) hp
      (isBasisOn_frame (A := A) j n) 1 (germR (hV y) f)
    rw [mul_one] at key
    exact (congrArg (Via.ofComplex ((self A N).evalAtPoint y.1.1)).symm key).trans
      (RingEquiv.symm_apply_apply _ _)
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous fun y : {y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} //
      y.1.1 ∈ CP.chartDomain j} =>
        ‖(self A N).evalAtPoint y.1.1 (germR (hV y) f)‖ *
          CP.fsNormPoly n ((MvPolynomial.X j : MvPolynomial (Fin (N + 1)) ℂ) ^ n) y.1.1.1 :=
    (continuous_norm.comp ((h₂ A N (self A N) ρ V f).comp hι)).mul
      ((CP.continuous_fsNormPoly (MvPolynomial.isHomogeneous_X_pow j n)).comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)))
  exact hc.congr fun y => (hval y).symm

theorem FSContinuousFrame.proof (h₁ : FSIndex.Statement.{u})
    (h₂ : ComplexMetric.RegularContinuous.Statement.{u}) : FSContinuousFrame.Statement.{u} := by
  intro A _ N n ρ U e _
  rw [continuous_iff_continuousAt]
  intro y₀
  let j := CP.chartIndex y₀.1.1
  have hW : IsOpen {y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} |
      y.1.1 ∈ CP.chartDomain j} :=
    (CP.isOpen_chartDomain j).preimage
      (continuous_subtype_val.comp continuous_subtype_val :
        Continuous fun y : {x : (self A N).complexPoints ρ // (self A N).point x ∈ U} => y.1.1)
  exact (continuousOn_chart h₁ h₂ ρ e j).continuousAt
    (hW.mem_nhds (CP.mem_chartDomain_chartIndex y₀.1.1))

example (h₁ : FSIndex.Statement.{0}) (h₂ : ComplexMetric.RegularContinuous.Statement.{0}) :
    Continuous fun y : {x : (self (NumberField.RingOfIntegers ℚ) 1).complexPoints
        (intEmb (Rat.castHom ℂ)) // (self _ 1).point x ∈ ProjSpace.stdOpen _ 1 0} =>
      fsFibreNorm 1 _ y.1 ((self _ 1).sectionValue y.1 y.2 (stdFrame _ 0 1)) :=
  FSContinuousFrame.proof h₁ h₂ _ _ _ _ _ _ (isBasisOn_frame 0 1)

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSFullSupport
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set

noncomputable section

namespace SectionsLatticeFS

lemma FSFullSupport.inter_chartDomain_nonempty {N : ℕ} {U : Set (CP N)} (hU : IsOpen U)
    (hne : U.Nonempty) : (U ∩ CP.chartDomain 0).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  induction x using Projectivization.ind with
  | h v hv =>
    rw [ProjTopology.isOpen_iff] at hU
    obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.mp hU
    let g : ℂ → (Fin (N + 1) → ℂ) := fun t => v + t • Pi.single 0 1
    have hg : Continuous g := continuous_const.add (continuous_id.smul continuous_const)
    have hvO : v ∈ O := by
      have : (⟨v, hv⟩ : {w : Fin (N + 1) → ℂ // w ≠ 0}) ∈ Projectivization.mk' ℂ ⁻¹' U := hx
      rw [← hOU] at this
      exact this
    have h0 : (g ⁻¹' O).Nonempty := ⟨0, by simpa [g] using hvO⟩
    obtain ⟨t, htO, ht⟩ :=
      (dense_compl_singleton (-(v 0))).inter_open_nonempty _ (hO.preimage hg) h0
    have hw0 : g t 0 ≠ 0 := by
      intro h
      apply ht
      simp only [g, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h
      simp only [mem_singleton_iff]
      linear_combination h
    have hw : g t ≠ 0 := fun h => hw0 (by rw [h]; rfl)
    refine ⟨Projectivization.mk ℂ (g t) hw, ?_, hw0⟩
    have : (⟨g t, hw⟩ : {w : Fin (N + 1) → ℂ // w ≠ 0}) ∈ Subtype.val ⁻¹' O := htO
    rw [hOU] at this
    exact this

theorem FSFullSupport.proof : FSFullSupport.Statement := by
  intro N U hU hne
  obtain ⟨x, hxU, hx0⟩ := FSFullSupport.inter_chartDomain_nonempty hU hne
  rw [CP.fsMeasure, Measure.map_apply (CP.measurable_chartInv 0) hU.measurableSet, CP.fsChartMeasure,
    pos_iff_ne_zero, Ne,
    withDensity_apply_eq_zero' (CP.measurable_fsVolumeDensity 0).ennreal_ofReal.aemeasurable]
  have hset : {z : Fin N → ℂ | ENNReal.ofReal (CP.fsVolumeDensity 0 z) ≠ 0} = univ := by
    ext z
    simp [CP.fsVolumeDensity_pos 0 z]
  rw [hset, univ_inter, ← Ne, ← pos_iff_ne_zero]
  refine ((CP.continuous_chartInv 0).isOpen_preimage U hU).measure_pos volume
    ⟨CP.chartCoord 0 x, ?_⟩
  simpa [CP.chartInv_chartCoord 0 hx0] using hxU

example : 0 < CP.fsMeasure 1 univ := FSFullSupport.proof 1 univ isOpen_univ univ_nonempty

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSValue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

theorem FSValue.proof (h : FSCoord.Statement.{u}) : FSValue.Statement.{u} := by
  intro A _ N n ρ P hP x
  have hj := rep_chartIndex_ne_zero x.1
  have hc := h A N n ρ P hP x (CP.chartIndex x.1) hj
  have hcoord : fsFrameCoord n ρ x ((self A N).evalGlobalSection (twistN A N n) x (polySection hP)) =
      evalAt ρ x.1.rep P / x.1.rep (CP.chartIndex x.1) ^ n :=
    eq_div_of_mul_eq (pow_ne_zero _ hj) hc
  have hpos : 0 < ‖x.1.rep (CP.chartIndex x.1)‖ ^ n := pow_pos (norm_pos_iff.mpr hj) n
  rw [fsFibreNorm, hcoord, CP.fsNormPoly, MvPolynomial.eval_map, norm_div, norm_pow,
    div_mul_cancel₀ _ hpos.ne']

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

