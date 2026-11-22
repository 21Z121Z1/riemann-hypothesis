import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.DiagUnitary
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FSInv

open scoped ComplexConjugate
open MeasureTheory MvPolynomial CP

noncomputable section

theorem Orth.proof (hU : UnitaryInv.Statement) (hP : PairMk.Statement) : Orth.Statement := by
  intro N a b hab hdeg
  obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
    by_contra h
    exact hab (Finsupp.ext fun i => by_contra fun hi => h ⟨i, hi⟩)
  have hA : monomial a (1 : ℂ) ∈ H0 N a.degree :=
    (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial _ rfl)
  have hB : monomial b (1 : ℂ) ∈ H0 N a.degree :=
    (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial _ hdeg.symm)

  set θ : ℝ := Real.pi / |(b k : ℝ) - a k| with hθ
  have key : ((b k : ℝ) - a k) * θ = Real.pi ∨ ((b k : ℝ) - a k) * θ = -Real.pi := by
    rcases lt_or_gt_of_ne hk with h | h
    · have h' : (0 : ℝ) < (b k : ℝ) - a k := by
        have : (a k : ℝ) < b k := by exact_mod_cast h
        linarith
      have hne : (b k : ℝ) - a k ≠ 0 := h'.ne'
      left
      rw [hθ, abs_of_pos h']
      field_simp
    · have h' : (b k : ℝ) - a k < 0 := by
        have : (b k : ℝ) < a k := by exact_mod_cast h
        linarith
      have hne : (b k : ℝ) - a k ≠ 0 := h'.ne
      right
      rw [hθ, abs_of_neg h']
      field_simp
  have hzmem : Complex.exp (θ * Complex.I) ∈ unitary ℂ := by
    rw [Unitary.mem_iff_star_mul_self, Complex.star_def, Complex.conj_mul',
      Complex.norm_exp_ofReal_mul_I]
    norm_num
  set z : unitary ℂ := ⟨Complex.exp (θ * Complex.I), hzmem⟩ with hz
  have hfac : conj ((z : ℂ) ^ a k) * (z : ℂ) ^ b k = -1 := by
    rw [hz, map_pow, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    have harg : (a k : ℂ) * (θ * -Complex.I) + (b k : ℂ) * (θ * Complex.I) =
        (((b k : ℝ) - a k) * θ : ℝ) * Complex.I := by
      push_cast; ring
    rw [harg]
    rcases key with h | h <;> rw [h]
    · exact Complex.exp_pi_mul_I
    · rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num

  set w : Fin (N + 1) → unitary ℂ := fun i => if i = k then z else 1 with hw
  have hwv : ∀ i, ((w i : unitary ℂ) : ℂ) = if i = k then (z : ℂ) else 1 := fun i => by
    simp only [hw]; split_ifs <;> rfl
  have hwn : ∀ i, ‖((w i : unitary ℂ) : ℂ)‖ = 1 := fun i => by
    rw [hwv]; split_ifs
    · rw [hz]; exact Complex.norm_exp_ofReal_mul_I θ
    · exact norm_one
  have hprod : ∀ c : Fin (N + 1) →₀ ℕ, ∏ i, ((w i : unitary ℂ) : ℂ) ^ c i = (z : ℂ) ^ c k := by
    intro c
    simp only [hwv, ite_pow, one_pow, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hlin : ∀ v : Fin (N + 1) → ℂ,
      Matrix.toLin' (diagUnitary w : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) v =
        fun i => ((w i : unitary ℂ) : ℂ) * v i := fun v => by
    funext i
    simp [diagUnitary, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have hev : ∀ (c : Fin (N + 1) →₀ ℕ) (v : Fin (N + 1) → ℂ),
      eval (fun i => ((w i : unitary ℂ) : ℂ) * v i) (monomial c (1 : ℂ)) =
        (z : ℂ) ^ c k * eval v (monomial c 1) := fun c v => by
    rw [← hprod c, eval_monomial, eval_monomial, one_mul, one_mul,
      Finsupp.prod_fintype _ _ (fun i => pow_zero _), Finsupp.prod_fintype _ _ (fun i => pow_zero _),
      ← Finset.prod_mul_distrib]
    simp only [mul_pow]
  have hnorm : ∀ v : Fin (N + 1) → ℂ, norm2 (fun i => ((w i : unitary ℂ) : ℂ) * v i) = norm2 v :=
    fun v => by simp only [norm2, normSq2, norm_mul, hwn, one_mul]

  set f := fsPair (N := N) a.degree (monomial a (1 : ℂ)) (monomial b 1) with hf
  have hpt : ∀ x, f (unitaryAct (diagUnitary w) x) = -f x := by
    intro x
    induction x using Projectivization.ind with
    | h v hv =>
      rw [hf, unitaryAct_mk, hP N _ _ _ hA hB, hP N _ _ _ hA hB, hlin, hev, hev, hnorm, map_mul]
      linear_combination (conj (eval v (monomial a (1 : ℂ))) * eval v (monomial b 1) /
        ((norm2 v ^ (2 * a.degree) : ℝ) : ℂ)) * hfac

  have hcont : Continuous f := by
    rw [ProjTopology.continuous_iff]
    have e : f ∘ Projectivization.mk' ℂ = fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} =>
        conj (eval v.1 (monomial a (1 : ℂ))) * eval v.1 (monomial b 1) /
          ((norm2 v.1 ^ (2 * a.degree) : ℝ) : ℂ) := by
      funext ⟨v, hv⟩
      exact hP N _ _ _ hA hB v hv
    rw [e]
    have hc2 : Continuous fun v : Fin (N + 1) → ℂ => norm2 v :=
      Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ =>
        (continuous_norm.comp (continuous_apply j)).pow 2)
    refine Continuous.div ?_ ?_ ?_
    · exact (Complex.continuous_conj.comp ((MvPolynomial.continuous_eval _).comp
        continuous_subtype_val)).mul ((MvPolynomial.continuous_eval _).comp continuous_subtype_val)
    · exact Complex.continuous_ofReal.comp ((hc2.comp continuous_subtype_val).pow _)
    · intro v
      exact_mod_cast (pow_pos (euclideanNorm_pos v.2) _).ne'

  have hmp := hU N (diagUnitary w)
  have hint : ∫ x, f x ∂fsMeasure N = ∫ x, f (unitaryAct (diagUnitary w) x) ∂fsMeasure N := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable hcont.measurable.aestronglyMeasurable
  rw [show (fun x => f (unitaryAct (diagUnitary w) x)) = fun x => -f x from funext hpt,
    integral_neg] at hint
  show ∫ x, f x ∂fsMeasure N = 0
  linear_combination hint / 2

end

end GroundTheory.Heights₂.Heights.FSInv
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.L2Inner
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ComplexConjugate
open MeasureTheory MvPolynomial CP

noncomputable section

namespace FSInv

theorem Sesq.proof (hP : PairMk.Statement) : Sesq.Statement := by
  intro N n P Q R hPn hQn hRn c
  have hint : ∀ A B : MvPolynomial (Fin (N + 1)) ℂ, A ∈ H0 N n → B ∈ H0 N n →
      Integrable (fsPair (N := N) n A B) (fsMeasure N) := by
    intro A B hA hB
    have hcont : Continuous (fsPair (N := N) n A B) := by
      rw [ProjTopology.continuous_iff]
      have e : fsPair (N := N) n A B ∘ Projectivization.mk' ℂ =
          fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} =>
            conj (eval v.1 A) * eval v.1 B / ((norm2 v.1 ^ (2 * n) : ℝ) : ℂ) := by
        funext ⟨v, hv⟩
        exact hP N n A B hA hB v hv
      rw [e]
      have hc : Continuous fun v : Fin (N + 1) → ℂ => norm2 v :=
        Real.continuous_sqrt.comp (continuous_finsetSum _ fun j _ =>
          (continuous_norm.comp (continuous_apply j)).pow 2)
      refine Continuous.div ?_ (Complex.continuous_ofReal.comp ((hc.comp continuous_subtype_val).pow _))
        fun v => ?_
      · exact (Complex.continuous_conj.comp ((continuous_eval A).comp continuous_subtype_val)).mul
          ((continuous_eval B).comp continuous_subtype_val)
      · exact_mod_cast (pow_pos (euclideanNorm_pos v.2) _).ne'
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨?_, ?_, ?_⟩
  · have e : fsPair (N := N) n (P + c • Q) R =
        fun x => fsPair n P R x + conj c * fsPair n Q R x := by
      funext x
      simp only [fsPair, map_add, smul_eval, map_mul]
      ring
    rw [l2Inner, e, integral_add (hint P R hPn hRn) ((hint Q R hQn hRn).const_mul _),
      integral_const_mul]
    rfl
  · have e : fsPair (N := N) n R (P + c • Q) =
        fun x => fsPair n R P x + c * fsPair n R Q x := by
      funext x
      simp only [fsPair, map_add, smul_eval]
      ring
    rw [l2Inner, e, integral_add (hint R P hRn hPn) ((hint R Q hRn hQn).const_mul _),
      integral_const_mul]
    rfl
  · have e : fsPair (N := N) n Q P = fun x => conj (fsPair n P Q x) := by
      funext x
      simp only [fsPair, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]
      ring
    rw [l2Inner, e, integral_conj]
    rfl

end FSInv

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PAmbEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace FSInv

open CP

private lemma measurable_lineOf' {N : ℕ} : Measurable (lineOf (N := N)) := by
  refine measurable_of_continuousOn_compl_singleton 0 ?_
  rw [continuousOn_iff_continuous_domRestrict]
  have h : ({0}ᶜ : Set (Fin (N + 1) → ℂ)).domRestrict lineOf =
      fun v => Projectivization.mk' ℂ ⟨v.1, v.2⟩ := by
    funext ⟨v, hv⟩; exact lineOf_of_ne hv
  rw [h]
  exact ProjTopology.continuous_mk'.comp (continuous_subtype_val.subtype_mk _)

private lemma chart_eq (hA : AmbChart.Statement) {N : ℕ} (i : Fin (N + 1)) :
    (fsChartMeasure i).map (chartInv i) =
      ENNReal.ofReal ((N + 1).factorial / Real.pi ^ (N + 1)) • (ambMeasure N).map lineOf := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf (measurable_chartInv i), fsChartMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_fsVolumeDensity i).ennreal_ofReal
      (g := fun z => f (chartInv i z)) (hf.comp (measurable_chartInv i)),
    lintegral_smul_measure, lintegral_map hf measurable_lineOf', hA N i f hf, smul_eq_mul,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun z => ?_
  simp only [Pi.mul_apply]
  have hr : fsVolumeDensity (N := N) i z = ((N + 1).factorial / Real.pi ^ (N + 1) *
      (Real.pi / (N + 1))) * (1 / (1 + normSqSum z) ^ (N + 1)) := by
    rw [fsVolumeDensity_eq, Nat.factorial_succ]
    push_cast
    have := Real.pi_pos
    have := one_add_normSqSum_pos z
    field_simp
    ring
  rw [hr, ENNReal.ofReal_mul (by positivity)]
  ring

theorem AmbEq.proof (hA : AmbChart.Statement) : AmbEq.Statement := fun _ => chart_eq hA 0

end FSInv

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PAmbUnitary
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped Matrix ComplexConjugate ENNReal
open MeasureTheory

noncomputable section

namespace FSInv

open CP

theorem AmbUnitary.proof (hL : LinChange.Statement) : AmbUnitary.Statement := by
  intro N U
  set A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) with hA
  have hU : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2

  have hC : ∀ w : Fin (N + 1) → ℂ, ((normSq2 w : ℝ) : ℂ) = star w ⬝ᵥ w := by
    intro w
    simp only [normSq2, dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
    push_cast; rfl
  have hnorm : ∀ v : Fin (N + 1) → ℂ, normSq2 (A *ᵥ v) = normSq2 v := by
    intro v
    apply Complex.ofReal_injective
    rw [hC, hC, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Matrix.star_eq_conjTranspose, hU, Matrix.vecMul_one]
  have hdens : ∀ v : Fin (N + 1) → ℂ, ambDensity (A *ᵥ v) = ambDensity v := by
    intro v; simp only [ambDensity, hnorm]

  have hdet : Complex.normSq (LinearMap.det (Matrix.toLin' A)) = 1 := by
    rw [LinearMap.det_toLin']
    have h1 : star A.det * A.det = 1 := Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary U.2)
    have h2 : ((Complex.normSq A.det : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]; exact h1
    exact_mod_cast h2
  have hdet0 : LinearMap.det (Matrix.toLin' A) ≠ 0 := by
    intro h; rw [h, map_zero] at hdet; exact zero_ne_one hdet
  have hT : Measurable (Matrix.toLin' A) :=
    (LinearMap.continuous_of_finiteDimensional (Matrix.toLin' A)).measurable
  have hmd : Measurable fun v : Fin (N + 1) → ℂ => ENNReal.ofReal (ambDensity v) := by
    unfold ambDensity normSq2; fun_prop
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf hT, ambMeasure, lintegral_withDensity_eq_lintegral_mul _ hmd
      (show Measurable fun a => f (Matrix.toLin' A a) from hf.comp hT),
    lintegral_withDensity_eq_lintegral_mul _ hmd hf]
  have key := hL (N + 1) (Matrix.toLin' A) hdet0 (fun u => ENNReal.ofReal (ambDensity u) * f u)
    (hmd.mul hf)
  rw [hdet, ENNReal.ofReal_one, one_mul] at key
  simp only [Pi.mul_apply, Matrix.toLin'_apply] at key ⊢
  rw [key]
  simp only [hdens]

end FSInv

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PDefinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace FSInv

open CP

theorem Definite.proof (hPar : Parseval.Statement) (hI : InnerSelf.Statement) :
    Definite.Statement := by
  intro N n P hP
  constructor
  · intro h0
    have h1 : sectionL2NormSq (N := N) n P = 0 := by exact_mod_cast (hI N n P).symm.trans h0
    have h2 := hPar N n P hP
    rw [fubiniStudy_l2Norm_sq_eq, h1] at h2
    by_contra hne
    obtain ⟨a, ha⟩ : P.support.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hne)
    have hpos : 0 < ∑ a ∈ P.support, ‖P.coeff a‖ ^ 2 *
        ((∏ i, ((a i).factorial : ℝ)) * N.factorial / (n + N).factorial) := by
      refine Finset.sum_pos' (fun b _ => by positivity) ⟨a, ha, ?_⟩
      have hc : P.coeff a ≠ 0 := MvPolynomial.mem_support_iff.mp ha
      have : 0 < ‖P.coeff a‖ := norm_pos_iff.mpr hc
      positivity
    linarith
  · rintro rfl
    rw [hI]
    simp [sectionL2NormSq, fsNormPoly]

end FSInv

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PFormIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace FSInv

open CP

theorem FormIntegral.proof (hC : ChartIndep.Statement) : FormIntegral.Statement := by
  intro N i g hg
  rw [hC N i] at hg ⊢
  rw [integral_map (measurable_chartInv i).aemeasurable hg, fsChartMeasure]
  have hd : (fun z => ENNReal.ofReal (fsVolumeDensity (N := N) i z)) =
      fun z => (((fsVolumeDensity (N := N) i z).toNNReal : NNReal) : ℝ≥0∞) := rfl
  rw [hd, integral_withDensity_eq_integral_smul (measurable_fsVolumeDensity i).real_toNNReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (fsVolumeDensity_pos i z).le, smul_eq_mul]
  rw [fsVolumeDensity, mul_comm]

end FSInv

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PInnerSelf
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace FSInv

open CP

theorem InnerSelf.proof : InnerSelf.Statement := by
  intro N n P
  rw [l2Inner, sectionL2NormSq, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [fsPair, fsNormPoly]
  have hn : ((norm2 x.rep : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (euclideanNorm_pos x.rep_nonzero).ne'
  rw [mul_comm (conj _), Complex.mul_conj']
  push_cast
  field_simp
  ring

end FSInv

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PLinChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace FSInv

open CP

theorem LinChange.proof : LinChange.Statement := by
  intro n f hf g hg
  set L := f.restrictScalars ℝ
  have hdet : LinearMap.det L = Complex.normSq (LinearMap.det f) := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  have hpos : 0 < Complex.normSq (LinearMap.det f) := Complex.normSq_pos.mpr hf
  have hL : LinearMap.det L ≠ 0 := by rw [hdet]; exact hpos.ne'
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin n → ℂ)) hL
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  have e : ∫⁻ z, g (f z) = ∫⁻ z, g (L z) := rfl
  rw [e, ← lintegral_map hg hLm, hmap, lintegral_smul_measure, hdet, abs_inv, abs_of_pos hpos,
    smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne',
    ENNReal.ofReal_one, one_mul]

end FSInv

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PPairMk
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace FSInv

open CP

theorem PairMk.proof : PairMk.Statement := by
  intro N n P Q hP hQ v hv
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  have hPe : eval ((a : ℂ) • v) P = (a : ℂ) ^ n * eval v P :=
    evalAt_smul (RingHom.id ℂ) ((mem_homogeneousSubmodule _ _).mp hP) (a : ℂ) v
  have hQe : eval ((a : ℂ) • v) Q = (a : ℂ) ^ n * eval v Q :=
    evalAt_smul (RingHom.id ℂ) ((mem_homogeneousSubmodule _ _).mp hQ) (a : ℂ) v
  rw [fsPair, ← ha, Units.smul_def, hPe, hQe, euclideanNorm_smul]
  have ha0 : (a : ℂ) ≠ 0 := a.ne_zero
  have hA : ((‖(a : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr ha0).ne'
  have hN : ((norm2 v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (euclideanNorm_pos hv).ne'
  have hc : conj (a : ℂ) ^ n * (a : ℂ) ^ n = ((‖(a : ℂ)‖ : ℝ) : ℂ) ^ (2 * n) := by
    rw [← mul_pow, Complex.conj_mul', ← pow_mul]
  push_cast
  rw [div_eq_div_iff (pow_ne_zero _ (mul_ne_zero hA hN)) (pow_ne_zero _ hN), map_mul, map_pow,
    mul_pow, ← hc]
  ring

end FSInv

end

end GroundTheory.Heights₂.Heights
end

