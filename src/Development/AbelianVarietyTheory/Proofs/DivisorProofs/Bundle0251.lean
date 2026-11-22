import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0093
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0207
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
import Formalism.LatticeTheta.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0204
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMetaplecticSchwartzActionProd
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

noncomputable section

namespace GlobalTheory.RealWeil

theorem continuous_omS_prod (l : Type) [Fintype l] [DecidableEq l] (G : Type) [Group G] [TopologicalSpace G]
    (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l))
    (hpr : Continuous pr) (hom : ∀ f : L2 l, Continuous fun g => om g f)
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) :
    Continuous fun x : G × Sch l => omS x.1 x.2 := by

  have hjoint : Continuous fun x : G × L2 l => om x.1 x.2 :=
    continuous_prod_of_continuous_lipschitzWith' (fun x : G × L2 l => om x.1 x.2) 1
      (fun g => (om g).isometry.lipschitz) hom
  have hentry : ∀ a b, Continuous fun g => (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b := fun a b =>
    by
    have hv : Continuous fun g => (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
      (continuous_subtype_val (p := fun M => M ∈ Matrix.symplecticGroup l ℝ)).comp hpr
    exact (continuous_apply b).comp ((continuous_apply a).comp hv)

  have key : ∀ {A : Sch l →L[ℂ] Sch l}, A ∈ weylAlg l →
      Continuous fun x : G × Sch l => schwartzToL2 l (A (omS x.1 x.2)) := by
    intro A hA
    refine weylAlg_induction (P := fun A => Continuous fun x : G × Sch l => schwartzToL2 l (A (omS x.1 x.2)))
      ?_ ?_ ?_ ?_ ?_ hA
    · have e : (fun x : G × Sch l => schwartzToL2 l ((1 : Sch l →L[ℂ] Sch l) (omS x.1 x.2))) =
          fun x => om x.1 (schwartzToL2 l x.2) := by
        funext x
        simp only [ContinuousLinearMap.one_apply, schwartzToL2_apply, h4]
      rw [e]
      exact hjoint.comp (continuous_fst.prodMk ((schwartzToL2 l).continuous.comp continuous_snd))
    · intro A w ih
      simp only [toLp_dRho_omS h3 h4]
      refine continuous_finset_sum _ fun a _ => ?_
      have hih : Continuous fun x : G × Sch l => schwartzToL2 l (A (omS x.1 (dRho (Pi.single a 1) x.2))) :=
        ih.comp (continuous_fst.prodMk ((dRho (Pi.single a 1)).continuous.comp continuous_snd))
      refine Continuous.smul (M := ℂ) ?_ hih
      refine continuous_ofReal.comp ?_
      simp only [mulVec, dotProduct, Matrix.neg_apply, Matrix.mul_apply, transpose_apply]
      exact continuous_finset_sum _ fun b _ => Continuous.mul (Continuous.neg (continuous_finset_sum _ fun c _ =>
        Continuous.mul (continuous_finset_sum _ fun d _ => continuous_const.mul
          ((hentry _ _).comp continuous_fst)) continuous_const)) continuous_const
    · simp only [ContinuousLinearMap.zero_apply, map_zero]
      exact continuous_const
    · intro A B hA hB
      simp only [ContinuousLinearMap.add_apply, map_add]
      exact hA.add hB
    · intro c A hA
      simp only [ContinuousLinearMap.smul_apply, map_smul]
      exact hA.const_smul c
  rw [continuous_iff_continuousAt]
  intro x0
  unfold ContinuousAt
  rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨A, hA, hb⟩ := exists_seminorm_le (l := l) k n
  have ht : Filter.Tendsto (fun x : G × Sch l => ∑ r, ‖schwartzToL2 l (A r (omS x.1 x.2)) - schwartzToL2 l (A r (omS x0.1 x0.2))‖)
      (nhds x0) (nhds 0) := by
    have : (0 : ℝ) = ∑ r : Fin n → l, ‖schwartzToL2 l (A r (omS x0.1 x0.2)) - schwartzToL2 l (A r (omS x0.1 x0.2))‖ := by simp
    rw [this]
    exact tendsto_finset_sum _ fun r _ => ((((key (hA r)).sub continuous_const).norm).tendsto x0)
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with x hx
  refine lt_of_le_of_lt ?_ hx
  rw [SchwartzMap.schwartzSeminormFamily_apply]
  refine (hb _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← schwartzToL2_apply, map_sub, map_sub]

end GlobalTheory.RealWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosineSquarePushforwardUniform
section
set_option autoImplicit false

open MeasureTheory
open scoped ComplexOrder ENNReal

noncomputable section

namespace GlobalTheory.LineCos.FsLaw

open GlobalTheory.LineCos

theorem re_det_pos {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) : 0 < G.det.re :=
  (Complex.pos_iff.1 hG.det_pos).1

theorem corner_eq {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) : G 0 0 = ((G 0 0).re : ℂ) := by
  have h := hG.isHermitian.apply 0 0
  exact (Complex.conj_eq_iff_re.1 h).symm

theorem hform_single (G : Matrix (Fin 2) (Fin 2) ℂ) (w : Fin 2 → ℂ) :
    hform G w (Pi.single 0 1) = w 0 * G 0 0 + w 1 * G 1 0 := by
  simp [hform, Fin.sum_univ_two]

theorem re_hform_mul {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (w : Fin 2 → ℂ) :
    (hform G w w).re * (G 0 0).re = ‖w 0 * G 0 0 + w 1 * G 1 0‖ ^ 2 + G.det.re * ‖w 1‖ ^ 2 := by
  have h00 : (G 0 0).im = 0 := Complex.conj_eq_iff_im.1 (hG.isHermitian.apply 0 0)
  have h11 : (G 1 1).im = 0 := Complex.conj_eq_iff_im.1 (hG.isHermitian.apply 1 1)
  have h01 : G 0 1 = starRingEnd ℂ (G 1 0) := (hG.isHermitian.apply 0 1).symm
  simp only [hform, Fin.sum_univ_two, Matrix.det_fin_two, h01, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.conj_re, Complex.conj_im,
    h00, h11]
  ring

theorem measurable_lineVec (s : Bool) (i : Fin 2) : Measurable fun x : ℂ => lineVec s x i := by
  cases s
  · fin_cases i
    · exact measurable_const
    · exact measurable_id
  · fin_cases i
    · exact measurable_id
    · exact measurable_const

theorem measurable_hform (G : Matrix (Fin 2) (Fin 2) ℂ) {a b : ℂ → Fin 2 → ℂ} (ha : ∀ i, Measurable fun x => a x i)
    (hb : ∀ i, Measurable fun x => b x i) : Measurable fun x => hform G (a x) (b x) := by
  unfold hform
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact ((ha i).mul (Complex.continuous_conj.measurable.comp (hb j))).mul_const _

theorem measurable_cosSq (s : Bool) (G : Matrix (Fin 2) (Fin 2) ℂ) : Measurable (cosSq s G) := by
  have h1 : Measurable fun x : ℂ => hform G (lineVec s x) (Pi.single (0 : Fin 2) (1 : ℂ)) :=
    measurable_hform G (b := fun _ => Pi.single (0 : Fin 2) (1 : ℂ)) (measurable_lineVec s) fun _ => measurable_const
  have h2 : Measurable fun x : ℂ => (hform G (lineVec s x) (lineVec s x)).re :=
    Complex.measurable_re.comp (measurable_hform G (measurable_lineVec s) (measurable_lineVec s))
  exact (h1.norm.pow_const 2).div (h2.mul_const _)

theorem lintegral_reflect (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, g (1 - t) = ∫⁻ t in Set.Ioo (0 : ℝ) 1, g t := by
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo,
    ← lintegral_sub_left_eq_self ((Set.Ioo (0 : ℝ) 1).indicator g) 1]
  congr 1
  funext t
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
  · have : 1 - t ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simp only [Set.indicator_of_mem ht, Set.indicator_of_mem this]
  · have : 1 - t ∉ Set.Ioo (0 : ℝ) 1 := fun h => ht ⟨by linarith [h.2], by linarith [h.1]⟩
    simp only [Set.indicator_of_notMem ht, Set.indicator_of_notMem this]

theorem lintegral_false {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x : ℂ, ENNReal.ofReal (G.det.re / (Real.pi * (hform G (lineVec false x) (lineVec false x)).re ^ 2)) *
      g (cosSq false G x) = ∫⁻ t in Set.Ioo (0 : ℝ) 1, g t := by
  set a : ℝ := (G 0 0).re with ha_def
  set D : ℝ := G.det.re with hD_def
  have ha : 0 < a := re_corner_pos hG
  have hD : 0 < D := re_det_pos hG
  have hG0 : G 0 0 = (a : ℂ) := corner_eq hG
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hc : ((Real.sqrt D / a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (div_pos (Real.sqrt_pos.2 hD) ha).ne'
  have hH : Measurable fun x : ℂ =>
      g (1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)) := by
    have : Measurable fun x : ℂ => g (1 / (1 + ‖x‖ ^ 2)) := hg.comp (by fun_prop)
    fun_prop
  rw [← GlobalTheory.FibLine.lintegral_comp_fsDens g hg,
    ← GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius (G 1 0 / a) _ hc _ hH]
  refine lintegral_congr_ae ?_
  filter_upwards [GlobalTheory.FibLine.UnitaryInv.ae_affine_ne 1 (G 1 0 / a) (Or.inl one_ne_zero)] with x hx
  have hsq := re_hform_mul hG (lineVec false x)
  have hone := hform_single G (lineVec false x)
  have hw0 : lineVec false x 0 = 1 := rfl
  have hw1 : lineVec false x 1 = x := rfl
  have hp : 1 * G 0 0 + x * G 1 0 = a * (1 + G 1 0 / a * x) := by
    rw [hG0]; field_simp
  rw [hw0, hw1, hp] at hsq hone
  set q : ℝ := ‖1 + G 1 0 / a * x‖ with hq_def
  have hq : 0 < q := norm_pos_iff.2 hx
  have hn : ‖(a : ℂ) * (1 + G 1 0 / a * x)‖ = a * q := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
  have hcn : ‖((Real.sqrt D / a : ℝ) : ℂ)‖ ^ 2 = D / a ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hD.le]
  have hy : ‖((Real.sqrt D / a : ℝ) : ℂ) * x / (1 + G 1 0 / a * x)‖ ^ 2 = D / a ^ 2 * ‖x‖ ^ 2 / q ^ 2 := by
    rw [norm_div, norm_mul, div_pow, mul_pow, hcn]
  have hj : ‖((Real.sqrt D / a : ℝ) : ℂ) / (1 + G 1 0 / a * x) ^ 2‖ ^ 2 = D / a ^ 2 / q ^ 4 := by
    rw [norm_div, norm_pow, div_pow, hcn, ← pow_mul]
  rw [hn, ← ha_def, ← hD_def] at hsq
  have hh : (hform G (lineVec false x) (lineVec false x)).re = ((a * q) ^ 2 + D * ‖x‖ ^ 2) / a :=
    eq_div_of_mul_eq ha.ne' hsq
  have hcos : cosSq false G x = 1 / (1 + D / a ^ 2 * ‖x‖ ^ 2 / q ^ 2) := by
    unfold cosSq
    rw [hone, hn, ← ha_def, hsq]
    field_simp
  have hpi := Real.pi_pos
  rw [hy, hj, hcos, hh, mul_left_comm, mul_comm, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

theorem lintegral_true {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x : ℂ, ENNReal.ofReal (G.det.re / (Real.pi * (hform G (lineVec true x) (lineVec true x)).re ^ 2)) *
      g (cosSq true G x) = ∫⁻ t in Set.Ioo (0 : ℝ) 1, g t := by
  set a : ℝ := (G 0 0).re with ha_def
  set D : ℝ := G.det.re with hD_def
  have ha : 0 < a := re_corner_pos hG
  have hD : 0 < D := re_det_pos hG
  have hG0 : G 0 0 = (a : ℂ) := corner_eq hG
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hc : ((a / Real.sqrt D : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (div_pos ha (Real.sqrt_pos.2 hD)).ne'
  have hg' : Measurable fun t : ℝ => g (1 - t) := hg.comp (by fun_prop)
  have hH : Measurable fun x : ℂ =>
      g (1 - 1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)) := by
    have : Measurable fun x : ℂ => g (1 - 1 / (1 + ‖x‖ ^ 2)) := hg.comp (by fun_prop)
    fun_prop
  rw [← lintegral_reflect, ← GlobalTheory.FibLine.lintegral_comp_fsDens _ hg',
    ← GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius 0 _ hc _ hH,
    ← lintegral_sub_right_eq_self _ (G 1 0 / a)]
  refine lintegral_congr fun x => ?_
  have hsq := re_hform_mul hG (lineVec true (x - G 1 0 / a))
  have hone := hform_single G (lineVec true (x - G 1 0 / a))
  have hw0 : lineVec true (x - G 1 0 / a) 0 = x - G 1 0 / a := rfl
  have hw1 : lineVec true (x - G 1 0 / a) 1 = 1 := rfl
  have hp : (x - G 1 0 / a) * G 0 0 + 1 * G 1 0 = a * x := by
    rw [hG0]; field_simp; ring
  rw [hw0, hw1, hp] at hsq hone
  have hn : ‖(a : ℂ) * x‖ = a * ‖x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
  have hcn : ‖((a / Real.sqrt D : ℝ) : ℂ)‖ ^ 2 = a ^ 2 / D := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hD.le]
  have hy : ‖((a / Real.sqrt D : ℝ) : ℂ) * x / (1 + 0 * x)‖ ^ 2 = a ^ 2 / D * ‖x‖ ^ 2 := by
    rw [zero_mul, add_zero, div_one, norm_mul, mul_pow, hcn]
  have hj : ‖((a / Real.sqrt D : ℝ) : ℂ) / (1 + 0 * x) ^ 2‖ ^ 2 = a ^ 2 / D := by
    rw [zero_mul, add_zero, one_pow, div_one, hcn]
  rw [hn, ← ha_def, ← hD_def, norm_one, one_pow, mul_one] at hsq
  have hh : (hform G (lineVec true (x - G 1 0 / a)) (lineVec true (x - G 1 0 / a))).re = ((a * ‖x‖) ^ 2 + D) / a :=
    eq_div_of_mul_eq ha.ne' hsq
  have hcos : cosSq true G (x - G 1 0 / a) = 1 - 1 / (1 + a ^ 2 / D * ‖x‖ ^ 2) := by
    unfold cosSq
    rw [hone, hn, ← ha_def, hsq]
    field_simp
    ring
  have hpi := Real.pi_pos
  rw [hy, hj, hcos, hh, mul_left_comm, mul_comm, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp
  ring

theorem map_cosSq_fs (G : Matrix (Fin 2) (Fin 2) ℂ) (s : Bool) (hG : G.PosDef) :
    Measure.map (cosSq s G)
        (volume.withDensity fun x : ℂ => ENNReal.ofReal (G.det.re /
          (Real.pi * (hform G (lineVec s x) (lineVec s x)).re ^ 2))) =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
  have hd : Measurable fun x : ℂ => ENNReal.ofReal (G.det.re /
      (Real.pi * (hform G (lineVec s x) (lineVec s x)).re ^ 2)) := by
    have := Complex.measurable_re.comp (measurable_hform G (measurable_lineVec s) (measurable_lineVec s))
    exact (measurable_const.div ((this.pow_const 2).const_mul _)).ennreal_ofReal
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  rw [lintegral_map hg (measurable_cosSq s G),
    lintegral_withDensity_eq_lintegral_mul _ hd (g := fun x => g (cosSq s G x)) (hg.comp (measurable_cosSq s G)),
    ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  cases s
  · exact lintegral_false hG g hg
  · exact lintegral_true hG g hg

end GlobalTheory.LineCos.FsLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveDegreeUnique
section
open IsLocalRing Polynomial

namespace GlobalTheory.EtalePolyDvr

theorem isDiscreteValuationRing_atPrime_of_etale_polynomial :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (E : Type) [CommRing E] [Algebra A[X] E] [Algebra A E] [IsScalarTower A A[X] E]
    [Algebra.Etale A[X] E] (Q : Ideal E) [Q.IsPrime] (P : Ideal (Localization.AtPrime Q)) [P.IsPrime]
    (p : Ideal A) [p.IsPrime], p.height = 1 →
    P.comap (algebraMap A[X] (Localization.AtPrime Q)) = p.map (Polynomial.C : A →+* A[X]) →
    (∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P)) ∧
      ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime p) π) →
        Irreducible (algebraMap A (Localization.AtPrime P) π) := by
  intro A _ _ _ _ E _ _ _ _ _ Q _ P _ p _ hp hP
  classical
  haveI hE : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing A[X] E
  haveI hR : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ hE
  haveI hLPn : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ hR
  let Q' : Ideal E := P.comap (algebraMap E (Localization.AtPrime Q))
  haveI hQ' : Q'.IsPrime := Ideal.comap_isPrime _ _
  haveI hLoc : IsLocalization.AtPrime (Localization.AtPrime P) Q' :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization Q.primeCompl
      (Localization.AtPrime P) P
  let e : Localization.AtPrime Q' ≃ₐ[E] Localization.AtPrime P :=
    IsLocalization.algEquiv Q'.primeCompl _ _
  haveI hAp : IsDomain (Localization.AtPrime p) :=
    IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors
  haveI hApd : IsDiscreteValuationRing (Localization.AtPrime p) :=
    GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp _
  have hAL : ∀ a : A, algebraMap A (Localization.AtPrime Q') a =
      algebraMap E (Localization.AtPrime Q') (algebraMap A E a) := fun a =>
    IsScalarTower.algebraMap_apply A E _ a
  have hALP : ∀ a : A, algebraMap A (Localization.AtPrime P) a =
      algebraMap E (Localization.AtPrime P) (algebraMap A E a) := fun a => by
    rfl
  have he : ∀ a : A, e (algebraMap A (Localization.AtPrime Q') a) =
      algebraMap A (Localization.AtPrime P) a := by
    intro a; rw [hAL, hALP, e.commutes]
  have hunder : Q'.comap (algebraMap A[X] E) = p.map C := by
    rw [← hP]
    show Ideal.comap _ (Ideal.comap _ P) = _
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  have hunderA : ∀ a : A, algebraMap A E a ∈ Q' ↔ a ∈ p := by
    intro a
    rw [IsScalarTower.algebraMap_apply A A[X] E, ← Ideal.mem_comap, hunder,
      Polynomial.algebraMap_eq, Ideal.mem_map_C_iff]
    refine ⟨fun h => by simpa using h 0, fun h n => ?_⟩
    rw [Polynomial.coeff_C]
    split_ifs
    · exact h
    · exact p.zero_mem
  have hcomp : (algebraMap A[X] (Localization.AtPrime Q')).comp C =
      algebraMap A (Localization.AtPrime Q') := by
    ext a
    simp only [RingHom.comp_apply]
    rw [hAL, IsScalarTower.algebraMap_apply A A[X] E, Polynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply A[X] E (Localization.AtPrime Q')]
  have hun : Algebra.IsUnramifiedAt A[X] Q' := inferInstance
  let p0 : Ideal A[X] := Q'.under A[X]
  let := Localization.AtPrime.algebraOfLiesOver p0 Q'
  have hm := ((Algebra.isUnramifiedAt_iff_map_eq A[X] p0 Q').mp hun).2
  have hp0 : p0 = p.map C := hunder
  have hunit : ∀ a : A, a ∉ p → IsUnit (algebraMap A (Localization.AtPrime Q') a) := by
    intro a ha
    by_contra h
    apply ha
    rw [← hunderA, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q') Q', ← hAL]
    exact h
  haveI hflatE : Module.Flat A E := Module.Flat.trans A A[X] E
  haveI hflatL : Module.Flat A (Localization.AtPrime Q') := Module.Flat.trans A E _
  have key : ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime p) π) →
      ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) ∧
        Irreducible (algebraMap A (Localization.AtPrime P) π) := by
    intro π hπ
    have hπp : π ∈ p := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p π]
      exact hπ.not_isUnit
    have hπ0 : π ≠ 0 := by rintro rfl; exact hπ.ne_zero (map_zero _)
    have hmAp := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hπ
    have hmL : maximalIdeal (Localization.AtPrime Q') =
        Ideal.span {algebraMap A (Localization.AtPrime Q') π} := by
      rw [← hm, hp0, Ideal.map_map, hcomp]
      apply le_antisymm
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        have h1 : algebraMap A (Localization.AtPrime p) a ∈ maximalIdeal _ :=
          (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p a).mpr ha
        rw [hmAp, Ideal.mem_span_singleton'] at h1
        obtain ⟨c, hc⟩ := h1
        obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl c
        have h2 : algebraMap A (Localization.AtPrime p) (a * s) =
            algebraMap A (Localization.AtPrime p) (b * π) := by
          rw [map_mul, map_mul, ← hc, mul_right_comm, IsLocalization.mk'_spec]
        obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists p.primeCompl _).mp h2
        have hts : (t : A) * s ∉ p := p.primeCompl.mul_mem t.2 s.2
        rw [Ideal.mem_comap, Ideal.mem_span_singleton,
          ← (hunit _ hts).dvd_mul_right, ← map_mul]
        have h3 : a * ((t : A) * s) = π * ((t : A) * b) := by linear_combination ht
        rw [h3, map_mul]
        exact dvd_mul_right _ _
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        exact Ideal.mem_map_of_mem _ hπp
    have hreg : ∀ x : Localization.AtPrime Q', algebraMap A _ π * x = 0 → x = 0 := by
      intro x hx
      have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Localization.AtPrime Q')
        (mem_nonZeroDivisors_of_ne_zero hπ0)
      exact this (show π • x = π • (0 : Localization.AtPrime Q') by
        rw [smul_zero, Algebra.smul_def, hx])
    have hmem : ∀ y : Localization.AtPrime Q',
        e y ∈ maximalIdeal (Localization.AtPrime P) ↔ y ∈ maximalIdeal _ := by
      intro y
      simp only [mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
    have hmLP : maximalIdeal (Localization.AtPrime P) =
        Ideal.span {algebraMap A (Localization.AtPrime P) π} := by
      ext x
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [hmem, hmL, Ideal.mem_span_singleton, Ideal.mem_span_singleton, ← he, map_dvd_iff]
    have hregP : ∀ x : Localization.AtPrime P, algebraMap A _ π * x = 0 → x = 0 := by
      intro x hx
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [← he, ← map_mul, map_eq_zero_iff _ e.injective] at hx
      rw [hreg y hx, map_zero]
    exact GlobalTheory.Pat.dvr_of_maximalIdeal_eq_span hmLP hregP
  refine ⟨?_, fun π hπ => (key π hπ).2.2⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl ϖ
  have ha : Irreducible (algebraMap A (Localization.AtPrime p) a) := by
    have h := IsLocalization.mk'_spec (Localization.AtPrime p) a s
    rw [← h]
    exact (irreducible_mul_isUnit (IsLocalization.map_units _ s)).mpr hϖ
  obtain ⟨hd, hdvr, -⟩ := key a ha
  exact ⟨hd, hdvr⟩

end GlobalTheory.EtalePolyDvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlocksTwistedConjBlockUpperTriangular
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.BlocksTwist

theorem toG_map {F : Type} [Field F] (t : F →+* F) {m : ℕ} (M : Matrix (Fin m) (Fin m) F) (h : IsUnit M) :
    toG (M.map t) = gal t m (toG M) := by
  have h' : IsUnit (M.map t) := by simpa using h.map (t.mapMatrix)
  unfold toG
  rw [dif_pos h', dif_pos h]
  ext i j
  simp [gal]

theorem coe_gal {F : Type} [Field F] (t : F →+* F) (n : ℕ) (p : GL (Fin n) F) :
    ((gal t n p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = (p : Matrix (Fin n) (Fin n) F).map t := by
  simp [gal]

theorem ent_map {F : Type} [Field F] (t : F →+* F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) :
    ent (M.map t) i j = t (ent M i j) := by
  unfold ent
  split_ifs <;> simp

theorem tl_map {F : Type} [Field F] (t : F →+* F) (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    tl a (M.map t) = (tl a M).map t := by
  ext i j; simp [tl, ent_map]

theorem br_map {F : Type} [Field F] (t : F →+* F) (a b : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    br a b (M.map t) = (br a b M).map t := by
  ext i j; simp [br, ent_map]

theorem inPar_gal {F : Type} [Field F] (t : F →+* F) (a : ℕ) {n : ℕ} (p : GL (Fin n) F) (hp : InPar a p) :
    InPar a (gal t n p) := by
  intro i j hj hi
  rw [coe_gal]
  simp [hp i j hj hi]

theorem blocks_twist : ∀ (F : Type) [Field F] (t : F →+* F) (a b n : ℕ), n = a + b → ∀ (p x : GL (Fin n) F), InPar a p → InPar a x → tlG a (p⁻¹ * x * gal t n p) = (tlG a p)⁻¹ * tlG a x * gal t a (tlG a p) ∧ brG a b (p⁻¹ * x * gal t n p) = (brG a b p)⁻¹ * brG a b x * gal t b (brG a b p) := by
  intro F _ t a b n hn p x hp hx
  obtain ⟨H, π, hH, -, hπ, -, -⟩ := BlockPar.block_par F a b n hn
  let p' : H := ⟨p, (hH p).2 hp⟩
  let x' : H := ⟨x, (hH x).2 hx⟩
  let g' : H := ⟨gal t n p, (hH _).2 (inPar_gal t a p hp)⟩
  have key : π (p'⁻¹ * x' * g') = (π p')⁻¹ * π x' * π g' := by simp only [map_mul, map_inv]
  rw [hπ, hπ, hπ, hπ] at key
  have e : ((p'⁻¹ * x' * g' : H) : GL (Fin n) F) = p⁻¹ * x * gal t n p := rfl
  rw [e] at key
  have htl : tlG a (gal t n p) = gal t a (tlG a p) := by
    subst hn
    unfold tlG
    rw [coe_gal, tl_map, toG_map _ _ (BlockPar.units_of_par p hp).1]
  have hbr : brG a b (gal t n p) = gal t b (brG a b p) := by
    subst hn
    unfold brG
    rw [coe_gal, br_map, toG_map _ _ (BlockPar.units_of_par p hp).2]
  simp only [Prod.ext_iff, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] at key
  rw [← htl, ← hbr]
  exact key

end GlobalTheory.Shin.BlocksTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyFractionalIdealRealLatticeImageStatement
section
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteTopology_fractionalIdealRealLatticeImage : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), DiscreteTopology (latOf N) := by
  first | exact @GlobalTheory.LipschitzTR.discrete_latOf | exact GlobalTheory.LipschitzTR.discrete_latOf | (intros; apply GlobalTheory.LipschitzTR.discrete_latOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeImageEqLatticeImageTraceDualStatement
section
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_latticeImage_eq_latticeImage_traceDual : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := by
  first | exact @GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual | exact GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual | (intros; apply GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenProjectionQuotientLatticeStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_projection_quotient_lattice : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → ∃ π : (Fin h → C) →ₗ[C] eig C ρ τ, (∀ x : eig C ρ τ, π x = x) ∧ (∀ (z : Fin h → C) (x : eig C ρ τ), (z - (x : Fin h → C) ∈ ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ σ.1) ↔ x = π z) ∧ quotLattice C ρ τ = Set.range (fun t : Fin h → O => π (fun i => algebraMap O C (t i))) := by
  first | exact @GlobalTheory.eig_projection_quotLattice | exact GlobalTheory.eig_projection_quotLattice | (intros; apply GlobalTheory.eig_projection_quotLattice <;> assumption)
end

