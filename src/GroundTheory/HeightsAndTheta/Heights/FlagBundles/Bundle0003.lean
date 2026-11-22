import Mathlib
import GroundTheory.PAdicHodge.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PPluckerFrameChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Matrix Finset

theorem PluckerFrameChange.proof : PluckerFrameChange.Statement := by
  classical
  intro R _ l N V g I hI
  have hmul : (V * g).submatrix id (I.orderEmbOfFin hI) =
      V * g.submatrix id (I.orderEmbOfFin hI) := by
    ext i j; simp [Matrix.mul_apply]
  have hL : pluckerCoord (V * g) I =
      ∑ s : GroundTheory.PAdicHodge.KSubset N l,
        (V.submatrix id s.emb).det *
          ((g.submatrix id (I.orderEmbOfFin hI)).submatrix s.emb id).det := by
    rw [pluckerCoord, dif_pos hI, hmul, GroundTheory.PAdicHodge.det_mul_eq_sum_minors]
  rw [hL, Finset.sum_subtype (Finset.powersetCard l (Finset.univ : Finset (Fin N)))
    (p := fun J : Finset (Fin N) => J.card = l) (fun J => Finset.mem_powersetCard_univ)]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h2 : s.1.card = l ∧ I.card = l := ⟨s.2, hI⟩
  rw [pluckerCoord, dif_pos s.2, minorOn, dif_pos h2]
  rfl

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PPolarisationDegreeD
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial Finset

theorem PolarisationDegreeD.proof : PolarisationDegreeD.Statement := by
  intro K _ _ r D φ ψ h P hP
  set χ : MvPolynomial (Fin r) K →ₗ[K] K := φ - ψ with hχdef
  have hχ : ∀ c : Fin r → K, χ ((∑ i, C (c i) * X i) ^ D) = 0 := fun c => by
    simp [hχdef, h c]

  have hmono : ∀ k : Fin r → ℕ, (∏ i, X i ^ k i : MvPolynomial (Fin r) K) =
      monomial (Finsupp.equivFunOnFinite.symm k) 1 := by
    intro k
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    simp

  have hexp : ∀ c : Fin r → K, (∑ i, C (c i) * X i : MvPolynomial (Fin r) K) ^ D =
      ∑ k ∈ piAntidiag univ D,
        C ((Nat.multinomial univ k : K) * ∏ i, c i ^ k i) * ∏ i, X i ^ k i := by
    intro c
    rw [sum_pow_eq_sum_piAntidiag]
    refine sum_congr rfl fun k _ => ?_
    simp only [mul_pow, prod_mul_distrib, map_mul, map_prod, map_pow, map_natCast]
    ring

  set Q : MvPolynomial (Fin r) K := ∑ k ∈ piAntidiag univ D,
      C ((Nat.multinomial univ k : K) * χ (∏ i, X i ^ k i)) * ∏ i, X i ^ k i with hQdef
  have hQ : Q = 0 := by
    apply MvPolynomial.funext
    intro c
    rw [map_zero, ← hχ c, hexp c, hQdef, map_sum, map_sum]
    refine sum_congr rfl fun k _ => ?_
    have hs : C ((Nat.multinomial univ k : K) * ∏ i, c i ^ k i) * ∏ i, X i ^ k i =
        ((Nat.multinomial univ k : K) * ∏ i, c i ^ k i) • (∏ i, X i ^ k i : MvPolynomial (Fin r) K) :=
      C_mul'
    rw [hs, map_smul, smul_eq_mul, eval_mul, eval_C]
    simp only [map_prod, map_pow, eval_X]
    ring

  have hzero : ∀ k ∈ piAntidiag univ D, χ (∏ i, X i ^ k i) = 0 := by
    intro k hk
    have hc : coeff (Finsupp.equivFunOnFinite.symm k) Q =
        (Nat.multinomial univ k : K) * χ (∏ i, X i ^ k i) := by
      rw [hQdef, coeff_sum]
      simp_rw [hmono, coeff_C_mul, coeff_monomial, EmbeddingLike.apply_eq_iff_eq]
      simp [hk]
    rw [hQ, coeff_zero] at hc
    have hm : (Nat.multinomial univ k : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.multinomial_pos _ _).ne'
    exact (mul_eq_zero.mp hc.symm).resolve_left hm

  have hP0 : χ P = 0 := by
    rw [as_sum P, map_sum]
    refine sum_eq_zero fun d hd => ?_
    have hdeg : ∑ i, d i = D := by
      rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
      exact hP (mem_support_iff.mp hd)
    have hmem : (⇑d : Fin r → ℕ) ∈ piAntidiag univ D := by
      simp [hdeg]
    have hd1 : monomial d (coeff d P) = coeff d P • monomial d (1 : K) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hd1, map_smul, smul_eq_mul]
    have := hzero _ hmem
    rw [hmono, Finsupp.equivFunOnFinite_symm_coe] at this
    rw [this, mul_zero]
  have := hP0
  rw [hχdef, LinearMap.sub_apply, sub_eq_zero] at this
  exact this

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSectionLocalEquation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Submodule

theorem quotient_span_bijective_second_basis {R : Type} [CommRing R] (v : Fin 2 → R) (hv : v 0 = 1) :
    Function.Bijective (fun r : R => r • (span R {v}).mkQ (eps R 1)) := by
  constructor
  · intro r s h
    simp only at h
    rw [← map_smul, ← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq,
      ← sub_smul, mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp [eps, hv] at h0 h1
    subst h0
    simp at h1
    exact sub_eq_zero.mp h1.symm
  · intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    refine ⟨x 1 - x 0 * v 1, ?_⟩
    simp only
    rw [← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq, mem_span_singleton]
    refine ⟨-x 0, ?_⟩
    ext k
    fin_cases k <;> simp [eps, hv]

theorem quotient_span_bijective_first_basis {R : Type} [CommRing R] (v : Fin 2 → R) (hv : v 1 = 1) :
    Function.Bijective (fun r : R => r • (span R {v}).mkQ (eps R 0)) := by
  constructor
  · intro r s h
    simp only at h
    rw [← map_smul, ← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq,
      ← sub_smul, mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp [eps, hv] at h0 h1
    subst h1
    simp at h0
    exact sub_eq_zero.mp h0.symm
  · intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    refine ⟨x 0 - x 1 * v 0, ?_⟩
    simp only
    rw [← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq, mem_span_singleton]
    refine ⟨-x 1, ?_⟩
    ext k
    fin_cases k <;> simp [eps, hv]

theorem SectionLocalEquation.proof : SectionLocalEquation.Statement := by
  intro R _ a₁ a₂ b₁ b₂
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact quotient_span_bijective_second_basis _ (by simp [eps])
  · rw [← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq, mem_span_singleton]
    refine ⟨1, ?_⟩
    ext k
    fin_cases k <;> simp [eps]
  · exact quotient_span_bijective_first_basis _ (by simp [eps])
  · rw [← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq, mem_span_singleton]
    refine ⟨1, ?_⟩
    ext k
    fin_cases k <;> simp [eps]
  · rw [← map_smul, mkQ_apply, mkQ_apply, Submodule.Quotient.eq, mem_span_singleton]
    refine ⟨a₁, ?_⟩
    ext k
    fin_cases k <;> simp [eps]

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSectionNormLog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open scoped InnerProductSpace ComplexConjugate

noncomputable section

theorem quotient_norm_eq_norm_sub_starProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (U : Submodule ℂ E) [U.HasOrthogonalProjection] (x : E) :
    ‖(Submodule.Quotient.mk x : E ⧸ U)‖ = ‖x - U.starProjection x‖ := by
  have h1 : ‖(Submodule.Quotient.mk x : E ⧸ U)‖ = Metric.infDist x (U : Set E) :=
    QuotientAddGroup.norm_mk (S := U.toAddSubgroup) x
  rw [h1, Metric.infDist_eq_iInf, Submodule.starProjection_minimal]
  simp only [dist_eq_norm]
  rfl

theorem quotient_norm_sq_line {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e₁ e₂ : E) (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) :
    ‖(Submodule.Quotient.mk e₁ : E ⧸ ℂ ∙ e₂)‖ ^ 2 = 1 - ‖⟪e₁, e₂⟫_ℂ‖ ^ 2 := by
  rw [quotient_norm_eq_norm_sub_starProjection, Submodule.starProjection_unit_singleton ℂ h₂,
    @norm_sub_sq ℂ, inner_smul_right, norm_smul, h₁, h₂, mul_one, ← inner_conj_symm e₁ e₂,
    Complex.norm_conj, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  rw [RCLike.re_to_complex, Complex.ofReal_re]
  ring

theorem SectionNormLog.proof (h0 : BlochOverlap.Statement) : SectionNormLog.Statement := by
  intro e₁ e₂ h₁ h₂
  have hsq := quotient_norm_sq_line e₁ e₂ h₁ h₂
  refine ⟨hsq, fun _ => ?_⟩
  rw [h0.2 e₁ e₂ h₁ h₂] at hsq
  unfold kernelL
  set q := ‖(Submodule.Quotient.mk e₁ : EuclideanSpace ℂ (Fin 2) ⧸ ℂ ∙ e₂)‖
  have : (1 - ⟪blochVector e₁, blochVector e₂⟫_ℝ) / 2 = q ^ 2 := by rw [hsq]; ring
  rw [this, Real.log_pow]
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSphereMoment
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

lemma SphereMoment.exists_unit (a : E3) :
    ∃ u : E3, ‖u‖ = 1 ∧ ∀ n : E3, ⟪a, n⟫_ℝ = ‖a‖ * ⟪u, n⟫_ℝ := by
  by_cases h : a = 0
  · refine ⟨EuclideanSpace.single 0 1, by simp, fun n => by simp [h]⟩
  · have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr h
    refine ⟨‖a‖⁻¹ • a, ?_, fun n => ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hna]
    · rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hna, one_mul]

lemma SphereMoment.moment (h0 : SphereHeightUniform.Statement) (a : E3) (k : ℕ) :
    ∫ n, ⟪a, (n : E3)⟫_ℝ ^ k ∂sphereMeasure =
      ‖a‖ ^ k * (2⁻¹ * ((1 - (-1 : ℝ) ^ (k + 1)) / (k + 1))) := by
  obtain ⟨u, hu, ha⟩ := SphereMoment.exists_unit a
  have hc : Continuous fun n : Sphere2 => ⟪u, (n : E3)⟫_ℝ :=
    continuous_const.inner continuous_subtype_val
  calc ∫ n, ⟪a, (n : E3)⟫_ℝ ^ k ∂sphereMeasure
      = ∫ n, ‖a‖ ^ k * ⟪u, (n : E3)⟫_ℝ ^ k ∂sphereMeasure := by
        simp_rw [ha, mul_pow]
    _ = ‖a‖ ^ k * ∫ n, ⟪u, (n : E3)⟫_ℝ ^ k ∂sphereMeasure := integral_const_mul _ _
    _ = ‖a‖ ^ k * ∫ t, t ^ k ∂(sphereMeasure.map fun n : Sphere2 => ⟪u, (n : E3)⟫_ℝ) := by
        rw [integral_map hc.measurable.aemeasurable
          (continuous_pow k).aestronglyMeasurable]
    _ = ‖a‖ ^ k * (2⁻¹ * ((1 - (-1 : ℝ) ^ (k + 1)) / (k + 1))) := by
        rw [h0 u hu, integral_smul_measure, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by norm_num), integral_pow]
        simp [smul_eq_mul]

theorem SphereMoment.proof (h0 : SphereHeightUniform.Statement) : SphereMoment.Statement := by
  intro a m
  refine ⟨?_, ?_⟩
  · rw [SphereMoment.moment h0, pow_succ, pow_mul]
    have h2 : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    norm_num
    field_simp
  · rw [SphereMoment.moment h0, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul]
    norm_num

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PTopPowerDiagonal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Finset

theorem add_pow_succ_of_sq_eq_zero {S : Type*} [CommRing S] {x y : S} (hx : x ^ 2 = 0)
    (m : ℕ) : (x + y) ^ (m + 1) = y ^ (m + 1) + ((m : S) + 1) * x * y ^ m := by
  induction m with
  | zero => simp [add_comm]
  | succ m ih =>
    push_cast
    linear_combination (x + y) * ih + ((m : S) + 1) * y ^ m * hx

theorem sum_pow_card_of_sq_eq_zero {S ι : Type*} [CommRing S] [DecidableEq ι] (x : ι → S)
    (hx : ∀ j, x j ^ 2 = 0) (s : Finset ι) :
    (∑ j ∈ s, x j) ^ (s.card + 1) = 0 ∧
      (∑ j ∈ s, x j) ^ s.card = (s.card.factorial : S) * ∏ j ∈ s, x j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [sum_insert ha, prod_insert ha, card_insert_of_notMem ha]
    constructor
    · rw [add_pow_succ_of_sq_eq_zero (hx a) (s.card + 1), pow_succ, h1]
      simp
    · rw [add_pow_succ_of_sq_eq_zero (hx a) s.card, h1, h2, Nat.factorial_succ]
      push_cast
      ring

theorem TopPowerDiagonal.proof : TopPowerDiagonal.Statement := by
  intro S _ D ω lam hω
  have h := (sum_pow_card_of_sq_eq_zero (fun j => lam j * ω j)
    (fun j => by rw [mul_pow, hω j, mul_zero]) (univ : Finset (Fin D))).2
  rw [card_univ, Fintype.card_fin, prod_mul_distrib] at h
  rw [h, mul_assoc]

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PTorusInvariantDiagonal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open scoped ComplexConjugate

theorem TorusInvariantDiagonal.proof : TorusInvariantDiagonal.Statement := by
  intro ι T V _ _ _ _ _ _ ρ L χ _ _ hχ hρ h _ hinv i j hij x hx y hy
  by_contra hne
  apply hij
  apply hχ
  ext t
  have key := hinv t x y
  rw [hρ i x hx t, hρ j y hy t] at key
  simp only [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul] at key

  have h1 : conj ((χ i t : Circle) : ℂ) * ((χ j t : Circle) : ℂ) = 1 := by
    have : (conj ((χ i t : Circle) : ℂ) * ((χ j t : Circle) : ℂ) - 1) * h x y = 0 := by
      linear_combination key
    rcases mul_eq_zero.1 this with h2 | h2
    · linear_combination h2
    · exact absurd h2 hne
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, Circle.coe_eq_one, inv_mul_eq_one] at h1
  exact congrArg (fun z : Circle => (z : ℂ)) h1

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PUnipotentCoordinates
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial Finset

noncomputable section

private def leadCols {N : ℕ} (m l : Fin N) (j : Fin (l.val + 1)) : Fin N :=
  if hj : j.val < l.val then ⟨j.val, lt_trans hj l.isLt⟩ else m

private lemma leadCols_strictMono {N : ℕ} (m l : Fin N) (h : l < m) :
    StrictMono (leadCols m l) := by
  intro i j hij
  have hij' : i.val < j.val := hij
  have hlm : l.val < m.val := h
  unfold leadCols
  by_cases hi : i.val < l.val <;> by_cases hj : j.val < l.val <;>
    simp only [hi, hj, dite_true, dite_false, Fin.lt_def] <;> omega

private lemma leadCols_mem {N : ℕ} (m l : Fin N) (j : Fin (l.val + 1)) :
    leadCols m l j ∈ insert m (Finset.Iio l) := by
  unfold leadCols
  split_ifs with hj
  · exact Finset.mem_insert_of_mem (Finset.mem_Iio.2 (Fin.lt_def.2 hj))
  · exact Finset.mem_insert_self _ _

private lemma card_leadCols {N : ℕ} (m l : Fin N) (h : l < m) :
    (insert m (Finset.Iio l)).card = l.val + 1 := by
  rw [Finset.card_insert_of_notMem (by simp [not_lt.2 h.le]), Fin.card_Iio]

theorem unipotent_pluckerCoord_eq {R : Type} [CommRing R] {N : ℕ} (a : LowerPairs N → R)
    (m l : Fin N) (h : l < m) :
    pluckerCoord (firstRows (unipotentMatrix a) (l.val + 1) l.isLt) (insert m (Finset.Iio l)) =
      a ⟨(m, l), h⟩ := by
  have hc := card_leadCols m l h
  have hemb : ((insert m (Finset.Iio l)).orderEmbOfFin hc : Fin (l.val + 1) → Fin N) =
      leadCols m l :=
    (Finset.orderEmbOfFin_unique hc (leadCols_mem m l) (leadCols_strictMono m l h)).symm
  have hlm : l.val < m.val := h
  unfold pluckerCoord
  rw [dif_pos hc]
  set M := (firstRows (unipotentMatrix a) (l.val + 1) l.isLt).submatrix id
    ((insert m (Finset.Iio l)).orderEmbOfFin hc) with hM
  have hentry : ∀ i j : Fin (l.val + 1),
      M i j = unipotentMatrix a (Fin.castLE l.isLt i) (leadCols m l j) := by
    intro i j
    simp only [hM, Matrix.submatrix_apply, id, firstRows, hemb]
  have htri : M.IsUpperTriangular := by
    intro i j hji
    have hji' : j.val < i.val := hji
    rw [hentry]
    have hj : j.val < l.val := by have := i.isLt; omega
    simp only [unipotentMatrix, leadCols, hj, dite_true, Matrix.of_apply]
    rw [dif_neg, if_neg]
    · intro he; have := congrArg Fin.val he; simp at this; omega
    · intro hlt; have := Fin.lt_def.1 hlt; simp at this; omega
  rw [Matrix.det_of_isUpperTriangular htri, Fin.prod_univ_castSucc]
  have hone : ∀ i : Fin l.val, M i.castSucc i.castSucc = 1 := by
    intro i
    rw [hentry]
    have hi : (i.castSucc : Fin (l.val + 1)).val < l.val := by simp
    simp only [unipotentMatrix, leadCols, hi, dite_true, Matrix.of_apply]
    rw [dif_neg, if_pos]
    · ext; simp
    · intro hlt; have := Fin.lt_def.1 hlt; simp at this
  have hlast : M (Fin.last l.val) (Fin.last l.val) = a ⟨(m, l), h⟩ := by
    rw [hentry]
    have hl : ¬ (Fin.last l.val).val < l.val := by simp
    have hcast : (Fin.castLE l.isLt (Fin.last l.val) : Fin N) = l := by ext; simp
    simp only [unipotentMatrix, leadCols, hl, dite_false, Matrix.of_apply, hcast]
    rw [dif_pos h]
  rw [Finset.prod_eq_one (fun i _ => hone i), hlast, one_mul]

theorem unipotent_pluckerCoord_adjoin (R : Type) [CommRing R] (N : ℕ) :
    Algebra.adjoin R (Set.range fun x : Fin (N + 1) × Finset (Fin N) =>
        pluckerCoord (firstRows (genericUnipotent R N) x.1.val (Nat.le_of_lt_succ x.1.isLt)) x.2) =
      ⊤ := by
  rw [eq_top_iff, ← MvPolynomial.adjoin_range_X, Algebra.adjoin_le_iff]
  rintro _ ⟨p, rfl⟩
  apply Algebra.subset_adjoin
  refine ⟨(⟨p.1.2.val + 1, Nat.succ_lt_succ p.1.2.isLt⟩, insert p.1.1 (Finset.Iio p.1.2)), ?_⟩
  exact unipotent_pluckerCoord_eq (fun q => (X q : MvPolynomial (LowerPairs N) R)) p.1.1 p.1.2 p.2

theorem UnipotentCoordinates.full : UnipotentCoordinates.Statement :=
  ⟨fun _ _ _ a m l h => unipotent_pluckerCoord_eq a m l h,
    fun R _ N => unipotent_pluckerCoord_adjoin R N⟩

theorem UnipotentCoordinates.proof (_h0 : UnipotentLeadingMinor.Statement) :
    UnipotentCoordinates.Statement :=
  UnipotentCoordinates.full

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PUnipotentLeadingMinor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

theorem UnipotentLeadingMinor.proof : UnipotentLeadingMinor.Statement := by
  intro R _ N a l hl
  unfold leadingMinor
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [unipotentMatrix]
  · intro i j hji
    have hji' : Fin.castLE hl j < Fin.castLE hl i := hji
    simp only [Matrix.submatrix_apply, unipotentMatrix, Matrix.of_apply]
    rw [dif_neg (not_lt.mpr hji'.le), if_neg (ne_of_gt hji')]

end GroundTheory.Heights₂.Heights.FlagBundles
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsSphereLongitude
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory

noncomputable section

def SphereLongitudeCoordinates.Statement : Prop :=
  sphereMeasure.map (fun n : Sphere2 => (n : E3)) =
    (ENNReal.ofReal (4 * Real.pi))⁻¹ •
      (volume.restrict (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Ioc 0 (2 * Real.pi))).map
        (fun p : ℝ × ℝ => spherePoint p.1 p.2)

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

