import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0642
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0113
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockRankFourLtTop
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.Fin4
noncomputable section

def pw (t : ℂ) : ℝ := (1 + ‖t‖ ^ 2) ^ (-(4 / 3 : ℝ))

theorem lintegral_pw_lt_top : ∫⁻ t : ℂ, ENNReal.ofReal (pw t) < ⊤ := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 8 / 3)
    (by rw [Complex.finrank_real_complex]; norm_num)
  convert h.lintegral_lt_top using 4
  simp only [pw]; norm_num

theorem gB_eq (w : Low 4 → ℂ) (p0 : ℕ) : gB p0 w =
    (colGram (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 1 ^ 2 * colGram (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 2 ^ 2)⁻¹ := by
  let M : Matrix (Fin 3) (Fin 3) ℂ := blkW p0 w
  show ∏ k : Fin 3, colGram M k.castSucc ^ (-2:ℤ) = (colGram M 1 ^ 2 * colGram M 2 ^ 2)⁻¹
  rw [Fin.prod_univ_three]
  have h0 : colGram M (Fin.castSucc 0) = 1 := by simp [colGram, lminor]
  rw [h0]
  simp only [one_zpow, one_mul, zpow_neg, mul_inv, inv_one]
  rfl

theorem pw_nonneg (t : ℂ) : 0 ≤ pw t := by unfold pw; positivity

theorem measurable_pw : Measurable fun t : ℂ => ENNReal.ofReal (pw t) := by
  unfold pw; fun_prop

theorem blkW_diag (w : Low 4 → ℂ) (p0 : ℕ) : ∀ i, (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) i i = 1 := by
  intro i; fin_cases i <;> simp [blkW, lowMat]

theorem blkW_upper (w : Low 4 → ℂ) (p0 : ℕ) :
    ∀ i j : Fin 3, i < j → (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) i j = 0 := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [blkW, lowMat]

theorem gB_eq_entries (p0 : ℕ) (pa pb pc : Low 4) (w : Low 4 → ℂ)
    (ha : (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 1 0 = w pa)
    (hb : (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 2 0 = w pb)
    (hc : (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 2 1 = w pc) :
    gB p0 w = ((1 + ‖w pa‖ ^ 2 + ‖w pb‖ ^ 2) ^ 2 *
      (1 + ‖w pc‖ ^ 2 + ‖w pa * w pc - w pb‖ ^ 2) ^ 2)⁻¹ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.columnGramDeterminant_unitLower_three (blkW (r := 4) p0 w) (blkW_diag w p0) (blkW_upper w p0)
  rw [gB_eq, h1, h2, ha, hb, hc]

theorem lintegral_hB_lt_top_of_pos (p0 : ℕ) (pa pb pc : Low 4) (hab : pa ≠ pb) (hcb : pc ≠ pb)
    (hac : pa ≠ pc)
    (hg : ∀ w : Low 4 → ℂ, gB p0 w = ((1 + ‖w pa‖ ^ 2 + ‖w pb‖ ^ 2) ^ 2 *
      (1 + ‖w pc‖ ^ 2 + ‖w pa * w pc - w pb‖ ^ 2) ^ 2)⁻¹)
    (hmix : ∀ p : Low 4, p ≠ pa → p ≠ pb → p ≠ pc → (p.1.2 : ℕ) < p0 ∧ p0 ≤ (p.1.1 : ℕ)) :
    ∫⁻ w : Low 4 → ℂ, hB p0 w < ⊤ := by
  set S : Finset (Low 4) := {pa, pb, pc} with hS
  let f : Low 4 → ℂ → ℝ≥0∞ := fun p x =>
    if p ∈ S then ENNReal.ofReal (pw x) else (Metric.closedBall (0 : ℂ) 1).indicator 1 x
  have hf : ∀ p, Measurable (f p) := by
    intro p; by_cases hp : p ∈ S
    · simp only [f, hp, if_true]; exact measurable_pw
    · simp only [f, hp, if_false]; exact measurable_one.indicator measurableSet_closedBall
  let U : (Low 4 → ℂ) → ℝ≥0∞ := fun w => ∏ p, f p (w p)
  have hU : Measurable U := Finset.measurable_prod _ fun p _ => (hf p).comp (measurable_pi_apply p)
  have hUfin : ∫⁻ w, U w < ⊤ := by
    have := GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (μ := fun _ : Low 4 => (volume : Measure ℂ))
      (fun p => (hf p).aemeasurable)
    rw [volume_pi, this]
    refine ENNReal.prod_lt_top fun p _ => ?_
    by_cases hp : p ∈ S
    · simp only [f, hp, if_true]; exact lintegral_pw_lt_top
    · simp only [f, hp, if_false]
      rw [lintegral_indicator measurableSet_closedBall]
      simpa using (measure_closedBall_lt_top (μ := (volume : Measure ℂ)) (x := 0) (r := 1))
  have hUeq : ∀ w : Low 4 → ℂ, (∀ p, p ∉ S → ‖w p‖ ≤ 1) →
      U w = ENNReal.ofReal (pw (w pa)) * ENNReal.ofReal (pw (w pb)) * ENNReal.ofReal (pw (w pc)) := by
    intro w hw
    simp only [U, f]
    rw [Finset.prod_ite, Finset.prod_eq_one (s := Finset.univ.filter (fun p => p ∉ S)) ?_, mul_one]
    · rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hS, Finset.prod_insert, Finset.prod_insert,
        Finset.prod_singleton, mul_assoc]
      · simpa using hcb.symm
      · simp [hab, hac]
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [Set.indicator, hw p hp]
  have hpt : ∀ w, hB p0 w ≤ U w + U (Function.update w pb (w pb - w pa * w pc)) := by
    intro w
    by_cases hw : w ∈ {w : Low 4 → ℂ | ∀ p : Low 4, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
    · have hw' : ∀ p, p ∉ S → ‖w p‖ ≤ 1 := fun p hp => by
        have h1 : p ≠ pa := fun h => hp (by simp [hS, h])
        have h2 : p ≠ pb := fun h => hp (by simp [hS, h])
        have h3 : p ≠ pc := fun h => hp (by simp [hS, h])
        obtain ⟨k1, k2⟩ := hmix p h1 h2 h3
        exact hw p k1 k2
      have hw'' : ∀ p, p ∉ S → ‖Function.update w pb (w pb - w pa * w pc) p‖ ≤ 1 := fun p hp => by
        have : p ≠ pb := fun h => hp (by simp [hS, h])
        rw [Function.update_of_ne this]; exact hw' p hp
      rw [hUeq w hw', hUeq _ hw'']
      simp only [Function.update_self, Function.update_of_ne hab, Function.update_of_ne hcb]
      have n1 := pw_nonneg (w pa)
      have n2 := pw_nonneg (w pb)
      have n3 := pw_nonneg (w pc)
      have n4 := pw_nonneg (w pb - w pa * w pc)
      unfold hB
      rw [Set.indicator_of_mem hw, ← ENNReal.ofReal_mul n1, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul n1, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [hg w]
      have key := GlobalTheory.T.flagGram_density_inequality_complex (w pa) (w pb) (w pc)
      have e : pw (w pb - w pa * w pc) = (1 + ‖w pa * w pc - w pb‖ ^ 2) ^ (-(4 / 3 : ℝ)) := by
        simp only [pw, norm_sub_rev (w pb)]
      rw [e]
      simp only [pw]
      calc _ ≤ _ := key
        _ = _ := by ring
    · unfold hB; rw [Set.indicator_of_notMem hw]; exact zero_le'
  have hgm : Measurable fun w : Low 4 → ℂ => w pa * w pc :=
    (measurable_pi_apply pa).mul (measurable_pi_apply pc)
  have hgi : ∀ w v : Low 4 → ℂ, (∀ j, j ≠ pb → w j = v j) → w pa * w pc = v pa * v pc := by
    intro w v h; rw [h pa hab, h pc hcb]
  calc ∫⁻ w, hB p0 w ≤ ∫⁻ w, (U w + U (Function.update w pb (w pb - w pa * w pc))) :=
        lintegral_mono hpt
    _ = (∫⁻ w, U w) + ∫⁻ w, U (Function.update w pb (w pb - w pa * w pc)) :=
        lintegral_add_left hU _
    _ = (∫⁻ w, U w) + ∫⁻ w, U w := by
        rw [GlobalTheory.T.lintegral_update_sub_shear' pb (fun w => w pa * w pc) hgm hgi U hU]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hUfin, hUfin⟩

theorem lintegral_hB_four_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 3) → ∫⁻ w : Low 4 → ℂ, hB p0 w < ⊤ := by
  rintro p0 (rfl | rfl)
  · exact lintegral_hB_lt_top_of_pos 1 ⟨(2, 1), by decide⟩ ⟨(3, 1), by decide⟩ ⟨(3, 2), by decide⟩
      (by decide) (by decide) (by decide) (fun w => gB_eq_entries 1 _ _ _ w rfl rfl rfl) (by decide)
  · exact lintegral_hB_lt_top_of_pos 3 ⟨(1, 0), by decide⟩ ⟨(2, 0), by decide⟩ ⟨(2, 1), by decide⟩
      (by decide) (by decide) (by decide) (fun w => gB_eq_entries 3 _ _ _ w rfl rfl rfl) (by decide)
end
end GlobalTheory.IntBall.Fin4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockRankThreeLtTop
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.Fin3

theorem norm_one_add_conj_mul (z : ℂ) : ‖1 + (starRingEnd ℂ) z * z‖ = 1 + ‖z‖ ^ 2 := by
  rw [Complex.conj_mul', show (1 : ℂ) + (‖z‖ : ℂ) ^ 2 = ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_of_nonneg (by positivity)]

theorem gB_one (w : Low 3 → ℂ) : gB 1 w = (1 + ‖w ⟨(2, 1), by decide⟩‖ ^ 2) ^ (-2 : ℤ) := by
  simp [gB, Fin.prod_univ_two, colGram, lminor, Matrix.det_fin_one, Matrix.mul_apply, Fin.sum_univ_two, blkW, lowMat]
  rw [norm_one_add_conj_mul]

theorem gB_two (w : Low 3 → ℂ) : gB 2 w = (1 + ‖w ⟨(1, 0), by decide⟩‖ ^ 2) ^ (-2 : ℤ) := by
  simp [gB, Fin.prod_univ_two, colGram, lminor, Matrix.det_fin_one, Matrix.mul_apply, Fin.sum_univ_two, blkW, lowMat]
  rw [norm_one_add_conj_mul]

noncomputable def dom (x : ℂ) : ℝ≥0∞ :=
  (Metric.closedBall (0 : ℂ) 1).indicator 1 x + ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (-(4 : ℝ) / 2))

theorem measurable_dom : Measurable dom := by
  unfold dom
  refine Measurable.add ((measurable_const).indicator Metric.isClosed_closedBall.measurableSet) ?_
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

theorem lintegral_dom_lt_top : ∫⁻ x, dom x < ⊤ := by
  unfold dom
  rw [lintegral_add_left (f := (Metric.closedBall (0 : ℂ) 1).indicator (1 : ℂ → ℝ≥0∞))
    (measurable_one.indicator Metric.isClosed_closedBall.measurableSet)]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · rw [lintegral_indicator_one Metric.isClosed_closedBall.measurableSet]
    exact measure_closedBall_lt_top
  · exact (integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
      (by rw [Complex.finrank_real_complex]; norm_num)).lintegral_lt_top

theorem le_prod_dom (w : Low 3 → ℂ) (e : Low 3) (hw : ∀ p, p ≠ e → ‖w p‖ ≤ 1) :
    ENNReal.ofReal ((1 + ‖w e‖ ^ 2) ^ (-2 : ℤ)) ≤ ∏ p, dom (w p) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
  calc ENNReal.ofReal ((1 + ‖w e‖ ^ 2) ^ (-2 : ℤ)) = ENNReal.ofReal ((1 + ‖w e‖ ^ 2) ^ (-2 : ℤ)) * 1 :=
        (mul_one _).symm
    _ ≤ dom (w e) * ∏ p ∈ Finset.univ.erase e, dom (w p) := by
      refine mul_le_mul' ?_ ?_
      · unfold dom
        refine le_trans (le_of_eq ?_) le_add_self
        congr 1
        rw [show (-(4 : ℝ) / 2) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      · refine Finset.one_le_prod' fun p hp => ?_
        unfold dom
        refine le_trans (le_of_eq ?_) le_self_add
        rw [Set.indicator_of_mem (by simpa using hw p (Finset.ne_of_mem_erase hp))]
        rfl

theorem hB_le (p0 : ℕ) (hp : p0 = 1 ∨ p0 = 2) (w : Low 3 → ℂ) : hB p0 w ≤ ∏ p, dom (w p) := by
  unfold hB
  by_cases hS : w ∈ {w : Low 3 → ℂ | ∀ p : Low 3, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
  · rw [Set.indicator_of_mem hS]
    rcases hp with rfl | rfl
    · rw [gB_one]
      refine le_prod_dom w _ fun p hpe => hS p ?_ ?_
      · revert hpe; revert p; decide
      · revert hpe; revert p; decide
    · rw [gB_two]
      refine le_prod_dom w _ fun p hpe => hS p ?_ ?_
      · revert hpe; revert p; decide
      · revert hpe; revert p; decide
  · rw [Set.indicator_of_notMem hS]
    exact bot_le

theorem lintegral_hB_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 2) → ∫⁻ w : Low 3 → ℂ, hB p0 w < ⊤ := by
  intro p0 hp
  refine lt_of_le_of_lt (lintegral_mono fun w => hB_le p0 hp w) ?_
  have h := GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (E := fun _ : Low 3 => ℂ)
    (μ := fun _ => (volume : Measure ℂ)) (f := fun _ => dom) (fun _ => measurable_dom.aemeasurable)
  rw [volume_pi, h]
  exact ENNReal.prod_lt_top fun _ _ => lintegral_dom_lt_top

end GlobalTheory.IntBall.Fin3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugacyClassClosed
section
open Polynomial
open scoped TensorProduct

namespace GlobalTheory.ClosedClass

section Alg

variable (S F B : Type) [Field S] [Algebra ℚ S] [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [Ring B]
  [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] [FiniteDimensional F B]

noncomputable abbrev cen : S ⊗[ℚ] F →ₐ[S] S ⊗[ℚ] B :=
  Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom ℚ F B)

theorem eq_zero_of_isNilpotent (n : ℕ) (x₀ : B) (hsep : (minpoly F x₀).Separable)
    (hdeg : (minpoly F x₀).natDegree = n) (c : Fin n → S ⊗[ℚ] F)
    (h : IsNilpotent (∑ j, cen S F B (c j) * ((1 : S) ⊗ₜ[ℚ] x₀) ^ (j : ℕ))) : c = 0 := by
  classical
  haveI hcz : CharZero S := charZero_of_injective_algebraMap (algebraMap ℚ S).injective
  obtain rfl : ‹Algebra ℚ S› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨ι, _, L, _, _, _, Φ, ψ, hΦ1, hΦ2⟩ := GlobalTheory.tensor_decomp_factorwise S F B
  have key : ∀ i (j : Fin n), ψ (c j) i = 0 := by
    intro i
    let K := L i
    let e : K ⊗[F] B := (1 : K) ⊗ₜ[F] x₀
    let hp : K[X] := ∑ j : Fin n, C (ψ (c j) i) * X ^ (j : ℕ)
    have hΦw : Φ (∑ j, cen S F B (c j) * ((1 : S) ⊗ₜ[ℚ] x₀) ^ (j : ℕ)) i = aeval e hp := by
      simp only [hp, map_sum, map_mul, map_pow, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, hΦ2, hΦ1,
        aeval_C, aeval_X, e]
      rfl
    obtain ⟨m, hm⟩ := h
    have hnil : aeval e (hp ^ (m + 1)) = 0 := by
      rw [map_pow, ← hΦw, pow_succ]
      have := congrArg (fun w => w i) (congrArg Φ hm)
      simp only [map_pow, map_zero, Pi.pow_apply, Pi.zero_apply] at this
      rw [this, zero_mul]
    have hmin : minpoly K e = (minpoly F x₀).map (algebraMap F K) := GlobalTheory.SkNoFactor.minpoly_one_tmul K x₀
    have hd1 : minpoly K e ∣ hp ^ (m + 1) := minpoly.dvd K e hnil
    rw [hmin] at hd1
    have hd2 : (minpoly F x₀).map (algebraMap F K) ∣ hp :=
      (hsep.map.squarefree.dvd_pow_iff_dvd (Nat.succ_ne_zero m)).1 hd1
    have hdeglt : hp.degree < ((minpoly F x₀).map (algebraMap F K)).degree := by
      have h1 : hp.degree < n := Polynomial.degree_sum_fin_lt _
      rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree (minpoly.ne_zero (IsIntegral.of_finite F x₀)), hdeg]
      exact h1
    have hz : hp = 0 := Polynomial.eq_zero_of_dvd_of_degree_lt hd2 hdeglt
    intro j
    have := congrArg (fun q : K[X] => q.coeff (j : ℕ)) hz
    simp only [hp, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single j] at this
    · simpa using this
    · intro b _ hb
      rw [if_neg]
      exact fun h' => hb (Fin.ext h'.symm)
    · simp
  funext j
  apply ψ.injective
  funext i
  simp [key i j]

end Alg

end GlobalTheory.ClosedClass

namespace GlobalTheory.ClosedClass

section Conj

variable (S F B : Type) [Field S] [Algebra ℚ S] [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [Ring B]
  [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] [FiniteDimensional F B]

noncomputable abbrev trL : S ⊗[ℚ] B →ₗ[S] S :=
  (LinearMap.trace S (S ⊗[ℚ] B)).comp (Algebra.lmul S (S ⊗[ℚ] B)).toLinearMap

theorem trL_conj (g : (S ⊗[ℚ] B)ˣ) (u : S ⊗[ℚ] B) :
    trL S B ((g : S ⊗[ℚ] B) * u * ((g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B)) = trL S B u := by
  simp only [trL, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, map_mul]
  rw [LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

theorem cen_comm (z : S ⊗[ℚ] F) (y : S ⊗[ℚ] B) : Commute (cen S F B z) y := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s f =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s' b =>
      simp only [cen, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
      show (s ⊗ₜ[ℚ] algebraMap F B f) * (s' ⊗ₜ[ℚ] b) = (s' ⊗ₜ[ℚ] b) * (s ⊗ₜ[ℚ] algebraMap F B f)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm s s',
        Algebra.commutes]
    | add a b ha hb => exact Commute.add_right ha hb
  | add a b ha hb => rw [map_add]; exact Commute.add_left ha hb

theorem exists_conj_of_traces [Algebra.IsCentral F B] [IsSimpleRing B] (n : ℕ) (hn : Module.finrank F B = n ^ 2)
    (x₀ : B) (hsep : (minpoly F x₀).Separable) (hdeg : (minpoly F x₀).natDegree = n) (y : S ⊗[ℚ] B)
    (hP : ∑ i ∈ Finset.range (n + 1), ((1 : S) ⊗ₜ[ℚ] algebraMap F B ((minpoly F x₀).coeff i)) * y ^ i = 0)
    (hT : ∀ (z : S ⊗[ℚ] F) (k : ℕ), trL S B (cen S F B z * y ^ k) =
      trL S B (cen S F B z * ((1 : S) ⊗ₜ[ℚ] x₀) ^ k)) :
    ∃ g : (S ⊗[ℚ] B)ˣ, (g : S ⊗[ℚ] B) * ((1 : S) ⊗ₜ[ℚ] x₀) = y * g := by
  classical
  haveI hcz : CharZero S := charZero_of_injective_algebraMap (algebraMap ℚ S).injective
  obtain rfl : ‹Algebra ℚ S› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  haveI : Module.Finite ℚ B := Module.Finite.trans F B
  refine GlobalTheory.SkNoFactor.exists_unit_conj_baseChange S F B n hn x₀ y hsep hdeg hP ?_
  intro c hc
  set e₀ : S ⊗[ℚ] B := (1 : S) ⊗ₜ[ℚ] x₀ with he₀
  let ev : S ⊗[ℚ] B → (S ⊗[ℚ] F)[X] →+* S ⊗[ℚ] B := fun u =>
    Polynomial.eval₂RingHom' (cen S F B).toRingHom u (fun a => cen_comm S F B a u)
  have hev : ∀ u (H : (S ⊗[ℚ] F)[X]), ev u H = ∑ k ∈ Finset.range (H.natDegree + 1), cen S F B (H.coeff k) * u ^ k := by
    intro u H
    show Polynomial.eval₂ _ u H = _
    rw [Polynomial.eval₂_eq_sum_range]
    rfl
  have htr : ∀ H : (S ⊗[ℚ] F)[X], trL S B (ev y H) = trL S B (ev e₀ H) := by
    intro H
    rw [hev, hev, map_sum, map_sum]
    exact Finset.sum_congr rfl fun k _ => hT _ k
  let R : (S ⊗[ℚ] F)[X] := ∑ j : Fin n, C (c j) * X ^ (j : ℕ)
  have hevR : ∀ u, ev u R = ∑ j : Fin n, cen S F B (c j) * u ^ (j : ℕ) := by
    intro u
    simp only [R, map_sum, map_mul, map_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    show Polynomial.eval₂ _ u (C (c j)) * Polynomial.eval₂ _ u X ^ (j : ℕ) = _
    rw [Polynomial.eval₂_C, Polynomial.eval₂_X]
    rfl
  have hyR : ev y R = 0 := by rw [hevR]; exact hc
  set w := ev e₀ R with hw
  have hpow : ∀ k, 1 ≤ k → LinearMap.trace S (S ⊗[ℚ] B) ((Algebra.lmul S (S ⊗[ℚ] B) w) ^ k) = 0 := by
    intro k hk
    rw [← map_pow, hw, ← map_pow]
    have := htr (R ^ k)
    rw [map_pow, hyR, zero_pow (by omega), map_zero] at this
    exact this.symm
  obtain ⟨m, hm⟩ := GlobalTheory.UnipNormalTrace.isNilpotent_of_trace_pow_eq_zero _ hpow
  have hwn : IsNilpotent w := by
    refine ⟨m, ?_⟩
    have := congrArg (fun f : Module.End S (S ⊗[ℚ] B) => f 1) hm
    rw [← map_pow] at this
    simpa using this
  rw [hw, hevR] at hwn
  exact eq_zero_of_isNilpotent S F B n x₀ hsep hdeg c hwn

end Conj

end GlobalTheory.ClosedClass

namespace GlobalTheory.ClosedClass

section Top

variable (S F B : Type) [Field S] [Algebra ℚ S] [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [Ring B]
  [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] [FiniteDimensional F B]

theorem conj_val_pow (g e : (S ⊗[ℚ] B)ˣ) (i : ℕ) :
    (((g * e * g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B)) ^ i =
      (g : S ⊗[ℚ] B) * (e : S ⊗[ℚ] B) ^ i * ((g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) := by
  rw [← Units.val_pow_eq_pow_val, conj_pow]
  simp [Units.val_pow_eq_pow_val]

theorem cen_mul_conj (z : S ⊗[ℚ] F) (g : (S ⊗[ℚ] B)ˣ) (u : S ⊗[ℚ] B) :
    cen S F B z * ((g : S ⊗[ℚ] B) * u * ((g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B)) =
      (g : S ⊗[ℚ] B) * (cen S F B z * u) * ((g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) := by
  rw [← mul_assoc, ← mul_assoc, (cen_comm S F B z g).eq, mul_assoc (g : S ⊗[ℚ] B)]

theorem one_tmul_eq_cen (f : F) : (1 : S) ⊗ₜ[ℚ] algebraMap F B f = cen S F B ((1 : S) ⊗ₜ[ℚ] f) := by
  simp [cen]

theorem isClosed_conjClass [TopologicalSpace S] [IsTopologicalRing S] [T2Space S] [Algebra.IsCentral F B]
    [IsSimpleRing B] (n : ℕ) (hn : Module.finrank F B = n ^ 2) (x₀ : B) (hsep : (minpoly F x₀).Separable)
    (hdeg : (minpoly F x₀).natDegree = n) (e : (S ⊗[ℚ] B)ˣ) (he : (e : S ⊗[ℚ] B) = (1 : S) ⊗ₜ[ℚ] x₀) :
    letI : TopologicalSpace (S ⊗[ℚ] B) := moduleTopology S (S ⊗[ℚ] B)
    IsClosed {y : (S ⊗[ℚ] B)ˣ | ∃ g : (S ⊗[ℚ] B)ˣ, y = g * e * g⁻¹} := by
  classical
  letI : TopologicalSpace (S ⊗[ℚ] B) := moduleTopology S (S ⊗[ℚ] B)
  haveI : IsModuleTopology S (S ⊗[ℚ] B) := ⟨rfl⟩
  haveI : Module.Finite ℚ B := Module.Finite.trans F B
  haveI : IsTopologicalRing (S ⊗[ℚ] B) := IsModuleTopology.isTopologicalRing S (S ⊗[ℚ] B)
  let Pv : S ⊗[ℚ] B → S ⊗[ℚ] B := fun y =>
    ∑ i ∈ Finset.range (n + 1), ((1 : S) ⊗ₜ[ℚ] algebraMap F B ((minpoly F x₀).coeff i)) * y ^ i
  have hPe : Pv (e : S ⊗[ℚ] B) = 0 := by
    have h0 : Polynomial.aeval x₀ (minpoly F x₀) = 0 := minpoly.aeval F x₀
    rw [Polynomial.aeval_eq_sum_range, hdeg] at h0
    have h1 := congrArg (fun b : B => (1 : S) ⊗ₜ[ℚ] b) h0
    simp only [TensorProduct.tmul_zero, TensorProduct.tmul_sum] at h1
    rw [← h1]
    simp only [Pv, he]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  let b := Module.finBasis S (S ⊗[ℚ] B)
  have hset : {y : (S ⊗[ℚ] B)ˣ | ∃ g : (S ⊗[ℚ] B)ˣ, y = g * e * g⁻¹} =
      (⋂ i, {y : (S ⊗[ℚ] B)ˣ | b.coord i (Pv (y : S ⊗[ℚ] B)) = 0}) ∩
      ⋂ (z : S ⊗[ℚ] F) (k : ℕ), {y : (S ⊗[ℚ] B)ˣ | trL S B (cen S F B z * (y : S ⊗[ℚ] B) ^ k) =
        trL S B (cen S F B z * (e : S ⊗[ℚ] B) ^ k)} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨g, rfl⟩
      have hPy : Pv ((g * e * g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) = 0 := by
        have : Pv ((g * e * g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) =
            (g : S ⊗[ℚ] B) * Pv (e : S ⊗[ℚ] B) * ((g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) := by
          simp only [Pv, conj_val_pow, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [one_tmul_eq_cen, cen_mul_conj]
        rw [this, hPe, mul_zero, zero_mul]
      refine ⟨fun i => by rw [hPy, map_zero], fun z k => ?_⟩
      rw [conj_val_pow, cen_mul_conj, trL_conj]
    · rintro ⟨hP, hT⟩
      have hP' : Pv (y : S ⊗[ℚ] B) = 0 := by
        apply b.forall_coord_eq_zero_iff.1
        exact hP
      rw [he] at hT
      obtain ⟨g, hg⟩ := exists_conj_of_traces S F B n hn x₀ hsep hdeg (y : S ⊗[ℚ] B) hP' hT
      refine ⟨g, Units.ext ?_⟩
      rw [Units.val_mul, Units.val_mul, he, hg, mul_assoc, Units.mul_inv, mul_one]
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun i => ?_) (isClosed_iInter fun z => isClosed_iInter fun k => ?_)
  · have hc : Continuous fun y : (S ⊗[ℚ] B)ˣ => b.coord i (Pv (y : S ⊗[ℚ] B)) := by
      refine (IsModuleTopology.continuous_of_linearMap (b.coord i)).comp ?_
      exact continuous_finset_sum _ fun j _ => continuous_const.mul (Units.continuous_val.pow j)
    exact isClosed_eq hc continuous_const
  · have hc : Continuous fun y : (S ⊗[ℚ] B)ˣ => trL S B (cen S F B z * (y : S ⊗[ℚ] B) ^ k) :=
      (IsModuleTopology.continuous_of_linearMap (trL S B)).comp
        (continuous_const.mul (Units.continuous_val.pow k))
    exact isClosed_eq hc continuous_const

end Top

end GlobalTheory.ClosedClass

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAf

end GlobalTheory.OrbFinAf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingImageStalkMap
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

open CategoryTheory AlgebraicGeometry TopologicalSpace in

theorem _root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm : ∀ {X Y : Scheme.{0}} [IsIntegral X] (π : X ⟶ Y) (y : X) (h : π (genericPoint X) ⤳ π y), Function.Surjective (π.stalkMap y).hom → ∀ c : X.functionField, c ∈ _root_.GlobalTheory.LogDR.locRing y ↔ ∃ z ∈ _root_.GlobalTheory.DI.stalkIm h, (π.stalkMap (genericPoint X)).hom z = c := by
  intro X Y _ π y h hsurj c
  have hcomm : ∀ b : Y.presheaf.stalk (π y),
      (π.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes h).hom b) =
        algebraMap (X.presheaf.stalk y) X.functionField ((π.stalkMap y).hom b) := by
    intro b
    exact Scheme.Hom.stalkSpecializes_stalkMap_apply π _ _
      ((genericPoint_spec X).specializes (Set.mem_univ y)) b
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := hsurj a
    exact ⟨(Y.presheaf.stalkSpecializes h).hom b, ⟨b, rfl⟩, hcomm b⟩
  · rintro ⟨z, ⟨b, rfl⟩, rfl⟩
    exact ⟨(π.stalkMap y).hom b, (hcomm b).symm⟩

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDifferentialMulLogCoordinateWedgeStatement
section
open GlobalTheory GlobalTheory.LogDR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logDifferential_mul_logCoordinateWedge : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ) (i : Fin n) (I : Finset (Fin n)), (i ∈ I → ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = 0) ∧ (i ∉ I → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = ε • logWedge x (insert i I)) := by
  first | exact @GlobalTheory.LogDR.dlog_mul_logWedge | exact GlobalTheory.LogDR.dlog_mul_logWedge | (intros; apply GlobalTheory.LogDR.dlog_mul_logWedge <;> assumption)
end

