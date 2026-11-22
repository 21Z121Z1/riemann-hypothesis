import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PChartIndep
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

theorem ChartIndep.proof (hA : AmbChart.Statement) : ChartIndep.Statement := fun _ i =>
  (chart_eq hA 0).trans (chart_eq hA i).symm

end FSInv

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PParseval
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ComplexConjugate
open MvPolynomial

noncomputable section

namespace FSInv

open CP

theorem Parseval.proof (hO : Orth.Statement) (hS : Sesq.Statement) (hI : InnerSelf.Statement) :
    Parseval.Statement := by
  intro N n P hP
  have hdeg : ∀ a ∈ P.support, a.degree = n := fun a ha =>
    (IsHomogeneous.degree_eq_sum_deg_support ((mem_homogeneousSubmodule _ _).mp hP) ha).symm
  have hmem : ∀ a ∈ P.support, monomial a (1 : ℂ) ∈ H0 N n := fun a ha =>
    (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial _ (hdeg a ha))
  have hsum : ∀ s ⊆ P.support, (∑ b ∈ s, P.coeff b • monomial b (1 : ℂ)) ∈ H0 N n := fun s hs =>
    Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _ (hmem b (hs hb))

  have hright : ∀ R ∈ H0 N n, ∀ s ⊆ P.support,
      l2Inner (N := N) n R (∑ b ∈ s, P.coeff b • monomial b (1 : ℂ)) =
        ∑ b ∈ s, P.coeff b * l2Inner n R (monomial b 1) := by
    intro R hR s
    induction s using Finset.induction_on with
    | empty => intro _; simp [l2Inner, fsPair]
    | insert b s hb ih =>
      intro hs
      have hs' : s ⊆ P.support := (Finset.subset_insert _ _).trans hs
      rw [Finset.sum_insert hb, Finset.sum_insert hb, add_comm,
        (hS N n _ _ R (hsum s hs') (hmem b (hs (Finset.mem_insert_self _ _))) hR _).2.1,
        ih hs', add_comm]

  have hleft : ∀ R ∈ H0 N n, ∀ s ⊆ P.support,
      l2Inner (N := N) n (∑ b ∈ s, P.coeff b • monomial b (1 : ℂ)) R =
        ∑ b ∈ s, conj (P.coeff b) * l2Inner n (monomial b 1) R := by
    intro R hR s
    induction s using Finset.induction_on with
    | empty => intro _; simp [l2Inner, fsPair]
    | insert b s hb ih =>
      intro hs
      have hs' : s ⊆ P.support := (Finset.subset_insert _ _).trans hs
      rw [Finset.sum_insert hb, Finset.sum_insert hb, add_comm,
        (hS N n _ _ R (hsum s hs') (hmem b (hs (Finset.mem_insert_self _ _))) hR _).1,
        ih hs', add_comm]
  have hPs : P = ∑ a ∈ P.support, P.coeff a • monomial a (1 : ℂ) := by
    conv_lhs => rw [P.as_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_monomial, smul_eq_mul, mul_one]
  have hdiag : ∀ a ∈ P.support, l2Inner (N := N) n (monomial a (1 : ℂ)) (monomial a 1) =
      (((∏ i, ((a i).factorial : ℝ)) * N.factorial / (n + N).factorial : ℝ) : ℂ) := by
    intro a ha
    rw [hI, ← fubiniStudy_l2Norm_sq_eq, ← hdeg a ha, fubiniStudy_l2Norm_monomial_sq]
  have key : l2Inner (N := N) n P P = ∑ a ∈ P.support, conj (P.coeff a) * P.coeff a *
      (((∏ i, ((a i).factorial : ℝ)) * N.factorial / (n + N).factorial : ℝ) : ℂ) := by
    conv_lhs => rw [hPs]
    rw [hleft _ (hsum _ subset_rfl) _ subset_rfl]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hright _ (hmem a ha) _ subset_rfl, Finset.mul_sum,
      Finset.sum_eq_single a, hdiag a ha, mul_assoc]
    · intro b hb hba
      have h0 : l2Inner (N := N) n (monomial a (1 : ℂ)) (monomial b 1) = 0 := by
        rw [← hdeg a ha]
        exact hO N a b (Ne.symm hba) (by rw [hdeg a ha, hdeg b hb])
      rw [h0, mul_zero, mul_zero]
    · intro ha'; exact absurd ha ha'
  rw [fubiniStudy_l2Norm_sq_eq]
  apply Complex.ofReal_injective
  rw [← hI N n P, key]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.conj_mul']

end FSInv

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.PRadial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FSInv

open MeasureTheory

theorem Radial.proof : Radial.Statement := by
  intro N s hs
  have hc : 0 < s⁻¹ := inv_pos.2 hs
  obtain ⟨hI, hV⟩ := GroundTheory.Heights₂.Heights.integral_complex_norm_pow_div s⁻¹ hc 0 N
  have hpt : ∀ t : ℂ, ‖t‖ ^ (2 * N) * (1 / (1 + ‖t‖ ^ 2 * s) ^ (N + 2)) =
      (s⁻¹) ^ (N + 2) * (‖t‖ ^ (2 * N) / (s⁻¹ + ‖t‖ ^ 2) ^ (N + 2 + 0)) := by
    intro t
    have h1 : 1 + ‖t‖ ^ 2 * s = s * (s⁻¹ + ‖t‖ ^ 2) := by field_simp
    have h2 : 0 < s⁻¹ + ‖t‖ ^ 2 := by positivity
    rw [h1, mul_pow, add_zero, inv_pow]
    field_simp
  have hnn : 0 ≤ᵐ[volume] fun t : ℂ => (s⁻¹) ^ (N + 2) * (‖t‖ ^ (2 * N) / (s⁻¹ + ‖t‖ ^ 2) ^ (N + 2 + 0)) :=
    Filter.Eventually.of_forall fun t => by positivity
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal (hI.const_mul _) hnn, integral_const_mul, hV,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one, add_zero, zero_add, pow_one,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add]
  have hN : (N.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  rw [div_pow, one_pow, show s ^ (N + 2) = s * s ^ (N + 1) by ring]
  field_simp

end GroundTheory.Heights₂.Heights.FSInv
end

