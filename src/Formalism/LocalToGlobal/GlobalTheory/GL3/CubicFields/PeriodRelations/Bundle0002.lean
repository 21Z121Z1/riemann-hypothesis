import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle0001
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.BrLamConjEq
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive LinkPer KroneckerLimit DedekindFactor)
open Formalism.MainNotions.TaylorLogMetric (lamConj lamOf embT meanLogOm DataIn tor0 IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice per22 logOmVal)

theorem br_lamConj_eq (hU : UniqInv) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (Λ Λ₀ : AddSubgroup ℂ) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M) (h1 : discr Λ = 1)
    (h0 : discr Λ₀ ≠ 0) (hjM : jL Λ ∈ M) (hj : ρ ⟨jL Λ, hjM⟩ = jL Λ₀) :
    ∃ c : ℂ, c ≠ 0 ∧ lamConj M ρ Λ = c • Λ₀ ∧ discr (c • Λ₀) = 1 := by
  set a : ℂ := ρ ⟨g2 Λ, h2⟩ with ha
  set b : ℂ := ρ ⟨g3 Λ, h3⟩ with hb
  have hdM : (⟨g2 Λ, h2⟩ : M) ^ 3 - 27 * (⟨g3 Λ, h3⟩ : M) ^ 2 = 1 := by
    apply M.val.injective
    rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one]
    exact h1
  have hab1 : a ^ 3 - 27 * b ^ 2 = 1 := by
    rw [ha, hb, ← map_pow, ← map_pow, ← map_ofNat ρ 27, ← map_mul, ← map_sub, hdM, map_one]
  have hjL : (⟨jL Λ, hjM⟩ : M) = 1728 * (⟨g2 Λ, h2⟩ : M) ^ 3 := by
    apply M.val.injective
    rw [map_mul, map_pow, map_ofNat]
    show jL Λ = 1728 * g2 Λ ^ 3
    rw [br_jL_eq, h1, div_one]
  have hj' : 1728 * a ^ 3 / (a ^ 3 - 27 * b ^ 2) = jL Λ₀ := by
    rw [hab1, div_one, ← hj, hjL, map_mul, map_pow, map_ofNat]
  obtain ⟨c, hc0, hc2, hc3⟩ := br_exists_scale Λ₀ h0 a b (by rw [hab1]; exact one_ne_zero) hj'
  have hd1 : discr (c • Λ₀) = 1 := by
    show g2 (c • Λ₀) ^ 3 - 27 * g3 (c • Λ₀) ^ 2 = 1
    rw [hc2, hc3, hab1]
  have hl2 : Formalism.MainNotions.TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.g2 Λ) = ⟨g2 Λ, h2⟩ := dif_pos h2
  have hl3 : Formalism.MainNotions.TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.g3 Λ) = ⟨g3 Λ, h3⟩ := dif_pos h3
  have hex : ∃ Λ' : AddSubgroup ℂ, Formalism.MainNotions.TaylorLogMetric.g2 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.g2 Λ)) ∧
      Formalism.MainNotions.TaylorLogMetric.g3 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.g3 Λ)) :=
    ⟨c • Λ₀, by rw [hl2]; exact hc2, by rw [hl3]; exact hc3⟩
  have hspec := Classical.epsilon_spec hex
  have hs2 : Formalism.MainNotions.TaylorLogMetric.g2 (lamConj M ρ Λ) = a := by
    exact hspec.1.trans (by rw [hl2])
  have hs3 : Formalism.MainNotions.TaylorLogMetric.g3 (lamConj M ρ Λ) = b := by
    exact hspec.2.trans (by rw [hl3])
  refine ⟨c, hc0, ?_, hd1⟩
  symm
  apply hU
  · show discr (c • Λ₀) ≠ 0
    rw [hd1]; exact one_ne_zero
  · rw [hs2]; exact hc2
  · rw [hs3]; exact hc3

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Period
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive LinkPer KroneckerLimit DedekindFactor)
open Formalism.MainNotions.TaylorLogMetric (lamConj lamOf embT meanLogOm DataIn tor0 IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice per22 logOmVal)

theorem br_ellT_eq (D : D7) (M : IntermediateField ℚ ℂ) [NumberField M] (τ : D.what₂.Tau) :
    Formalism.MainNotions.TaylorLogMetric.ellT D M τ = lineR M (embT D) D.host.AA0 τ := rfl

theorem br_brN_eq (D : D7) : brN D = ((FractionalIdeal.absNorm (D.host.AA0 *
    ((differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : ℚ) : ℝ) := rfl

theorem br_exists_ellT (D : D7) (M : IntermediateField ℚ ℂ) [NumberField M]
    (hemb : ∀ τ x, embT D τ x ∈ M) (τ : D.what₂.Tau) :
    ∃ s : M, s ≠ 0 ∧ s ∈ Formalism.MainNotions.TaylorLogMetric.ellT D M τ := by
  rw [br_ellT_eq, lineR_eq D.host.K D.host.E (brPhi D) M D.what₂.Tau (embT D) (br_embT_injective D)
    (br_embT_res D) (br_card_tau D) hemb]
  have hJ : D.host.AA0 * ((differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    mul_ne_zero (leading_constant_ne_zero D) (coeIdeal_different_ne_zero _ _)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hJ)
  refine ⟨liftM M (embT D τ a), ?_, Submodule.subset_span ⟨a, ha, rfl⟩⟩
  have hm := hemb τ a
  unfold liftM
  rw [dif_pos hm]
  intro h
  have : embT D τ a = 0 := congrArg Subtype.val h
  exact ha0 ((map_eq_zero (embT D τ)).mp this)

theorem br_meanLogOm_eq (D : D7) (Λ : AddSubgroup ℂ) (M : IntermediateField ℚ ℂ) [NumberField M]
    (hemb : ∀ τ x, embT D τ x ∈ M) (τ : D.what₂.Tau)
    (hpos : ∀ ρ : M →ₐ[ℚ] ℂ, 0 < area (lamConj M ρ Λ)) :
    meanLogOm D Λ M τ =
      -(2 / (Module.finrank ℚ D.host.E : ℝ)) * Real.log (brN D) +
        (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ Λ) / Real.pi)) /
          (Module.finrank ℚ M : ℝ) := by
  have hex := br_exists_ellT D M hemb τ
  unfold meanLogOm
  dsimp only
  set s : M := Classical.epsilon (fun s : M => s ≠ 0 ∧ s ∈ Formalism.MainNotions.TaylorLogMetric.ellT D M τ) with hsdef
  have hs : s ≠ 0 ∧ s ∈ Formalism.MainNotions.TaylorLogMetric.ellT D M τ := Classical.epsilon_spec hex
  rw [br_ellT_eq] at hs ⊢
  have hidx := index_lineR D.host.K D.host.E (brPhi D) M D.what₂.Tau (embT D) (br_embT_injective D)
    (br_embT_res D) (br_card_tau D) hemb D.host.AA0 (leading_constant_ne_zero D) τ s hs.1 hs.2
  rw [← br_brN_eq] at hidx
  set x : ℝ := ((((Submodule.span (𝓞 M) {s}).toAddSubgroup.addSubgroupOf
        (lineR M (embT D) D.host.AA0 τ).toAddSubgroup).index : ℕ) : ℝ) with hxdef
  set e : ℕ := Module.finrank ℚ D.host.E with he
  set m : ℕ := Module.finrank ℚ M with hm
  set ns : ℝ := |((Algebra.norm ℚ s : ℚ) : ℝ)| with hns
  have hns0 : ns ≠ 0 := by
    rw [hns, abs_ne_zero, Rat.cast_ne_zero]
    exact (Algebra.norm_ne_zero_iff).mpr hs.1
  have hrhs : ns ^ e ≠ 0 := pow_ne_zero _ hns0
  have hl : x ^ e * brN D ^ m ≠ 0 := hidx ▸ hrhs
  have hx0 : x ^ e ≠ 0 := left_ne_zero_of_mul hl
  have hN0 : brN D ^ m ≠ 0 := right_ne_zero_of_mul hl
  have hlog : (e : ℝ) * Real.log x + (m : ℝ) * Real.log (brN D) = (e : ℝ) * Real.log ns := by
    have := congrArg Real.log hidx
    rw [Real.log_mul hx0 hN0, Real.log_pow, Real.log_pow, Real.log_pow] at this
    exact this
  have he0 : (e : ℝ) ≠ 0 := by
    rw [he]; exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ D.host.E).ne'
  have hm0 : (m : ℝ) ≠ 0 := by
    rw [hm]; exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ M).ne'
  have hterm : ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.logMet M Λ ρ s =
      Real.log Real.pi + Real.log (‖ρ s‖ ^ 2) - Real.log (area (lamConj M ρ Λ)) := by
    intro ρ
    unfold Formalism.MainNotions.TaylorLogMetric.logMet
    rw [br_area_eq]
    have hρ : ‖ρ s‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ((map_ne_zero ρ).mpr hs.1))
    rw [Real.log_div (mul_ne_zero Real.pi_ne_zero hρ) (hpos ρ).ne', Real.log_mul Real.pi_ne_zero hρ]
  have hsum : ∑ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.logMet M Λ ρ s =
      (m : ℝ) * Real.log Real.pi + 2 * Real.log ns -
        ∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ Λ)) := by
    rw [Finset.sum_congr rfl (fun ρ _ => hterm ρ), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      br_sum_log_norm_sq M s hs.1, Finset.sum_const, Finset.card_univ, AlgHom.card, nsmul_eq_mul]
  have hsum2 : ∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ Λ) / Real.pi) =
      ∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ Λ)) - (m : ℝ) * Real.log Real.pi := by
    rw [Finset.sum_congr rfl (fun ρ _ => Real.log_div (hpos ρ).ne' Real.pi_ne_zero),
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, AlgHom.card, nsmul_eq_mul]
  rw [hsum, hsum2]
  field_simp
  linear_combination 2 * hlog

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
end

