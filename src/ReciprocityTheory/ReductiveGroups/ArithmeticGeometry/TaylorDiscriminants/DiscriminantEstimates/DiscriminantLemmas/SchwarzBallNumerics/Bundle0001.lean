import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0001

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.SchwarzBallNumerics.ArithmeticFourInequalityNum
section
namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

theorem arithmetic_four_inequality_num : ReciprocityTheory.ChartRestriction.G.TB.ScaledBoundInequality := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.ScaledBoundInequality
  intro P lNc D L G2 G1 hP hl hD hL hG2 hG1
  have hD0 : D ≠ 0 := by linarith
  have hcan : 2 * lNc / D * D = 2 * lNc := div_mul_cancel₀ _ hD0
  have hexp : (5 * P + 2 * lNc / D) * D * L = 5 * P * D * L + 2 * lNc * L := by
    calc (5 * P + 2 * lNc / D) * D * L = 5 * P * D * L + (2 * lNc / D * D) * L := by ring
      _ = 5 * P * D * L + 2 * lNc * L := by rw [hcan]
  rw [hexp]
  have h1 : P * G2 ≤ P * ((D + 4) * L) := mul_le_mul_of_nonneg_left hG2 hP
  have h2 : P * G1 ≤ P * (2 * L) := mul_le_mul_of_nonneg_left hG1 hP
  have h3 : 0 ≤ P * L := mul_nonneg hP (by linarith)
  have h4 : P * L ≤ P * D * L := by nlinarith [mul_nonneg h3 (sub_nonneg.mpr hD)]
  have h5 : lNc ≤ lNc * L := by nlinarith [mul_nonneg hl (sub_nonneg.mpr hL)]
  constructor <;> nlinarith

end PI.UnitaryGroupMassFormula.TBNum
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.SchwarzBallNumerics.EBasis
section
namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

theorem eBasis : ReciprocityTheory.ChartRestriction.G.TB.EBasisSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.EBasisSt
  intro E _ _ W _ _ _ _ _ ι _ v hv hcard
  classical
  haveI : FiniteDimensional ℚ W := Module.Finite.trans E W
  have hinj : Function.Injective v := hv.injective
  have hspanQ : Submodule.span ℚ (Set.range v) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hv, hcard, Module.finrank_mul_finrank]
  have hspanE : Submodule.span E (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℚ (Set.range v) := by rw [hspanQ]; trivial
    exact Submodule.span_le_restrictScalars ℚ E (Set.range v) hx
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent E (Set.range v)
  let s : Finset ι := Finset.univ.filter (fun i => v i ∈ b)
  have hrange : Set.range (fun i : s => v i) = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (Finset.mem_filter.mp i.2).2
    · intro hx
      obtain ⟨i, rfl⟩ := hbsub hx
      exact ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩, rfl⟩
  have hli : LinearIndependent E (fun i : s => v i) := by
    let f : s → b := fun i => ⟨v i, (Finset.mem_filter.mp i.2).2⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      exact hinj (congrArg Subtype.val hij)
    exact hbli.comp f hf
  have hspan : Submodule.span E (Set.range fun i : s => v i) = ⊤ := by
    rw [hrange, hbspan, hspanE]
  refine ⟨s, ?_, hli, hspan⟩
  have hfr := finrank_span_eq_card hli
  rw [hspan, finrank_top, Fintype.card_coe] at hfr
  exact hfr.symm

end PI.UnitaryGroupMassFormula.TBNum
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.SchwarzBallNumerics.NetForm
section
namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

theorem netHerm : ReciprocityTheory.ChartRestriction.G.TB.NetHermSt := by
  intro V _ _ ι _ ev
  have hF : ∀ F, ReciprocityTheory.ChartRestriction.G.TB.netForm ev F F
      = (((Fintype.card ι : ℝ)⁻¹ * ∑ y, Complex.normSq (ev y F) : ℝ) : ℂ) := by
    intro F
    simp only [ReciprocityTheory.ChartRestriction.G.TB.netForm, Complex.mul_conj]
    push_cast
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro F G
    simp only [ReciprocityTheory.ChartRestriction.G.TB.netForm, map_mul, map_sum, map_inv₀, map_natCast,
      Complex.conj_conj]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  · intro F
    rw [hF, Complex.ofReal_im, Complex.ofReal_re]
    exact ⟨rfl, mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun y _ => Complex.normSq_nonneg _)⟩
  · intro hinj F h0
    apply hinj F
    intro y
    rw [hF, Complex.ofReal_eq_zero] at h0
    have hne : (Fintype.card ι : ℝ) ≠ 0 := by
      have : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨y⟩
      exact_mod_cast this.ne'
    have hs : ∑ y, Complex.normSq (ev y F) = 0 := by
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd (inv_eq_zero.1 h) hne
      · exact h
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => Complex.normSq_nonneg (ev y F))).1 hs y
      (Finset.mem_univ y)
    exact Complex.normSq_eq_zero.1 this

end PI.UnitaryGroupMassFormula.TBNum
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.SchwarzBallNumerics.NetSup
section
namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

theorem netSup : ReciprocityTheory.ChartRestriction.G.TB.NetSupSt := by
  intro ι _ f S hf hS ⟨y0, hy0⟩
  have hn : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨y0⟩
  have key : Real.sqrt (Fintype.card ι) * Real.sqrt ((Fintype.card ι : ℝ)⁻¹ * ∑ y, f y ^ 2)
      = Real.sqrt (∑ y, f y ^ 2) := by
    rw [← Real.sqrt_mul hn.le, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  have h1 : f y0 ^ 2 ≤ ∑ y, f y ^ 2 :=
    Finset.single_le_sum (f := fun y => f y ^ 2) (fun y _ => sq_nonneg (f y)) (Finset.mem_univ y0)
  have h2 : f y0 ≤ Real.sqrt (∑ y, f y ^ 2) := by
    rw [← Real.sqrt_sq (hf y0)]
    exact Real.sqrt_le_sqrt h1
  calc S ≤ 4 * f y0 := by linarith
    _ ≤ 4 * Real.sqrt (∑ y, f y ^ 2) := by linarith
    _ = _ := by rw [mul_assoc, key]

end PI.UnitaryGroupMassFormula.TBNum
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.SchwarzBallNumerics.Schwarz
section
namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

theorem schwarzBall : ReciprocityTheory.ChartRestriction.G.TB.SchwarzBallSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.SchwarzBallSt
  intro E _ _ u ρ M hρ hu hM z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hzρ : ‖z‖ < ρ := mem_ball_zero_iff.mp hz
  have hmaps : Set.MapsTo (fun w : ℂ => w • z) (Metric.ball 0 (ρ / ‖z‖)) (Metric.ball (0 : E) ρ) := by
    intro w hw
    rw [mem_ball_zero_iff] at hw ⊢
    rw [norm_smul]
    rw [lt_div_iff₀ hzpos] at hw
    exact hw
  have hg : DifferentiableOn ℂ (fun w : ℂ => u (w • z)) (Metric.ball 0 (ρ / ‖z‖)) :=
    hu.comp (differentiable_id.smul_const z).differentiableOn hmaps
  have h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (ρ / ‖z‖) := by
    rw [mem_ball_zero_iff, norm_one, lt_div_iff₀ hzpos, one_mul]
    exact hzρ
  have hmap2 : Set.MapsTo (fun w : ℂ => u (w • z)) (Metric.ball 0 (ρ / ‖z‖))
      (Metric.closedBall (u ((0 : ℂ) • z)) M) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm, zero_smul]
    exact hM _ (hmaps hw)
  have hS := Complex.dist_le_div_mul_dist_of_mapsTo_ball hg hmap2 h1
  simp only [one_smul, zero_smul, dist_eq_norm, sub_zero, norm_one, mul_one] at hS
  rw [div_div_eq_mul_div] at hS
  exact hS

end PI.UnitaryGroupMassFormula.TBNum
end

