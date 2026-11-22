import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDiscriminantSquare.RelDiffTop

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDiscriminantSquare.AdjoinEqTopOfStarNe
section
open NumberField Polynomial

namespace PIW.CMDiscSq

theorem exists_of_star_eq {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) {y : E} (hy : star y = y) :
    ∃ a : F, algebraMap F E a = y := by
  have : y ∈ Set.range (algebraMap F E) := by rw [hR]; exact hy
  exact this

theorem adjoin_eq_top_of_star_ne {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) {x : E} (hx : star x ≠ x) :
    Algebra.adjoin F {x} = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hd : x - star x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hbd : (y - star y) / (x - star x) * (x - star x) = y - star y := div_mul_cancel₀ _ hd
  have hb : star ((y - star y) / (x - star x)) = (y - star y) / (x - star x) := by
    rw [star_div₀, star_sub, star_sub, star_star, star_star, ← neg_sub y, ← neg_sub x,
      neg_div_neg_eq]
  have ha : star (y - (y - star y) / (x - star x) * x) = y - (y - star y) / (x - star x) * x := by
    rw [star_sub, star_mul', hb]
    linear_combination hbd
  obtain ⟨b, hb'⟩ := exists_of_star_eq hR hb
  obtain ⟨a, ha'⟩ := exists_of_star_eq hR ha
  have hy : y = algebraMap F E a + algebraMap F E b * x := by rw [ha', hb']; ring
  rw [hy]
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ a)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ b) (Algebra.subset_adjoin rfl))

theorem minpoly_eq_of_star_ne {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    [FiniteDimensional F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) {x : E} (hx : star x ≠ x) :
    ∃ s n : F, algebraMap F E s = x + star x ∧ algebraMap F E n = x * star x ∧
      minpoly F x = X ^ 2 - C s * X + C n := by
  obtain ⟨s, hs⟩ := exists_of_star_eq hR (y := x + star x) (by rw [star_add, star_star, add_comm])
  obtain ⟨n, hn⟩ := exists_of_star_eq hR (y := x * star x) (by rw [star_mul', star_star, mul_comm])
  refine ⟨s, n, hs, hn, ?_⟩
  have hmon : (X ^ 2 - C s * X + C n : F[X]).Monic := by monicity!
  have hdeg : (X ^ 2 - C s * X + C n : F[X]).natDegree = 2 := by compute_degree!
  have hroot : aeval x (X ^ 2 - C s * X + C n : F[X]) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, hs, hn]
    ring
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have h2 : 2 ≤ (minpoly F x).natDegree := by
    rw [minpoly.two_le_natDegree_iff hint]
    rintro ⟨a, rfl⟩
    apply hx
    have : algebraMap F E a ∈ Set.range (algebraMap F E) := ⟨a, rfl⟩
    rw [hR] at this
    exact this
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon
    (minpoly.dvd F x hroot) (by rw [hdeg]; exact h2)).symm

end PIW.CMDiscSq
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDiscriminantSquare.Development
section
open NumberField

namespace PIW.CMDiscSq

theorem discSq_of (h1 : RelDiffTop) (h2 : RelDegTwo) : Formalism.L2.SG.MassRatio.DiscSq := by
  intro F E _ _ _ _ _ _ hFE
  have hN := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    F (𝓞 F) E (𝓞 E)
  rw [h1 F E hFE, Ideal.absNorm_top, one_mul, h2 F E hFE] at hN
  have hR : (((discr E).natAbs : ℕ) : ℝ) = (((discr F).natAbs : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hN
  unfold Formalism.L2.SG.MassRatio.dF
  simpa [Nat.cast_natAbs, Int.cast_abs] using hR

end PIW.CMDiscSq
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDiscriminantSquare.FinrankTwoOf
section
open NumberField Module

noncomputable section

namespace PIW.CMDiscSq

theorem exists_star_ne {E : Type} [Field E] [NumberField E] [StarRing E]
    (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) : ∃ x : E, star x ≠ x := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
  obtain ⟨θ, t, ht, hθ⟩ := hE.2.2 P hP
  refine ⟨algebraMap (𝓞 E) E θ, ?_⟩
  rw [← ht]
  intro h
  apply hθ
  have : t = θ := RingOfIntegers.coe_injective h
  rw [this, sub_self]
  exact P.zero_mem

theorem finrank_two_of {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
    (hR : Set.range (algebraMap F E) = {a : E | star a = a}) (x : E) (hx : star x ≠ x) :
    finrank F E = 2 := by
  have hmem : ∀ a : E, star a = a → ∃ c : F, algebraMap F E c = a := by
    intro a ha
    have : a ∈ Set.range (algebraMap F E) := by rw [hR]; exact ha
    exact this
  have hfix : ∀ c : F, star (algebraMap F E c) = algebraMap F E c := by
    intro c
    have : algebraMap F E c ∈ Set.range (algebraMap F E) := ⟨c, rfl⟩
    rw [hR] at this
    exact this
  have hd : x - star x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  let v : Fin 2 → E := ![1, x]
  have hli : LinearIndependent F v := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    by_cases ht : t = 0
    · subst ht
      simp only [map_zero, zero_mul, add_zero] at hst
      exact ⟨(FaithfulSMul.algebraMap_injective F E) (by rw [hst, map_zero]), rfl⟩
    · exfalso
      have htE : algebraMap F E t ≠ 0 := by
        intro h0
        apply ht
        exact (FaithfulSMul.algebraMap_injective F E) (by rw [h0, map_zero])
      have hxe : x = algebraMap F E (-s / t) := by
        rw [map_div₀, map_neg]
        field_simp
        linear_combination hst
      apply hx
      rw [hxe, hfix]
  have hsp : ⊤ ≤ Submodule.span F (Set.range v) := by
    intro y _
    have hb : star ((y - star y) / (x - star x)) = (y - star y) / (x - star x) := by
      rw [star_div₀, star_sub, star_sub, star_star, star_star]
      rw [← neg_sub y, ← neg_sub x, neg_div_neg_eq]
    obtain ⟨b, hb'⟩ := hmem _ hb
    have ha : star (y - algebraMap F E b * x) = y - algebraMap F E b * x := by
      rw [star_sub, star_mul', hfix, hb']
      field_simp
      ring
    obtain ⟨a, ha'⟩ := hmem _ ha
    have hy : y = a • v 0 + b • v 1 := by
      simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one]
      rw [ha']
      ring
    rw [hy]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have bas := Basis.mk hli hsp
  rw [finrank_eq_card_basis bas, Fintype.card_fin]

theorem relDegTwo : RelDegTwo := by
  intro F E _ _ _ _ _ _ hFE
  obtain ⟨x, hx⟩ := exists_star_ne hFE.1
  exact finrank_two_of hFE.2 x hx

end PIW.CMDiscSq
end
end

