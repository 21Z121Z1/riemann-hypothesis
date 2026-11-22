import Mathlib
import Formalism.PeriodIntegrals.Bundle0007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.OddDualWeylFactorization
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OpBound
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.Bundle0002
import Formalism.PeriodIntegrals.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSubstitutionIntegral.Bundle0002
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoincareSeriesMeasurability.FoldL2DoubleCoset
import Formalism.PeriodIntegrals.Bundle0008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.ClaimOfTwo
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Bundle0002
import Formalism.PeriodIntegrals.Bundle0021
import Formalism.PeriodIntegrals.Bundle0023
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFirstColumn.FirstColumnSplitBijective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EntrywiseSandwichCommute.Imports
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkipSuccessorIndex.SkipSucc2
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittLogarithm.Bundle0001

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OddDualWeyl
section
theorem oddDualWeyl {K : Type} [Field K] (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) :
    PI.OddDualWeyl.OddFact (K := K) O m lam :=
  PI.OddDualWeyl.odd_dual_weyl_factorization O m lam
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OpWords
section
theorem operator_words_bound : Formalism.MainNotions.TestSideCounting.OpBound :=
  PI.OpWords.opBound_of_vanish PI.OpWords.vanishingOnQuadric
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhGram
section
theorem phase_gram' : PI.FglGram.PhGram :=
  PI.UnitaryGroupMassFormula.PhGram.phGram_of_steps PI.UnitaryGroupMassFormula.PhGram.gram_bilinear_expansion PI.UnitaryGroupMassFormula.PhGram.gram_sum_first_variable
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PoincareSeriesMemLp
section
theorem fold_l2_bound_b (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesMemLp G μ :=
  PI.PoincareSeriesMemLp.UnitaryGroupMassFormula.fold_L2_double_coset G μ
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PrimesDyadicRS
section
theorem primes_dyadic_range : PI.PrimesDyadicRS.Claim :=
  PI.PrimesDyadicRS.W.claim_of_two PI.PrimesDyadicRS.K.small_natural_numbers_bound PI.PrimesDyadicRS.W.real_dyadic_inequality
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmColExp
section
private theorem bijective_cycleRange_symm_mul_decomposeFin_symm (t : ℕ) :
    Function.Bijective (fun p : Fin (t + 1) × Equiv.Perm (Fin t) =>
      (Fin.cycleRange p.1).symm * Equiv.Perm.decomposeFin.symm ((0 : Fin (t + 1)), p.2)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨l, τ⟩ ⟨l', τ'⟩ h
    simp only at h
    have h0 := congrArg (fun σ : Equiv.Perm (Fin (t + 1)) => σ 0) h
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_zero,
      Fin.cycleRange_symm_zero] at h0
    subst h0
    have h1 := mul_left_cancel h
    have h2 := Equiv.Perm.decomposeFin.symm.injective h1
    simp only [Prod.mk.injEq, true_and] at h2
    rw [h2]
  · simp [Fintype.card_perm, Nat.factorial_succ]

private theorem sum_perm_succ_eq_sum_cycleRange_decomposeFin {M : Type*} [AddCommMonoid M] (t : ℕ) (g : Equiv.Perm (Fin (t + 1)) → M) :
    ∑ σ, g σ = ∑ l : Fin (t + 1), ∑ τ : Equiv.Perm (Fin t),
      g ((Fin.cycleRange l).symm * Equiv.Perm.decomposeFin.symm ((0 : Fin (t + 1)), τ)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ (bijective_cycleRange_symm_mul_decomposeFin_symm t) _ _ (fun _ => rfl)).symm

private theorem sign_cycleRange_symm_mul_decomposeFin_symm (t : ℕ) (l : Fin (t + 1)) (τ : Equiv.Perm (Fin t)) :
    ((Equiv.Perm.sign ((Fin.cycleRange l).symm *
        Equiv.Perm.decomposeFin.symm ((0 : Fin (t + 1)), τ)) : ℤˣ) : ℤ)
      = (-1) ^ (l : ℕ) * (Equiv.Perm.sign τ : ℤ) := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
    Equiv.Perm.decomposeFin.symm_sign]
  simp

private theorem sign_cycleRange_symm_mul_decomposeFin_mul_finRotate (t : ℕ) (l : Fin (t + 1)) (τ : Equiv.Perm (Fin t)) :
    ((Equiv.Perm.sign ((Fin.cycleRange l).symm *
        Equiv.Perm.decomposeFin.symm ((0 : Fin (t + 1)), τ) * finRotate (t + 1)) : ℤˣ) : ℤ)
      = (-1) ^ (t + (l : ℕ)) * (Equiv.Perm.sign τ : ℤ) := by
  rw [Equiv.Perm.sign_mul, Units.val_mul, sign_cycleRange_symm_mul_decomposeFin_symm, sign_finRotate]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    add_tsub_cancel_right, add_tsub_cancel_left]
  ring

private theorem qminor_eq_sum_expand_first_column {A : Type} [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A)
    (a b : Fin (t + 1) → Fin n) (u : ℂ) :
    Formalism.REAL.qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (l : ℕ) : ℤ) : A) *
      (Formalism.REAL.Tm E u (a l) (b 0) *
        Formalism.REAL.qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (u - 1)) := by
  unfold Formalism.REAL.qminor
  rw [sum_perm_succ_eq_sum_cycleRange_decomposeFin]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [sign_cycleRange_symm_mul_decomposeFin_symm, List.ofFn_succ, List.prod_cons]
  have hs : ∀ k : Fin t, u - ((k : ℂ) + 1) = u - 1 - (k : ℂ) := fun k => by ring
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_zero,
    Fin.cycleRange_symm_zero, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self,
    Equiv.refl_apply, Fin.cycleRange_symm_succ, Function.comp_apply, Fin.val_zero,
    Nat.cast_zero, sub_zero, Fin.val_succ, Nat.cast_add, Nat.cast_one, hs]
  rw [Int.cast_mul, mul_assoc]
  congr 1
  rw [← mul_assoc, (Int.cast_commute ((Equiv.Perm.sign τ : ℤˣ) : ℤ)
    (Formalism.REAL.Tm E u (a l) (b 0))).eq, mul_assoc]

private theorem qminor_eq_sum_expand_last_column {A : Type} [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A)
    (a b : Fin (t + 1) → Fin n) (u : ℂ) :
    Formalism.REAL.qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (t + (l : ℕ)) : ℤ) : A) *
      (Formalism.REAL.qminor E (a ∘ l.succAbove) (b ∘ Fin.castSucc) u *
        Formalism.REAL.Tm E (u - (t : ℂ)) (a l) (b (Fin.last t))) := by
  unfold Formalism.REAL.qminor
  rw [← Equiv.sum_comp (Equiv.mulRight (finRotate (t + 1))), sum_perm_succ_eq_sum_cycleRange_decomposeFin]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Equiv.coe_mulRight]
  rw [sign_cycleRange_symm_mul_decomposeFin_mul_finRotate, List.ofFn_succ', List.prod_concat]
  simp only [Equiv.Perm.mul_apply, finRotate_succ_apply, Fin.coeSucc_eq_succ, Fin.last_add_one,
    Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply,
    Fin.cycleRange_symm_succ, Function.comp_apply, Fin.coe_castSucc, Fin.val_last]
  rw [Int.cast_mul]
  simp only [mul_assoc]

theorem quantum_minor_column_expansion : PI.QmColExp := by
  delta PI.QmColExp PI.ExpFirstCol PI.ExpLastCol
  exact ⟨fun A _ _ n t E a b u => qminor_eq_sum_expand_first_column n t E a b u,
    fun A _ _ n t E a b u => qminor_eq_sum_expand_last_column n t E a b u⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmSandwich
section
private theorem rtt_commutator_sandwich_eq_of_relations {M : Type} [Ring M] (R e2b e1b' e1q' e2q e1a' e2a : M)
    (h1 : e2q * e1a' = e1a' * e2q) (h2 : e2b * e1q' = e1q' * e2b) (h3 : e2b * e1a' = e1a' * e2b)
    (h4 : e2a * e1b' = e1b' * e2a) (h5 : e2q * e1b' = e1b' * e2q) (h6 : e2a * e1q' = e1q' * e2a)
    (hP : R * e1b' * e2b = e2b * e1b' * R) (hU : R * e1a' * e2a = e2a * e1a' * R) :
    e2b * e1b' * (R * e1q' * e2q - e2q * e1q' * R) * (e1a' * e2a) =
      R * (e1b' * e1q' * e1a' * (e2b * e2q * e2a)) - e2b * e2q * e2a * (e1b' * e1q' * e1a') * R := by
  rw [mul_sub, sub_mul]
  congr 1
  · calc e2b * e1b' * (R * e1q' * e2q) * (e1a' * e2a)
        = e2b * e1b' * R * e1q' * (e2q * e1a') * e2a := by simp only [mul_assoc]
      _ = R * e1b' * e2b * e1q' * (e1a' * e2q) * e2a := by rw [← hP, h1]
      _ = R * e1b' * (e2b * e1q') * e1a' * e2q * e2a := by simp only [mul_assoc]
      _ = R * e1b' * e1q' * (e2b * e1a') * e2q * e2a := by rw [h2]; simp only [mul_assoc]
      _ = R * (e1b' * e1q' * e1a' * (e2b * e2q * e2a)) := by rw [h3]; simp only [mul_assoc]
  · calc e2b * e1b' * (e2q * e1q' * R) * (e1a' * e2a)
        = e2b * e1b' * e2q * e1q' * (R * e1a' * e2a) := by simp only [mul_assoc]
      _ = e2b * e1b' * e2q * e1q' * (e2a * e1a' * R) := by rw [hU]
      _ = e2b * (e1b' * e2q) * (e1q' * e2a) * e1a' * R := by simp only [mul_assoc]
      _ = e2b * (e2q * e1b') * (e2a * e1q') * e1a' * R := by rw [← h5, ← h6]
      _ = e2b * e2q * (e1b' * e2a) * e1q' * e1a' * R := by simp only [mul_assoc]
      _ = e2b * e2q * e2a * (e1b' * e1q' * e1a') * R := by rw [← h4]; simp only [mul_assoc]

theorem rtt_sandwich' : PI.RTTSandwich := by
  intro A _ _ QQ p c ci p' c' ci' hW hW' hcomm hQ Y Y'
  dsimp only
  have hbu : ∀ (y : ℂ) (i j : Fin 2), ∀ u ∈ ({p, c, ci} : Set A), Commute (Formalism.YangianSpanCharacter.T.Tm y p' c' ci' i j) u := by
    intro y i j u hu
    exact PI.QmSandwichWork.tm_entry_comm y (hcomm u hu p' (by simp)).symm (hcomm u hu c' (by simp)).symm
      (hcomm u hu ci' (by simp)).symm i j
  have hab : ∀ (y y' : ℂ) (i j k l : Fin 2),
      Commute (Formalism.YangianSpanCharacter.T.Tm y p c ci i j) (Formalism.YangianSpanCharacter.T.Tm y' p' c' ci' k l) := by
    intro y y' i j k l
    exact PI.QmSandwichWork.tm_entry_comm y (hbu y' k l p (by simp)).symm (hbu y' k l c (by simp)).symm
      (hbu y' k l ci (by simp)).symm i j
  have haq : ∀ (y y' : ℂ) (i j k l : Fin 2), Commute (Formalism.YangianSpanCharacter.T.Tm y p c ci i j) (QQ y' k l) :=
    fun y y' i j k l => PI.QmSandwichWork.tm_entry_comm y (hQ p (by simp) y' k l) (hQ c (by simp) y' k l)
      (hQ ci (by simp) y' k l) i j
  have hbq : ∀ (y y' : ℂ) (i j k l : Fin 2), Commute (Formalism.YangianSpanCharacter.T.Tm y p' c' ci' i j) (QQ y' k l) :=
    fun y y' i j k l => PI.QmSandwichWork.tm_entry_comm y (hQ p' (by simp) y' k l) (hQ c' (by simp) y' k l)
      (hQ ci' (by simp) y' k l) i j
  have h1 : Formalism.YangianSpanCharacter.T.E2 (QQ Y) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) * Formalism.YangianSpanCharacter.T.E2 (QQ Y) :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => haq Y' Y i j k l).symm
  have h2 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (QQ Y') =
      Formalism.YangianSpanCharacter.T.E1 (QQ Y') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => (hbq Y Y' k l i j).symm).symm
  have h3 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => hab Y' Y i j k l).symm
  have h4 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => (hab Y Y' k l i j).symm).symm
  have h5 : Formalism.YangianSpanCharacter.T.E2 (QQ Y) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') * Formalism.YangianSpanCharacter.T.E2 (QQ Y) :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => hbq Y' Y i j k l).symm
  have h6 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) * Formalism.YangianSpanCharacter.T.E1 (QQ Y') =
      Formalism.YangianSpanCharacter.T.E1 (QQ Y') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) :=
    (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute _ _ fun i j k l => (haq Y Y' k l i j).symm).symm
  have hP : ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Formalism.YangianSpanCharacter.T.Pf A) *
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') =
      Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') *
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Formalism.YangianSpanCharacter.T.Pf A) :=
    Formalism.YangianSpanCharacter.P.rttRelation ℂ A p' c' ci' Y Y' hW'
  have hU : ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Formalism.YangianSpanCharacter.T.Pf A) *
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) =
      Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) *
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Formalism.YangianSpanCharacter.T.Pf A) :=
    Formalism.YangianSpanCharacter.P.rttRelation ℂ A p c ci Y Y' hW
  have hmat := rtt_commutator_sandwich_eq_of_relations _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 hP hU
  change _ = (Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') *
    (_ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) *
    (Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci))) (0, 0) (0, 0)
  rw [hmat, Matrix.sub_apply, PI.QmSandwichWork.flip_row, PI.QmSandwichWork.flip_col, ← Formalism.FourierDecayAlt.P.W.first_embedding_mul,
    ← Formalism.FourierDecayAlt.P.W.first_embedding_mul, ← Formalism.FourierDecayAlt.P.W.entries_mem_mul, ← Formalism.FourierDecayAlt.P.W.entries_mem_mul, PI.QmSandwichWork.block_embedding_mul_entry,
    PI.QmSandwichWork.block_embedding_mul_entry_swap, mul_sub]
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmSkip
section
theorem quantum_minor_skip : PI.QmSkip := by
  have hsa : ∀ {n : ℕ} (p : Fin (n + 1)) (k : Fin n),
      (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
    intro n p k
    unfold Fin.succAbove
    split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]
  refine ⟨fun t i j => ?_, fun t i i' j hii' => ?_⟩
  · apply Fin.ext
    have e := hsa i j
    unfold PI.skip1
    split_ifs at e ⊢ <;> simp only at * <;> omega
  · apply Fin.ext
    have e1 := hsa i i'
    have e2 := hsa i' j
    have e3 := hsa i (i'.succAbove j)
    rw [if_neg (by omega)] at e1
    unfold PI.skip2
    split_ifs at e2 e3 ⊢ <;> simp only at * <;> omega
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittLogarithm
section
private lemma inv_series_sub : PI.InvSerSub := by
  intro K _ S l ex hl hl0 hl1 hex0 hsub n
  obtain ⟨c, hc⟩ := PowerSeries.X_dvd_iff.2 hex0
  have hpow : ∀ d m, PowerSeries.coeff m (ex ^ d) =
      if d ≤ m then PowerSeries.coeff (m - d) (c ^ d) else 0 := by
    intro d m
    rw [hc, mul_pow, PowerSeries.coeff_X_pow_mul']
  have hcoef : ∀ j, PowerSeries.coeff j c = PowerSeries.coeff (j + 1) ex := by
    intro j
    rw [hc, PowerSeries.coeff_succ_X_mul]
  have hHS : PowerSeries.HasSubst ex := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero hex0
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' hex0
    | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [hex0]; exact IsNilpotent.zero)
  have key : ∀ m, PowerSeries.coeff m (PowerSeries.X : PowerSeries K) =
      ∑ d ∈ Finset.range (m + 1), PowerSeries.coeff d l * PowerSeries.coeff m (ex ^ d) := by
    intro m
    have hfin : (∑ᶠ d, PowerSeries.coeff d l • PowerSeries.coeff m (ex ^ d)) =
        ∑ d ∈ Finset.range (m + 1), PowerSeries.coeff d l • PowerSeries.coeff m (ex ^ d) := by
      apply finsum_eq_sum_of_support_subset
      intro d hd
      simp only [Function.mem_support] at hd
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hd
      rw [hpow, if_neg (by omega), smul_zero]
    rw [← hsub, PowerSeries.coeff_subst' hHS, hfin]
    simp only [smul_eq_mul]

  have hB : ∀ N, (∀ j ≤ N, PowerSeries.coeff j c ∈ S) →
      ∀ d, ∀ i ≤ N, PowerSeries.coeff i (c ^ d) ∈ S := by
    intro N hN d
    induction d with
    | zero =>
      intro i _
      rw [pow_zero, PowerSeries.coeff_one]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    | succ d ihd =>
      intro i hi
      rw [pow_succ, PowerSeries.coeff_mul]
      apply Subring.sum_mem
      intro p hp
      have h : p.1 + p.2 = i := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      exact S.mul_mem (ihd _ (by omega)) (hN _ (by omega))
  have hl0' : PowerSeries.coeff 0 l = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hl0]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hex0]
      exact S.zero_mem
    · have k := key (n + 1)
      rw [Finset.sum_range_succ', Finset.sum_range_succ'] at k
      simp only [zero_add, pow_one, hl1, one_mul, hl0', zero_mul, add_zero] at k
      have he : PowerSeries.coeff (n + 1) ex = PowerSeries.coeff (n + 1) (PowerSeries.X : PowerSeries K) -
          ∑ i ∈ Finset.range n, PowerSeries.coeff (i + 1 + 1) l *
            PowerSeries.coeff (n + 1) (ex ^ (i + 1 + 1)) := by
        rw [k]
        ring
      rw [he]
      apply S.sub_mem
      · rw [PowerSeries.coeff_X]
        split_ifs
        · exact S.one_mem
        · exact S.zero_mem
      · apply Subring.sum_mem
        intro i hi
        rw [Finset.mem_range] at hi
        apply S.mul_mem (hl _)
        rw [hpow]
        split_ifs with hle
        · apply hB (n - 1) _ (i + 1 + 1) _ (by omega)
          intro j hj
          rw [hcoef]
          exact ih _ (by omega)
        · exact S.zero_mem

theorem witt_logarithm : PI.WfLog :=
  PI.WfLogWork.wfLog_of inv_series_sub PI.WfLogWork.formal_logarithm_holds
end

