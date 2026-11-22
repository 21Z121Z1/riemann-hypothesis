import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PPolarisationBound
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem prod_factorial_le_factorial_of_sum {σ : Type*} (m : σ →₀ ℕ) (n : ℕ)
    (hm : (m.sum fun _ e => e) = n) :
    (m.prod fun _ e => (e.factorial : ℝ)) ≤ (n.factorial : ℝ) := by
  have hd : (∏ i ∈ m.support, (m i).factorial) ∣ (∑ i ∈ m.support, m i).factorial :=
    Nat.prod_factorial_dvd_factorial_sum _ _
  have hle : (∏ i ∈ m.support, (m i).factorial) ≤ n.factorial := by
    rw [← hm]; exact Nat.le_of_dvd (Nat.factorial_pos _) hd
  show (∏ a ∈ m.support, ((m a).factorial : ℝ)) ≤ (n.factorial : ℝ)
  exact_mod_cast hle

theorem PolarisationBound.proof (hC : PolarisationCoeff.Statement) : PolarisationBound.Statement := by
  intro σ _ n
  refine ⟨fun Φ Ψ hΦΨ F hF => ?_, fun Φ m M hm hM => ?_⟩
  ·
    have hmono : ∀ m : σ →₀ ℕ, (m.sum fun _ e => e) = n → Φ (monomial m 1) = Ψ (monomial m 1) := by
      intro m hm
      rw [hC σ Φ n m hm, hC σ Ψ n m hm, hΦΨ]
    conv_lhs => rw [F.as_sum]
    conv_rhs => rw [F.as_sum]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun m hmF => ?_)
    have hdeg : (m.sum fun _ e => e) = n := by
      have := hF (mem_support_iff.1 hmF)
      simpa [Finsupp.weight_apply, Finsupp.sum] using this
    have hsm : monomial m (coeff m F) = coeff m F • monomial m (1 : ℝ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hsm, map_smul, map_smul, hmono m hdeg]
  · have hc := hM m
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) hc
    have hfac := prod_factorial_le_factorial_of_sum m n hm
    have hpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hpnn : (0 : ℝ) ≤ (m.prod fun _ e => (e.factorial : ℝ)) := by
      unfold Finsupp.prod
      exact Finset.prod_nonneg (fun _ _ => by positivity)
    have hq0 : 0 ≤ (m.prod fun _ e => (e.factorial : ℝ)) / (n.factorial : ℝ) := div_nonneg hpnn hpos.le
    have hq1 : (m.prod fun _ e => (e.factorial : ℝ)) / (n.factorial : ℝ) ≤ 1 := by
      rw [div_le_one hpos]; exact hfac
    rw [hC σ Φ n m hm, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg hq0]
    calc (m.prod fun _ e => (e.factorial : ℝ)) / (n.factorial : ℝ) * |coeff m (polarPoly Φ n)|
        ≤ 1 * |coeff m (polarPoly Φ n)| :=
          mul_le_mul_of_nonneg_right hq1 (abs_nonneg _)
      _ ≤ M := by rw [one_mul]; exact hc

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PPolarisationCoeff
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem PolarisationCoeff.prod_X_pow_eq_monomial_one {σ S : Type*} [CommSemiring S] [Fintype σ] (K : σ →₀ ℕ) :
    ∏ v, (X v : MvPolynomial σ S) ^ K v = monomial K 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem PolarisationCoeff.coeff_polarPoly {σ R : Type*} [CommRing R] [Fintype σ]
    (Φ : MvPolynomial σ R →ₗ[R] R) (n : ℕ) (m : σ →₀ ℕ) :
    coeff m (polarPoly Φ n) = Φ (coeff m ((-outerDot σ R) ^ n)) := by
  classical
  unfold polarPoly
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

theorem PolarisationCoeff.coeff_outerDot_pow {σ R : Type*} [CommRing R] [Fintype σ] (n : ℕ) (m : σ →₀ ℕ)
    (hm : (m.sum fun _ e => e) = n) :
    coeff m ((outerDot σ R) ^ n) = (Nat.multinomial univ m : MvPolynomial σ R) * monomial m 1 := by
  classical
  unfold outerDot
  rw [Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]
  have hterm : ∀ k : σ → ℕ,
      (Nat.multinomial univ k : MvPolynomial σ (MvPolynomial σ R)) *
          ∏ v, (X v * C (X v) : MvPolynomial σ (MvPolynomial σ R)) ^ k v =
        monomial (Finsupp.equivFunOnFinite.symm k)
          ((Nat.multinomial univ k : MvPolynomial σ R) *
            monomial (Finsupp.equivFunOnFinite.symm k) 1) := by
    intro k
    simp_rw [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    have h1 := PolarisationCoeff.prod_X_pow_eq_monomial_one (S := MvPolynomial σ R) (Finsupp.equivFunOnFinite.symm k)
    have h2 := PolarisationCoeff.prod_X_pow_eq_monomial_one (S := R) (Finsupp.equivFunOnFinite.symm k)
    simp only [Finsupp.coe_equivFunOnFinite_symm] at h1 h2
    rw [h1, h2, ← map_natCast (C : MvPolynomial σ R →+* _),
      mul_comm (monomial _ (1 : MvPolynomial σ R)) (C _), C_mul_monomial, mul_one, C_mul_monomial]
  simp_rw [hterm, coeff_monomial]
  have hiff : ∀ k : σ → ℕ, Finsupp.equivFunOnFinite.symm k = m ↔ (⇑m : σ → ℕ) = k := by
    intro k
    constructor
    · rintro rfl; rfl
    · rintro rfl; exact Finsupp.equivFunOnFinite.symm_apply_apply m
  simp_rw [hiff]
  rw [Finset.sum_ite_eq]
  have hmem : (⇑m : σ → ℕ) ∈ piAntidiag univ n := by
    rw [mem_piAntidiag]
    refine ⟨?_, fun i _ => mem_univ i⟩
    rw [← hm, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  rw [if_pos hmem, Finsupp.equivFunOnFinite_symm_coe]

theorem PolarisationCoeff.proof : PolarisationCoeff.Statement := by
  intro σ _ Φ n m hm
  classical
  have hneg : ((-1 : MvPolynomial σ (MvPolynomial σ ℝ)) ^ n) = C ((-1 : MvPolynomial σ ℝ) ^ n) := by
    simp
  rw [PolarisationCoeff.coeff_polarPoly, neg_pow (outerDot σ ℝ), hneg, coeff_C_mul,
    PolarisationCoeff.coeff_outerDot_pow n m hm]
  have hsmul : (-1 : MvPolynomial σ ℝ) ^ n * ((Nat.multinomial univ m : MvPolynomial σ ℝ) * monomial m 1) =
      ((-1 : ℝ) ^ n * (Nat.multinomial univ m : ℝ)) • monomial m 1 := by
    rw [smul_eq_C_mul, C_mul, C_pow, C_neg, C_1, map_natCast (C : ℝ →+* MvPolynomial σ ℝ), mul_assoc]
  rw [hsmul, map_smul, smul_eq_mul]
  have hsum : ∑ v, m v = n := by rw [← hm, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  have hprod : (m.prod fun _ e => (e.factorial : ℝ)) * (Nat.multinomial univ m : ℝ) = (n.factorial : ℝ) := by
    rw [Finsupp.prod_fintype _ _ (fun _ => by simp), ← hsum]
    exact_mod_cast Nat.multinomial_spec univ m
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hsq : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by rw [← mul_pow]; simp
  calc Φ (monomial m 1)
      = ((-1 : ℝ) ^ n * (-1) ^ n) * (((m.prod fun _ e => (e.factorial : ℝ)) *
          (Nat.multinomial univ m : ℝ)) / (n.factorial : ℝ)) * Φ (monomial m 1) := by
        rw [hsq, hprod, div_self hn, one_mul, one_mul]
    _ = _ := by ring

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PShOfPower
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem ShOfPower.pderiv_lineClass (d : IndexData) (u : Idx d → ℚ) (p : Idx d) :
    pderiv p (lineClass d u) = C (-u p) := by
  classical
  unfold lineClass lamDotX
  rw [map_neg, map_sum]
  simp only [pderiv_C_mul]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp [pderiv_X_of_ne hq]
  · simp

theorem ShOfPower.pderiv_lineClass_pow (d : IndexData) (u : Idx d → ℚ) (p : Idx d) :
    pderiv p (lineClass d u ^ (d.D + 1)) =
      C (-((d.D + 1 : ℕ) : ℚ) * u p) * lineClass d u ^ d.D := by
  rw [pderiv_pow, ShOfPower.pderiv_lineClass, Nat.add_sub_cancel]
  simp only [map_mul, map_neg, map_natCast]
  ring

theorem ShOfPower.proof : ShOfPower.Statement := by
  intro d τ u
  have hs : ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j),
        pderiv (τ, i) (lineClass d u ^ (d.D + 1)) =
      C (-((d.D + 1 : ℕ) : ℚ) * ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), u (τ, i)) *
        lineClass d u ^ d.D := by
    rw [Finset.mul_sum, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => ShOfPower.pderiv_lineClass_pow d u (τ, i))
  unfold shiftFl degAt
  rw [hs, C_mul', LinearMap.map_smul, smul_eq_mul]
  ring

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.PTotOfPower
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem pderiv_lineClass (d : IndexData) (u : Idx d → ℚ) (p : Idx d) :
    pderiv p (lineClass d u) = C (-(u p)) := by
  classical
  simp only [lineClass, lamDotX, map_neg, map_sum, pderiv_C_mul, pderiv_X, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_pderiv_lineClass_pow (d : IndexData) (τ : Fin d.f) (u : Idx d → ℚ) :
    ∑ i : Fin d.N, pderiv (τ, i) (lineClass d u ^ (d.D + 1)) =
      C (-((d.D + 1 : ℕ) : ℚ) * ∑ i : Fin d.N, u (τ, i)) * lineClass d u ^ d.D := by
  simp only [pderiv_pow, pderiv_lineClass, Nat.add_sub_cancel]
  rw [Finset.mul_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_neg, map_natCast]
  ring

theorem TotOfPower.proof : TotOfPower.Statement := by
  intro d τ u
  rw [totalFl, sum_pderiv_lineClass_pow, ← smul_eq_C_mul, map_smul, smul_eq_mul, degAt]
  ring

end GroundTheory.Heights₂.Heights.TheoremB
end
end

