import Formalism.NormUnitaryBounds.Statement
import Formalism.NormUnitaryBounds.DetPolynomialWeights.Bundle0001

-- bundled from Formalism.NormUnitaryBounds.DetPolynomialWeights.GaussianCoefficientFactorialBound
section
open MeasureTheory Complex

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas

open ExponentialIntegralMeasures

lemma norm_sq_coeff_le_gaussian_growth (G : ℕ) (Θ : (Fin G → ℂ) → ℂ) (c : (Fin G → ℕ) → ℂ) (S : ℝ)
    (hΘ : ∀ z : Fin G → ℂ, HasSum (fun e : Fin G → ℕ => c e * ∏ i, z i ^ e i) (Θ z))
    (hS : ∀ z : Fin G → ℂ, ‖Θ z‖ ≤ S * Real.exp ((∑ i, ‖z i‖ ^ 2) / 2))
    (e : Fin G → ℕ) :
    ‖c e‖ ^ 2 * ∏ i, ((e i : ℝ)) ^ e i ≤ S ^ 2 * Real.exp (∑ i, (e i : ℝ)) := by
  set r : Fin G → ℝ := fun i => Real.sqrt (e i) with hr
  have hB : ∀ θ : Fin G → ℝ, ‖Θ (fun i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * I))‖ ≤
      S * Real.exp ((∑ i, (e i : ℝ)) / 2) := by
    intro θ
    have h := hS (fun i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * I))
    have hz : ∀ i, ‖(r i : ℂ) * Complex.exp ((θ i : ℂ) * I)‖ ^ 2 = (e i : ℝ) := by
      intro i
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        sq_abs, hr, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp only [hz] at h
    exact h
  have h1 := cauchy_torus G Θ c hΘ r _ hB e
  have hr' : ∀ i, |r i| = Real.sqrt (e i) := fun i => abs_of_nonneg (Real.sqrt_nonneg _)
  simp only [hr'] at h1
  have h0 : 0 ≤ ‖c e‖ * ∏ i, Real.sqrt (e i) ^ e i := by positivity
  have h2 := pow_le_pow_left₀ h0 h1 2
  have hl : (‖c e‖ * ∏ i, Real.sqrt (e i) ^ e i) ^ 2 = ‖c e‖ ^ 2 * ∏ i, ((e i : ℝ)) ^ e i := by
    rw [mul_pow, ← Finset.prod_pow]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hrr : (S * Real.exp ((∑ i, (e i : ℝ)) / 2)) ^ 2 = S ^ 2 * Real.exp (∑ i, (e i : ℝ)) := by
    rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
    congr 2; ring
  rw [hl, hrr] at h2
  exact h2

theorem gaussian_coefficient_bound_holds : N1 := by
  intro G Θ c S hΘ hS e
  have h := norm_sq_coeff_le_gaussian_growth G Θ c S hΘ hS e
  have hpos : 0 < ∏ i, ((e i : ℝ)) ^ e i := by
    apply Finset.prod_pos
    intro i _
    rcases Nat.eq_zero_or_pos (e i) with h0 | h0
    · rw [h0]; simp
    · positivity
  have hprod : ∏ i, (Real.exp 1 / (e i : ℝ)) ^ e i =
      Real.exp (∑ i, (e i : ℝ)) / ∏ i, ((e i : ℝ)) ^ e i := by
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Real.exp_sum]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.exp_nat_mul, mul_one]
  rw [hprod, ← mul_div_assoc, le_div_iff₀ hpos]
  exact h

end Formalism.NormUnitaryCountingLemmas
end
end

-- bundled from Formalism.NormUnitaryBounds.DetPolynomialWeights.ShearHypothesisOneHolds
section
open MvPolynomial

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas.H1OnPoints

variable {R : Type*} [CommRing R]

lemma core {B : Type*} [CommRing B] [Algebra R B] {N n : ℕ} {ν : Fin (N + 1) → ℕ}
    {F : MvPolynomial (Fin (N + 1) × Fin n) R} (hF : F ∈ H R ν)
    (x : Fin (N + 1) → Fin n → B) (u : Fin n → B) (c : Fin (N + 1) → B)
    (hc : IsLeftRegular (c 0)) :
    (aeval (fun p : Fin (N + 1) × Fin n =>
      Polynomial.C (x p.1 p.2) + Polynomial.X * Polynomial.C (c p.1 * u p.2)) F).natDegree
        ≤ ν 0 := by
  have hW : IsWeightedHomogeneous (blockWt (N + 1) n) F ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hF).1
  set φ : Fin (N + 1) × Fin n → Polynomial B := fun p =>
    Polynomial.C (x p.1 p.2) + Polynomial.X * Polynomial.C (c p.1 * u p.2) with hφ
  let y : Fin (N + 1) × Fin n → Polynomial B := fun p =>
    if p.1 = 0 then Polynomial.C (x 0 p.2) + Polynomial.X * Polynomial.C (c 0 * u p.2)
    else Polynomial.C (c 0 * x p.1 p.2 - c p.1 * x 0 p.2)
  let lam : Fin (N + 1) → Polynomial B := fun j => if j = 0 then 1 else Polynomial.C (c 0)
  let ℓ : B := ∏ j, (if j = 0 then 1 else c 0) ^ ν j
  have hsc := aeval_scale F hW lam φ
  have hfun : (fun p : Fin (N + 1) × Fin n => lam p.1 * φ p) = fun p =>
      y p + if p.1 ∈ Finset.univ.erase 0 then Polynomial.C (c p.1) * y (0, p.2) else 0 := by
    funext p
    obtain ⟨j, k⟩ := p
    by_cases hj : j = 0
    · subst hj
      simp [lam, y, φ]
    · simp only [lam, y, φ, hj, if_false, Finset.mem_erase, ne_eq, not_false_eq_true,
        Finset.mem_univ, and_true, if_true, map_sub, map_mul]
      ring
  have hsh := shear_multi hF y (fun j => Polynomial.C (c j)) (Finset.univ.erase 0) (by simp)
  rw [hfun, hsh] at hsc
  have hdeg := natDegree_aeval_le F hW y (by
    intro p
    by_cases h : p.1 = 0
    · simp only [y, h, if_true]
      have : Polynomial.C (x 0 p.2) + Polynomial.X * Polynomial.C (c 0 * u p.2) =
          Polynomial.C (c 0 * u p.2) * Polynomial.X + Polynomial.C (x 0 p.2) := by ring
      rw [this]
      exact Polynomial.natDegree_linear_le
    · simp only [y, h, if_false]
      exact (Polynomial.natDegree_C _).le)
  have hprodC : (∏ j, lam j ^ ν j) = Polynomial.C ℓ := by
    simp only [lam, ℓ, map_prod, map_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hℓ : IsLeftRegular ℓ := by
    refine Finset.prod_induction _ (fun b : B => IsLeftRegular b) (fun a b ha hb => ha.mul hb)
      (isRegular_one : IsRegular (1 : B)).left fun j _ => IsLeftRegular.pow _ ?_
    split_ifs
    · exact (isRegular_one : IsRegular (1 : B)).left
    · exact hc
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero] at hdeg ⊢
  intro e he
  have h0 := hdeg e he
  rw [hsc, hprodC, Polynomial.coeff_C_mul] at h0
  exact hℓ (h0.trans (mul_zero ℓ).symm)

end Formalism.NormUnitaryCountingLemmas.H1OnPoints

namespace Formalism.NormUnitaryCountingLemmas

open Formalism.NormUnitaryCountingLemmas.H1OnPoints in
theorem shear_hypothesis_one_holds : H1 := by
  intro R _ N n ν F hF A _ _ x u c
  let g : Polynomial A →ₐ[R] A := (Polynomial.aeval (0 : A)).restrictScalars R
  have hreg : IsLeftRegular (Polynomial.C (c 0) + Polynomial.X : Polynomial A) := by
    rw [add_comm]
    exact (Polynomial.monic_X_add_C _).isRegular.left
  have hc := core (B := Polynomial A) hF (fun j k => Polynomial.C (x j k))
    (fun k => Polynomial.C (u k)) (fun j => Polynomial.C (c j) + if j = 0 then Polynomial.X else 0)
    (by simpa using hreg)
  refine le_trans (le_of_eq ?_) ((Polynomial.natDegree_map_le (f := (g : Polynomial A →+* A))).trans hc)
  congr 1
  rw [← Polynomial.coe_mapAlgHom, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 1
  congr 1
  funext p
  by_cases h : p.1 = 0 <;> simp [g, h]

end Formalism.NormUnitaryCountingLemmas
end
end

