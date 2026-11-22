import Formalism.FlagUnipotentLattices.Bundle0002
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SuperdiagonalAdditionInvariance
import Formalism.FlagUnipotentLattices.MemLpTwoOfOneTop
import Formalism.RealPlaceAnalysis.Bundle0004
import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation

-- bundled from Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.GaussSumCharacterAverageBound
section
namespace Formalism.HermitianLatticeCounting.P

open Formalism.HermitianLatticeCounting.S4 Formalism.HermitianLatticeCounting.P.S4aux Finset

theorem geometric_powers_bound : Formalism.HermitianLatticeCounting.S4.GeomPowers := by
  intro q k N hq hk
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hx : (2 : ℝ) ≤ (q : ℝ) ^ (k - 1) := by
    calc (2 : ℝ) ≤ q := hq2
      _ = (q : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (q : ℝ) ^ (k - 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have e : ∀ i : ℕ, ((q : ℝ) ^ i) ^ (k - 1) = ((q : ℝ) ^ (k - 1)) ^ i := fun i => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [e]
  have := geo_q _ hx N
  linarith

theorem hermitian_assembly_numeric_bound : Formalism.HermitianLatticeCounting.S4.WeightedAmplitudeSqSumBoundTwoTypeClasses := by
  intro k r q H nn D Ty _ _ w amp μ be isBe hk hq hH hqH hnn hw hTy hbe hμ hμbe hμal hsum hamp hampbe
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 2 * r + 5 := ⟨k - 2 * r - 5, by omega⟩
  have hq0 : (0 : ℝ) < q := by positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have e1 : (q : ℝ) ^ (-(((K + 2 * r + 5 : ℕ) : ℤ) - 2 * r - 5)) = ((q : ℝ) ^ K)⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
  have e2 : (q : ℝ) ^ (1 - (((K + 2 * r + 5 : ℕ) : ℤ) - 2 * r - 3)) = ((q : ℝ) ^ (K + 1))⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
  rw [e1]; rw [e2] at hampbe
  have e3 : K + 2 * r + 5 - 1 = K + (2 * r + 4) := by omega
  rw [e3] at hμbe hμal hsum
  set n : ℕ := K + (2 * r + 4) with hn
  set A0 : ℝ := H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) with hA0
  set A1 : ℝ := H ^ (4 * (r + 1)) with hA1
  have hA0p : 0 < A0 := by positivity
  have hA1p : 0 < A1 := by positivity
  by_cases hne : Nonempty Ty
  swap
  · have : IsEmpty Ty := not_nonempty_iff.1 hne
    simp only [Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero]
    positivity
  have hqH' := hqH hne
  have per : ∀ t, ∑ d, w d * ‖amp t d‖ ^ 2 ≤ 392 * A0 * A1 * ((q : ℝ) ^ K)⁻¹ * nn := by
    intro t
    have hbe0 : 0 < be t := lt_of_lt_of_le one_pos (hbe t)
    obtain ⟨ε, X, hε0, hX0, hε, hX, hεb⟩ : ∃ ε X : ℝ, 0 ≤ ε ∧ 0 ≤ X ∧ (∀ d, ‖amp t d‖ ≤ ε * μ t d) ∧
        (∀ d, μ t d ≤ 2 * A0 * X) ∧ ε ^ 2 * (X * (be t ^ n)⁻¹) ≤ 49 * ((q : ℝ) ^ K)⁻¹ := by
      by_cases hb : isBe t
      · refine ⟨7 * ((q : ℝ) ^ (K + 1))⁻¹, be t ^ n, by positivity, by positivity,
          fun d => hampbe t d hb, fun d => hμbe t d hb, ?_⟩
        have h1 : be t ^ n * (be t ^ n)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
        rw [h1, mul_one, mul_pow]
        have h3 : (((q : ℝ) ^ (K + 1))⁻¹) ^ 2 ≤ ((q : ℝ) ^ K)⁻¹ := by
          rw [inv_pow, ← pow_mul]
          apply inv_anti₀ (by positivity)
          exact pow_le_pow_right₀ hq1 (by omega)
        nlinarith
      · refine ⟨1, (be t / q) ^ n, zero_le_one, by positivity, fun d => by rw [one_mul]; exact hamp t d,
          fun d => hμal t d hb, ?_⟩
        have h2 : (be t / q) ^ n * (be t ^ n)⁻¹ = ((q : ℝ) ^ n)⁻¹ := by
          rw [div_pow]; field_simp
        have h3 : ((q : ℝ) ^ n)⁻¹ ≤ ((q : ℝ) ^ K)⁻¹ := by
          apply inv_anti₀ (by positivity)
          exact pow_le_pow_right₀ hq1 (by omega)
        have h4 : 0 < ((q : ℝ) ^ K)⁻¹ := by positivity
        rw [h2]
        nlinarith
    have hms := S4aux.maximal_sum_bound D w (μ t) (amp t) ε (2 * A0 * X) hw (hμ t) hε0 hε hX
    calc _ ≤ _ := hms
      _ ≤ ε ^ 2 * (2 * A0 * X) * (4 * A1 * (be t ^ n)⁻¹ * nn) := by
          gcongr; exact hsum t
      _ = (ε ^ 2 * (X * (be t ^ n)⁻¹)) * (8 * A0 * A1 * nn) := by ring
      _ ≤ (49 * ((q : ℝ) ^ K)⁻¹) * (8 * A0 * A1 * nn) := by gcongr
      _ = _ := by ring
  have h392 : (392 : ℝ) ≤ H ^ 9 := by
    calc (392 : ℝ) ≤ 2 ^ 9 := by norm_num
      _ ≤ H ^ 9 := by
          gcongr
          refine le_trans ?_ hqH'
          exact_mod_cast hq
  have hexp : (r + 2) + (r + 2) + 9 + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1) ≤ 39 * (r + 1) ^ 2 := by
    nlinarith
  calc _ ≤ _ := S4aux.type_cauchy_schwarz D Ty w amp hw
    _ ≤ H ^ (r + 2) * ∑ t : Ty, 392 * A0 * A1 * ((q : ℝ) ^ K)⁻¹ * nn := by
        gcongr with t
        · exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun d _ => mul_nonneg (hw d) (sq_nonneg _)
        · exact per t
    _ = (Fintype.card Ty : ℝ) * (H ^ (r + 2) * (392 * A0 * A1 * ((q : ℝ) ^ K)⁻¹ * nn)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ H ^ (r + 2) * (H ^ (r + 2) * (H ^ 9 * A0 * A1 * ((q : ℝ) ^ K)⁻¹ * nn)) := by
        gcongr
    _ = H ^ ((r + 2) + (r + 2) + 9 + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1)) * ((q : ℝ) ^ K)⁻¹ * nn := by
        rw [pow_add, pow_add, pow_add, pow_add]; ring
    _ ≤ _ := by
        gcongr

theorem non_generic_bound_large_height : Formalism.HermitianLatticeCounting.S4.NonGenericBoundLargeHeight := by
  intro k r H nn D Ty _ _ w amp μ be hH hnn hw hTy hbe hμ hμM hsum hamp
  have hH1 : (1 : ℝ) ≤ H := by linarith
  set n : ℕ := k - 1 with hn
  set A0 : ℝ := H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) with hA0
  set A1 : ℝ := H ^ (4 * (r + 1)) with hA1
  have hA0p : 0 < A0 := by positivity
  have hA1p : 0 < A1 := by positivity
  have per : ∀ t, ∑ d, w d * ‖amp t d‖ ^ 2 ≤ 8 * A0 * A1 * nn := by
    intro t
    have hbe0 : 0 < be t := lt_of_lt_of_le one_pos (hbe t)
    have hms := S4aux.maximal_sum_bound D w (μ t) (amp t) 1 (2 * A0 * be t ^ n) hw (hμ t) zero_le_one
      (fun d => by rw [one_mul]; exact hamp t d) (hμM t)
    have h1 : be t ^ n * (be t ^ n)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    calc _ ≤ _ := hms
      _ ≤ 1 ^ 2 * (2 * A0 * be t ^ n) * (4 * A1 * (be t ^ n)⁻¹ * nn) := by
          gcongr; exact hsum t
      _ = (be t ^ n * (be t ^ n)⁻¹) * (8 * A0 * A1 * nn) := by ring
      _ = _ := by rw [h1, one_mul]
  have h8 : (8 : ℝ) ≤ H ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ H ^ 3 := by gcongr
  have hexp : 1 + 1 + 3 + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1) ≤ 39 * (r + 1) ^ 2 := by
    nlinarith
  calc _ ≤ _ := S4aux.type_cauchy_schwarz D Ty w amp hw
    _ ≤ H * ∑ t : Ty, 8 * A0 * A1 * nn := by
        gcongr with t
        · exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun d _ => mul_nonneg (hw d) (sq_nonneg _)
        · exact per t
    _ = (Fintype.card Ty : ℝ) * (H * (8 * A0 * A1 * nn)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ H * (H * (H ^ 3 * A0 * A1 * nn)) := by
        gcongr
    _ = H ^ (1 + 1 + 3 + (9 * (r + 1) ^ 2 + 12 * (r + 1)) + 4 * (r + 1)) * nn := by
        rw [pow_add, pow_add, pow_add, pow_add, pow_one]; ring
    _ ≤ _ := by
        gcongr

end Formalism.HermitianLatticeCounting.P
end

-- bundled from Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.InterlacingOfBlocksSecondCase
section
open Formalism.HermitianLatticeCounting.S8 MeasureTheory Filter Topology TensorProduct Finset

set_option linter.all false

noncomputable section

namespace Formalism.HermitianLatticeCounting.P

theorem assembly_of_second_bound : AssemblyB := by
  intro T _ μ E _ _ P χ W h1 h2 h0
  have e1 : (∫ x, (inner ℂ (W x) (P (fun y => (χ y : ℂ) • W y) x) : ℂ) ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [h0] with x hx
    simp only [hx, Pi.zero_apply, inner_zero_right]
  have e2 : (∫ x, (inner ℂ (W x) ((χ x : ℂ) • W x) : ℂ) ∂μ) = ((∫ x, χ x * ‖W x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1; ext x
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [e1, e2] at h1
  have := Complex.ofReal_eq_zero.mp h1.symm
  linarith

theorem conjugate_dual_representation : ConjDual := by
  intro E _ _ _ G _ ρ hu g v
  have h1 : ρ g * star (ρ g) = 1 := (Unitary.mem_iff.mp (hu g)).2
  have h2 : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul]; simp
  have h3 : ρ g⁻¹ = star (ρ g) := by
    calc ρ g⁻¹ = ρ g⁻¹ * (ρ g * star (ρ g)) := by rw [h1, mul_one]
      _ = star (ρ g) := by rw [← mul_assoc, h2, one_mul]
  ext y
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply]
  rw [h3, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

theorem residue_formula : Residue := by
  intro E _ _ n k lam u a K s₀ s₁ hinj hK H i
  have key : (∏ s ∈ univ.erase i, (lam i - lam s)) • a i = (∏ j, (lam i - s₀ + s₁ - u j)) • K := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    set P : Polynomial ℂ := ∑ i', Polynomial.C (φ (a i')) *
      ∏ s ∈ univ.erase i', (Polynomial.X + Polynomial.C (s₀ - lam s)) with hP
    set Q : Polynomial ℂ := Polynomial.C (φ K) * ∏ j, (Polynomial.X + Polynomial.C (s₁ - u j)) with hQ
    have evP : ∀ x, P.eval x = ∑ i', φ (a i') * ∏ s ∈ univ.erase i', (x + (s₀ - lam s)) := by
      intro x
      simp only [hP, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
        Polynomial.eval_add, Polynomial.eval_X]
    have evQ : ∀ x, Q.eval x = φ K * ∏ j, (x + (s₁ - u j)) := by
      intro x
      simp only [hQ, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
        Polynomial.eval_add, Polynomial.eval_X]
    have hPQ : P = Q := by
      apply Polynomial.eq_of_infinite_eval_eq
      have hfin : (Set.range fun s => lam s - s₀).Finite := Set.finite_range _
      refine hfin.infinite_compl.mono ?_
      intro x hx
      have hx' : ∀ s, x + s₀ - lam s ≠ 0 := by
        intro s h0
        apply hx
        exact ⟨s, by linear_combination -h0⟩
      have h1 := congrArg φ (H x hx')
      simp only [map_sum, map_smul, smul_eq_mul] at h1
      have hD : (∏ s, (x + s₀ - lam s)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun s _ => hx' s)
      show P.eval x = Q.eval x
      rw [evP, evQ]
      have h2 : ∀ i', φ (a i') * ∏ s ∈ univ.erase i', (x + (s₀ - lam s)) =
          (∏ s, (x + s₀ - lam s)) * ((x - (lam i' - s₀))⁻¹ * φ (a i')) := by
        intro i'
        rw [← Finset.mul_prod_erase univ (fun s => x + s₀ - lam s) (Finset.mem_univ i')]
        have h3 : x - (lam i' - s₀) = x + s₀ - lam i' := by ring
        have h4 : ∀ s, x + (s₀ - lam s) = x + s₀ - lam s := fun s => by ring
        simp only [h3, h4]
        field_simp [hx' i']
      simp only [h2]
      rw [← Finset.mul_sum, h1]
      have h5 : ∀ j, x + (s₁ - u j) = x + s₁ - u j := fun j => by ring
      simp only [h5]
      field_simp
    have h6 := congrArg (Polynomial.eval (lam i - s₀)) hPQ
    rw [evP, evQ, Finset.sum_eq_single i] at h6
    · rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, sub_eq_zero]
      have h7 : ∀ s, lam i - s₀ + (s₀ - lam s) = lam i - lam s := fun s => by ring
      have h8 : ∀ j, lam i - s₀ + (s₁ - u j) = lam i - s₀ + s₁ - u j := fun j => by ring
      simp only [h7, h8] at h6
      rw [mul_comm, h6, mul_comm]
    · intro i' _ hi'
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hi', Finset.mem_univ i⟩) (by ring), mul_zero]
    · simp
  have hc : (∏ s ∈ univ.erase i, (lam i - lam s)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro s hs
    rw [sub_ne_zero]
    intro h
    exact (Finset.mem_erase.mp hs).1 (hinj h).symm
  constructor
  · intro h0
    rw [h0, smul_zero] at key
    have := (smul_eq_zero.mp key.symm).resolve_right hK
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp this
    exact ⟨j, by linear_combination -hj⟩
  · rintro ⟨j, hj⟩
    have : (∏ j, (lam i - s₀ + s₁ - u j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj]; ring)
    rw [this, zero_smul] at key
    exact (smul_eq_zero.mp key).resolve_left hc

def gdet {A : Type*} [Ring A] (t : ℕ) (F : ℕ → ℕ → ℂ → A) (x : ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign σ : ℤ) : A) * (List.ofFn fun p : Fin t => F (σ p) p (x - (p : ℂ))).prod

theorem swap_lt {κ q i : ℕ} (hq : q ≤ κ) (hi : i < κ) : Equiv.swap 0 q (i + 1) < κ + 1 := by
  simp only [Equiv.swap_apply_def]; split_ifs <;> omega

def rowN {n : ℕ} (r k : ℕ) (c w : ℕ → Fin n) (p : ℕ) : Fin n :=
  if p < r then c (p + 1) else if p < r + k then w (p - r) else c (p - k + 1)

def colN {n : ℕ} (r k : ℕ) (c w : ℕ → Fin n) (p : ℕ) : Fin n :=
  if p < r then c p else if p < r + k then w (p - r) else c (p - k)

def gN {n : ℕ} (r k : ℕ) (c w : ℕ → Fin n) (p : ℕ) : Fin n :=
  if p = 0 then c r else if p ≤ r then c (p - 1) else if p ≤ r + k then w (p - r - 1) else c (p - k)

theorem cyc_val {m : ℕ} (i j : Fin (m + 1)) :
    ((Fin.cycleRange i j : Fin (m + 1)) : ℕ) =
      if (j : ℕ) < i then (j : ℕ) + 1 else if (j : ℕ) = i then 0 else (j : ℕ) := by
  rcases lt_trichotomy j i with h | h | h
  · rw [Fin.coe_cycleRange_of_lt h, if_pos (show (j : ℕ) < i from h)]
  · subst h; simp
  · rw [Fin.cycleRange_of_gt h, if_neg (by have : (i : ℕ) < j := h; omega),
      if_neg (by have : (i : ℕ) < j := h; omega)]

end Formalism.HermitianLatticeCounting.P
end
end

-- bundled from Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.NormalisationIdentity
section
namespace Formalism.HermitianLatticeCounting.P
open Finset Formalism.HermitianLatticeCounting.ExpansionTerms

noncomputable def brG (c : ℝ) (j : ℕ) : ℝ := if j = 0 then 2 + c else 1 + 1 / (j : ℝ)

end Formalism.HermitianLatticeCounting.P
end

