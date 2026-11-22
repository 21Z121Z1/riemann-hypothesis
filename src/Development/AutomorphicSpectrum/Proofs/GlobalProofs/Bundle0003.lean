import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdaptedFrameOrthogonalSubspaceStatement
section
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_basis_change_entries : ∀ (n n' a : ℕ) (hdim : a + n' + a = n) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P.det →
    ∀ (J : Matrix (Fin n) (Fin n') ℂ) (Jp : Matrix (Fin n') (Fin n) ℂ) (B Bi : Matrix (Fin n') (Fin n') ℂ), Jp * J = 1 → B * Bi = 1 →
    (∀ (i : Fin n) (j : Fin n'), J i j = ∑ r : Fin n', P i (⟨a + r.val, by omega⟩ : Fin n) * B r j) →
    (∀ b : Fin n, (b.val < a ∨ n ≤ b.val + a) → Jp *ᵥ (fun k => P k b) = 0) →
    ∀ p q : Fin n', J * Matrix.single p q (1 : ℂ) * Jp = ∑ r : Fin n', ∑ u : Fin n', (B r p * Bi q u) •
      (P * Matrix.single (⟨a + r.val, by omega⟩ : Fin n) (⟨a + u.val, by omega⟩ : Fin n) (1 : ℂ) * P⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.MidConj.conj_units_of_mid | exact GlobalTheory.CompanionTheory.MidConj.conj_units_of_mid | (intros; apply GlobalTheory.CompanionTheory.MidConj.conj_units_of_mid <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlockBasisChangeEntries
section
open Matrix

namespace GlobalTheory.CompanionTheory.IsometricMatrix

theorem exp_mulVec_of_mulVec_eq_zero {m : ℕ} (N : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ)
    (hx : N *ᵥ x = 0) : NormedSpace.exp N *ᵥ x = x := by
  have hC : N * Matrix.replicateCol (Fin 1) x = Matrix.replicateCol (Fin 1) x * (0 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    have hi := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hi
    simpa [Matrix.mul_apply, Matrix.replicateCol] using hi
  have hE := matrix_exp_mul_eq_mul_exp_of_intertwine N _ 0 hC
  simp only [NormedSpace.exp_zero, Matrix.mul_one] at hE
  ext i
  have hi := congrFun (congrFun hE i) 0
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.replicateCol] using hi

theorem main {n n' : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (H' : Matrix (Fin n') (Fin n') ℂ)
    (J : Matrix (Fin n) (Fin n') ℂ)
    (hH : Hᴴ = H) (hH' : H'ᴴ = H') (hd : IsUnit H.det) (hd' : IsUnit H'.det)
    (hJ : Jᴴ * H * J = H') :
    ((H'⁻¹ * Jᴴ * H) * J = 1 ∧
      (∀ Z : Matrix (Fin n') (Fin n') ℂ, -(H⁻¹ * (J * Z * (H'⁻¹ * Jᴴ * H))ᴴ * H) = J * (-(H'⁻¹ * Zᴴ * H')) * (H'⁻¹ * Jᴴ * H)) ∧
      (∀ A : Matrix (Fin n') (Fin n') ℂ, Aᴴ * H' + H' * A = 0 →
        (J * A * (H'⁻¹ * Jᴴ * H))ᴴ * H + H * (J * A * (H'⁻¹ * Jᴴ * H)) = 0) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ), NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) * J = J * NormedSpace.exp (t • A)) ∧
      (∀ (A : Matrix (Fin n') (Fin n') ℂ) (t : ℝ) (x : Fin n → ℂ), (Jᴴ * H) *ᵥ x = 0 →
        NormedSpace.exp (t • (J * A * (H'⁻¹ * Jᴴ * H))) *ᵥ x = x)) := by
  have hJ' : Jᴴ * (H * J) = H' := by rw [← Matrix.mul_assoc]; exact hJ
  have hPJ : H'⁻¹ * Jᴴ * H * J = 1 := by
    simp only [Matrix.mul_assoc]
    rw [hJ', Matrix.nonsing_inv_mul _ hd']
  have hPs : (H'⁻¹ * Jᴴ * H)ᴴ = H * J * H'⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, hH, hH', Matrix.mul_assoc]
  refine ⟨hPJ, fun Z => ?_, fun A hA => ?_, fun A t => ?_, fun A t x hx => ?_⟩
  · rw [Matrix.conjTranspose_mul (J * Z) (H'⁻¹ * Jᴴ * H), hPs, Matrix.conjTranspose_mul J Z]
    simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.mul_nonsing_inv_cancel_left _ _ hd']
  · have key : H * J * H'⁻¹ * (Aᴴ * H' + H' * A) * (H'⁻¹ * Jᴴ * H) =
        (J * A * (H'⁻¹ * Jᴴ * H))ᴴ * H + H * (J * A * (H'⁻¹ * Jᴴ * H)) := by
      rw [Matrix.conjTranspose_mul (J * A) (H'⁻¹ * Jᴴ * H), hPs, Matrix.conjTranspose_mul J A,
        Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd',
        Matrix.mul_nonsing_inv_cancel_left _ _ hd']
    rw [← key, hA, Matrix.mul_zero, Matrix.zero_mul]
  · have hBJ : J * A * (H'⁻¹ * Jᴴ * H) * J = J * A := by
      rw [Matrix.mul_assoc, hPJ, Matrix.mul_one]
    exact matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine n n' _ J A hBJ t
  · have hB : (J * A * (H'⁻¹ * Jᴴ * H)) *ᵥ x = 0 := by
      have hfac : J * A * (H'⁻¹ * Jᴴ * H) = (J * A * H'⁻¹) * (Jᴴ * H) := by
        simp only [Matrix.mul_assoc]
      rw [hfac, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    apply exp_mulVec_of_mulVec_eq_zero
    rw [Matrix.smul_mulVec, hB, smul_zero]

end GlobalTheory.CompanionTheory.IsometricMatrix
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlockMatrixMulBlocks
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.BlockMul

theorem blocks_mul : ∀ {F : Type} [Field F] (r d c e : ℕ) (x : Matrix (Fin (r + d)) (Fin (r + c)) F) (y : Matrix (Fin (r + c)) (Fin (r + e)) F), bAA (x * y) = bAA x * bAA y + bAD x * bDA y ∧ bAD (x * y) = bAA x * bAD y + bAD x * bDD y ∧ bDA (x * y) = bDA x * bAA y + bDD x * bDA y ∧ bDD (x * y) = bDA x * bAD y + bDD x * bDD y := by
  intro F _ r d c e x y
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp only [bAA, bAD, bDA, bDD, Matrix.submatrix_apply, Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_add]

end GlobalTheory.CompanionTheory.QL.BlockMul
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DigammaLogBoundRightHalfPlane
section
namespace GlobalTheory.CompanionTheory.DigammaBound

open Finset

lemma add_half_le_norm (z : ℂ) (hz : 1 / 2 ≤ z.re) (x : ℝ) (hx : 0 ≤ x) :
    x + 1 / 2 ≤ ‖z + (x : ℂ)‖ := by
  have h := Complex.abs_re_le_norm (z + (x : ℂ))
  have h2 : (z + (x : ℂ)).re = z.re + x := by simp
  rw [h2] at h
  have := le_abs_self (z.re + x)
  linarith

lemma term_eq (z : ℂ) (hz : 1 / 2 ≤ z.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / (z + ((k : ℂ) + 1))‖ =
      ‖z‖ / (((k : ℝ) + 1) * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hc : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  have hN := add_half_le_norm z hz ((k : ℝ) + 1) hk
  have h2 : z + (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hN
    linarith
  have h1 : (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    rw [← hc]
    exact_mod_cast Nat.succ_ne_zero k
  rw [hc]
  have : 1 / (((k : ℝ) + 1 : ℝ) : ℂ) - 1 / (z + (((k : ℝ) + 1 : ℝ) : ℂ)) =
      z / ((((k : ℝ) + 1 : ℝ) : ℂ) * (z + (((k : ℝ) + 1 : ℝ) : ℂ))) := by
    field_simp
    ring
  rw [this, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk]

lemma term_le_two (z : ℂ) (hz : 1 / 2 ≤ z.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / (z + ((k : ℂ) + 1))‖ ≤ 2 * ((k : ℝ) + 1)⁻¹ := by
  rw [term_eq z hz k]
  have ha : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hN := add_half_le_norm z hz ((k : ℝ) + 1) ha.le
  have hz' : ‖z‖ ≤ ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖ + ((k : ℝ) + 1) := by
    have h := norm_sub_le (z + (((k : ℝ) + 1 : ℝ) : ℂ)) (((k : ℝ) + 1 : ℝ) : ℂ)
    rw [add_sub_cancel_right, Complex.norm_real, Real.norm_of_nonneg ha.le] at h
    exact h
  have hNpos : 0 < ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖ := by linarith
  rw [div_le_iff₀ (by positivity)]
  have : 2 * ((k : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖) =
      2 * ‖z + (((k : ℝ) + 1 : ℝ) : ℂ)‖ := by
    field_simp
  rw [this]
  linarith

lemma term_le_sq (z : ℂ) (hz : 1 / 2 ≤ z.re) (k : ℕ) :
    ‖1 / ((k : ℂ) + 1) - 1 / (z + ((k : ℂ) + 1))‖ ≤ ‖z‖ / ((k : ℝ) + 1) ^ 2 := by
  rw [term_eq z hz k]
  have ha : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hN := add_half_le_norm z hz ((k : ℝ) + 1) ha.le
  apply div_le_div_of_nonneg_left (norm_nonneg z) (by positivity)
  nlinarith

lemma sum_terms_le (z : ℂ) (hz : 1 / 2 ≤ z.re) (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (hn : M ≤ n) :
    ∑ i ∈ range n, ‖1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1))‖ ≤
      2 * ∑ i ∈ range M, ((i : ℝ) + 1)⁻¹ + ‖z‖ * (1 / (M : ℝ) - 1 / (n : ℝ)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [sub_self, mul_zero, add_zero, mul_sum]
    exact sum_le_sum fun i _ => term_le_two z hz i
  | succ n hn ih =>
    rw [sum_range_succ]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hM hn)
    have ht := term_le_sq z hz n
    have htel : ‖z‖ / ((n : ℝ) + 1) ^ 2 ≤ ‖z‖ * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
      have : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) = ((n : ℝ) * ((n : ℝ) + 1))⁻¹ := by
        field_simp
        ring
      rw [this]
      apply inv_anti₀ (by positivity)
      nlinarith
    push_cast
    nlinarith [ih, ht, htel]

lemma harmonic_cast (n : ℕ) : ((harmonic n : ℚ) : ℝ) = ∑ i ∈ range n, ((i : ℝ) + 1)⁻¹ := by
  simp [harmonic]

lemma partial_le (z : ℂ) (hz : 1 / 2 ≤ z.re) (M : ℕ) (hM : 1 ≤ M) (hzM : ‖z‖ ≤ M)
    (n : ℕ) (hn : M ≤ n) :
    ‖((Real.log n : ℝ) : ℂ) - ∑ k ∈ range (n + 1), 1 / (z + (k : ℂ))‖ ≤
      6 + 2 * Real.log M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hn1 : 1 ≤ n := hM.trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set H : ℝ := ∑ i ∈ range n, ((i : ℝ) + 1)⁻¹ with hH
  have hlow : Real.log n ≤ H := by
    have h := log_add_one_le_harmonic n
    rw [harmonic_cast] at h
    have h2 : Real.log n ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log hn0 (by linarith)
    push_cast at h
    linarith
  have hup : H ≤ 1 + Real.log n := by
    have h := harmonic_le_one_add_log n
    rw [harmonic_cast] at h
    exact h
  have hHc : ((H : ℝ) : ℂ) = ∑ i ∈ range n, 1 / ((i : ℂ) + 1) := by
    rw [hH]
    push_cast
    simp
  have hdecomp : ((Real.log n : ℝ) : ℂ) - ∑ k ∈ range (n + 1), 1 / (z + (k : ℂ)) =
      ((Real.log n - H : ℝ) : ℂ) +
        ∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1))) - 1 / z := by
    rw [sum_range_succ', sum_sub_distrib, ← hHc]
    push_cast
    simp only [add_zero]
    ring
  have h1 : ‖((Real.log n - H : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h2 : ‖∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1)))‖ ≤
      2 * (1 + Real.log M) + 1 := by
    refine (norm_sum_le _ _).trans ((sum_terms_le z hz M hM n hn).trans ?_)
    have hHM := harmonic_le_one_add_log M
    rw [harmonic_cast] at hHM
    have h3 : ‖z‖ * (1 / (M : ℝ) - 1 / (n : ℝ)) ≤ 1 := by
      have h4 : ‖z‖ * (1 / (M : ℝ)) ≤ 1 := by
        rw [mul_one_div]
        exact (div_le_one hM0).2 hzM
      have h5 : 0 ≤ ‖z‖ * (1 / (n : ℝ)) := by positivity
      rw [mul_sub]
      linarith
    linarith
  have h3 : ‖1 / z‖ ≤ 2 := by
    have hzn : 1 / 2 ≤ ‖z‖ := hz.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z))
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]
    linarith
  rw [hdecomp]
  calc _ ≤ ‖((Real.log n - H : ℝ) : ℂ) +
        ∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1)))‖ + ‖1 / z‖ := norm_sub_le _ _
    _ ≤ ‖((Real.log n - H : ℝ) : ℂ)‖ +
        ‖∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1)))‖ + ‖1 / z‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ 6 + 2 * Real.log M := by linarith

theorem digamma_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2) := by
  refine ⟨11, by norm_num, fun z hz => ?_⟩
  have hzn : 1 / 2 ≤ ‖z‖ := hz.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z))
  set M : ℕ := ⌈‖z‖⌉₊ + 1 with hMdef
  have hM : 1 ≤ M := by omega
  have hzM : ‖z‖ ≤ M := by
    rw [hMdef]
    push_cast
    linarith [Nat.le_ceil ‖z‖]
  have hMle : (M : ℝ) ≤ ‖z‖ + 2 := by
    rw [hMdef]
    push_cast
    linarith [Nat.ceil_lt_add_one (norm_nonneg z)]
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hlogM : Real.log M ≤ Real.log (‖z‖ + 2) := Real.log_le_log hM0 hMle
  have hlim := (GlobalTheory.CompanionTheory.DigammaLimit.tendsto_log_sub_sum_digamma z (by linarith)).norm
  have hbd : ‖Complex.digamma z‖ ≤ 6 + 2 * Real.log M :=
    le_of_tendsto hlim ((Filter.eventually_ge_atTop M).mono fun n hn =>
      partial_le z hz M hM hzM n hn)
  have hL : (2 : ℝ) / 3 ≤ Real.log (‖z‖ + 2) := by
    have h2 : Real.log 2 ≤ Real.log (‖z‖ + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  linarith

end GlobalTheory.CompanionTheory.DigammaBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DirichletLogDerivReflectionFormulaStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dirichlet_logDeriv_reflection_formula : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 1 < N → χ.IsPrimitive → ∀ a : ℂ, (χ.Even ∧ a = 0 ∨ χ.Odd ∧ a = 1) → ∀ s : ℂ, (∀ n : ℕ, (s + a) / 2 ≠ -(n : ℂ)) → (∀ n : ℕ, (1 - s + a) / 2 ≠ -(n : ℂ)) → DirichletCharacter.LFunction χ s ≠ 0 → DirichletCharacter.LFunction χ⁻¹ (1 - s) ≠ 0 → deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s = -((Real.log (N / Real.pi) : ℝ) : ℂ) - Complex.digamma ((1 - s + a) / 2) / 2 - Complex.digamma ((s + a) / 2) / 2 - deriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) / DirichletCharacter.LFunction χ⁻¹ (1 - s) := by
  first | exact @GlobalTheory.CompanionTheory.ExplChi.logDeriv_LFunction_functional_equation | exact GlobalTheory.CompanionTheory.ExplChi.logDeriv_LFunction_functional_equation | (intros; apply GlobalTheory.CompanionTheory.ExplChi.logDeriv_LFunction_functional_equation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfCompactCoerciveStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_of_isCompactOperator_coercive : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H), IsCompactOperator A → ∀ (S : Submodule ℂ H) (c : ℝ), 0 < c → (∀ u ∈ S, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) → FiniteDimensional ℂ S := by
  first | exact @GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive | exact GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive | (intros; apply GlobalTheory.CompanionTheory.Glob.finiteDimensional_of_compact_coercive <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeneralLinearIntegralCompactOpen
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.QLTop

open ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem nonarchimedeanLocalField_secondCountable_t2Space (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k ∧ T2Space k := by
  let := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  exact ⟨secondCountable_of_proper, inferInstance⟩

theorem isOpen_isCompact_integers : IsOpen ((𝒪[F] : Subring F) : Set F) ∧ IsCompact ((𝒪[F] : Subring F) : Set F) := by
  refine ⟨?_, ?_⟩
  · exact Valuation.isOpen_valuationSubring (valuation F)
  · exact isCompact_iff_compactSpace.2 (inferInstance : CompactSpace 𝒪[F])

def intSet (O : Subring F) (n : ℕ) : Set (Matrix (Fin n) (Fin n) F) := {M | IsInt O M}

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem isOpen_intSet {O : Subring F} (hO : IsOpen (O : Set F)) (n : ℕ) : IsOpen (intSet O n) := by
  have : intSet O n = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) F => M i j) ⁻¹' (O : Set F) := by
    ext M; simp [intSet, IsInt]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hO.preimage ((continuous_apply j).comp (continuous_apply i))

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem isCompact_intSet {O : Subring F} (hO : IsCompact (O : Set F)) (n : ℕ) : IsCompact (intSet O n) := by
  have : intSet O n = Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => (O : Set F) := by
    ext M
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem GLint_eq_preimage (O : Subring F) (n : ℕ) :
    (GLint O n : Set (GL (Fin n) F)) =
      Units.embedProduct (Matrix (Fin n) (Fin n) F) ⁻¹' (intSet O n ×ˢ (MulOpposite.op '' intSet O n)) := by
  ext g
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, ⟨_, h2, rfl⟩⟩
  · rintro ⟨h1, ⟨y, hy, he⟩⟩
    have hy' : y = ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := MulOpposite.op_injective he
    exact ⟨h1, hy' ▸ hy⟩

theorem gl_topology : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n : ℕ,
    IsOpen (GLint O n : Set (GL (Fin n) F)) ∧ IsCompact (GLint O n : Set (GL (Fin n) F)) ∧
    LocallyCompactSpace (GL (Fin n) F) ∧ SecondCountableTopology (GL (Fin n) F) ∧ T2Space (GL (Fin n) F) ∧
    IsOpen (Mint O n) ∧ IsClosed (Mint O n) := by
  intro F _ _ _ _ O ϖ nrm q h n
  obtain ⟨hsc, ht2⟩ := nonarchimedeanLocalField_secondCountable_t2Space F
  obtain ⟨hOo, hOc⟩ : IsOpen (O : Set F) ∧ IsCompact (O : Set F) := by
    rw [h.O_eq]; exact isOpen_isCompact_integers
  have : T2Space (Matrix (Fin n) (Fin n) F) := inferInstanceAs (T2Space (Fin n → Fin n → F))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) F)).symm.isEmbedding.secondCountableTopology
  have hSo := isOpen_intSet hOo n
  have hSc := isCompact_intSet hOc n
  have hemb := Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)
  have hMint : Mint O n = Units.val ⁻¹' intSet O n := rfl
  refine ⟨?_, ?_, hemb.locallyCompactSpace, hemb.isEmbedding.secondCountableTopology, inferInstance, ?_, ?_⟩
  · rw [GLint_eq_preimage]
    exact (hSo.prod (MulOpposite.opHomeomorph.isOpenMap _ hSo)).preimage hemb.continuous
  · rw [GLint_eq_preimage]
    exact hemb.isCompact_preimage (hSc.prod (hSc.image MulOpposite.continuous_op))
  · rw [hMint]; exact hSo.preimage Units.continuous_val
  · rw [hMint]; exact hSc.isClosed.preimage Units.continuous_val

end GlobalTheory.CompanionTheory.QLTop
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IwasawaDecompositionUpperTriangular
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.Iwasawa

theorem map_mem_GLint {F : Type} [Field F] [ValuativeRel F] {n : ℕ}
    (k : GL (Fin n) (ValuativeRel.valuation F).valuationSubring) :
    GeneralLinearGroup.map (algebraMap (ValuativeRel.valuation F).valuationSubring F) k ∈
      GLint 𝒪[F] n := by
  have key : ∀ (u : GL (Fin n) (ValuativeRel.valuation F).valuationSubring),
      IsInt 𝒪[F] ((GeneralLinearGroup.map
        (algebraMap (ValuativeRel.valuation F).valuationSubring F) u : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) := by
    intro u i j
    have h := (u.1 i j).2
    exact h
  refine ⟨key k, ?_⟩
  rw [← map_inv]
  exact key k⁻¹

theorem exists_upper_mul_int {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
    (h : LF O ϖ nrm q) (n : ℕ) (g : GL (Fin n) F) :
    ∃ b : GL (Fin n) F, (b : Matrix (Fin n) (Fin n) F).BlockTriangular id ∧
      ∃ k ∈ GLint O n, g = b * k := by
  obtain rfl := h.O_eq
  obtain ⟨k, b, hb, hg⟩ :=
    GlobalTheory.ValIwasawa.iwasawa (ValuativeRel.valuation F).valuationSubring F n g⁻¹
  refine ⟨b⁻¹, ?_, _, (GLint _ n).inv_mem (map_mem_GLint k), ?_⟩
  · let _ : Invertible (b : Matrix (Fin n) (Fin n) F) := Units.invertible b
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  · rw [← _root_.mul_inv_rev, ← hg, inv_inv]

end GlobalTheory.CompanionTheory.QL.Iwasawa
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemConjSub
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.QIndex

variable {F : Type} [Field F]

def Lvl {n : ℕ} (O : Subring F) (c : F) (X : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ a b, ∃ o ∈ O, X a b = c * o

theorem Lvl.add {n : ℕ} {O : Subring F} {c : F} {X Y : Matrix (Fin n) (Fin n) F} (hX : Lvl O c X)
    (hY : Lvl O c Y) : Lvl O c (X + Y) := fun a b => by
  obtain ⟨o, ho, h⟩ := hX a b
  obtain ⟨o', ho', h'⟩ := hY a b
  exact ⟨o + o', O.add_mem ho ho', by simp [h, h', mul_add]⟩

theorem Lvl.neg {n : ℕ} {O : Subring F} {c : F} {X : Matrix (Fin n) (Fin n) F} (hX : Lvl O c X) :
    Lvl O c (-X) := fun a b => by
  obtain ⟨o, ho, h⟩ := hX a b
  exact ⟨-o, O.neg_mem ho, by simp [h]⟩

theorem Lvl.int_mul {n : ℕ} {O : Subring F} {c : F} {X Y : Matrix (Fin n) (Fin n) F}
    (hY : IsInt O Y) (hX : Lvl O c X) : Lvl O c (Y * X) := fun a b => by
  choose f hf hf' using hX
  refine ⟨∑ k, Y a k * f k b, O.sum_mem fun k _ => O.mul_mem (hY a k) (hf k b), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [hf' k b]; ring

def congGL (O : Subring F) (c : F) (n : ℕ) : Subgroup (GL (Fin n) F) where
  carrier := {g | g ∈ GLint O n ∧ Lvl O c ((g : Matrix (Fin n) (Fin n) F) - 1)}
  one_mem' := ⟨(GLint O n).one_mem, fun a b => ⟨0, O.zero_mem, by simp⟩⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨(GLint O n).mul_mem hx hy, ?_⟩
    have : ((x * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 =
        (x : Matrix (Fin n) (Fin n) F) * ((y : Matrix (Fin n) (Fin n) F) - 1) +
          ((x : Matrix (Fin n) (Fin n) F) - 1) := by
      simp [Matrix.mul_sub]
    rw [this]
    exact (Lvl.int_mul hx.1 hy').add hx'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨(GLint O n).inv_mem hx, ?_⟩
    have : ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 =
        -(((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          ((x : Matrix (Fin n) (Fin n) F) - 1)) := by
      rw [Matrix.mul_sub, ← Units.val_mul]
      simp
    rw [this]
    exact (Lvl.int_mul hx.2 hx').neg

def boxAdd (O : Subring F) {n : ℕ} (β : Fin n → ℕ) (c : Fin n → Fin n → F) :
    AddSubgroup (Matrix (Fin n) (Fin n) F) where
  carrier := {x | x.BlockTriangular β ∧ ∀ a b, ∃ o ∈ O, x a b = c a b * o}
  zero_mem' := ⟨fun _ _ _ => rfl, fun a b => ⟨0, O.zero_mem, by simp⟩⟩
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨fun i j h => by simp [hx h, hy h], fun a b => ?_⟩
    obtain ⟨o, ho, h⟩ := hx' a b
    obtain ⟨o', ho', h'⟩ := hy' a b
    exact ⟨o + o', O.add_mem ho ho', by simp [h, h', mul_add]⟩
  neg_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨fun i j h => by simp [hx h], fun a b => ?_⟩
    obtain ⟨o, ho, h⟩ := hx' a b
    exact ⟨-o, O.neg_mem ho, by simp [h]⟩

def conjSub {G : Type} [Group G] (H : Subgroup G) (d : G) : Subgroup G :=
  H.map (MulAut.conj d⁻¹).toMonoidHom

theorem mem_conjSub {G : Type} [Group G] (H : Subgroup G) (d p : G) :
    p ∈ conjSub H d ↔ d * p * d⁻¹ ∈ H := by
  simp only [conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [mul_assoc] using hh
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

def lev (ϖ : F) (T : ℕ) {n : ℕ} (dd : Fin n → F) : Fin n → Fin n → F :=
  fun a b => ϖ ^ (2 * T) * ((dd a)⁻¹ * dd b)

end GlobalTheory.CompanionTheory.QL.QIndex
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.NearIdentityMatrixPositiveSolutionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.near_identity_matrix_positive_solution : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (M : ℝ), ∃ ε : ℝ, 0 < ε ∧ ∀ W : κ → κ → ℝ, (∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) →
    (∀ c : κ → ℝ, (∀ σ, ∑ i, W σ i * c i = 0) → c = 0) ∧
    ∀ c : κ → ℝ, (∀ σ, 0 < ∑ i, W σ i * c i) → (∀ σ τ, ∑ i, W σ i * c i ≤ M * ∑ i, W τ i * c i) → ∀ i, 0 < c i := by
  first | exact @GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos | exact GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos | (intros; apply GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos <;> assumption)
end

