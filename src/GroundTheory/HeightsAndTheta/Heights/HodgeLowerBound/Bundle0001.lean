import Mathlib

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LoewnerDetBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem add_mul_eigenvalue_nonneg {M : Matrix n n ℂ} (hM : M.IsHermitian) {a b : ℝ}
    (h : ((a : ℂ) • (1 : Matrix n n ℂ) + (b : ℂ) • M).PosSemidef) (i : n) :
    0 ≤ a + b * hM.eigenvalues i := by
  set v : n → ℂ := ⇑(hM.eigenvectorBasis i) with hv
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 := hM.eigenvectorBasis.orthonormal.ne_zero i
    apply h1
    ext j
    simpa [hv] using congrFun h0 j
  have hMv : M *ᵥ v = (hM.eigenvalues i : ℂ) • v := hM.mulVec_eigenvectorBasis i
  have h0 := h.dotProduct_mulVec_nonneg v
  rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hMv, smul_smul, ← add_smul,
    dotProduct_smul, smul_eq_mul] at h0
  have hs : 0 < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.mpr hv0
  have hx : ((a : ℂ) + (b : ℂ) * (hM.eigenvalues i : ℂ)) = ((a + b * hM.eigenvalues i : ℝ) : ℂ) := by
    push_cast; ring
  rw [hx] at h0
  have h2 := (Complex.nonneg_iff.mp h0).1
  rw [Complex.re_ofReal_mul] at h2
  exact (mul_nonneg_iff_of_pos_right (Complex.pos_iff.mp hs).1).mp h2

theorem norm_det_le_of_loewner {H A : Matrix n n ℂ} {c : ℝ} (hc : 0 < c)
    (h₁ : ((c : ℂ) • A - H).PosSemidef) (h₂ : ((c : ℂ) • A + H).PosSemidef) :
    0 ≤ A.det.re ∧ A.det.im = 0 ∧ ‖H.det‖ ≤ c ^ Fintype.card n * A.det.re := by
  have hA : A.PosSemidef := by
    have e : A = ((1 / (2 * c) : ℝ) : ℂ) • (((c : ℂ) • A + H) + ((c : ℂ) • A - H)) := by
      rw [show ((c : ℂ) • A + H) + ((c : ℂ) • A - H) = ((2 * c : ℝ) : ℂ) • A by
        push_cast; rw [mul_smul, two_smul]; abel, smul_smul, ← Complex.ofReal_mul,
        one_div_mul_cancel (by positivity), Complex.ofReal_one, one_smul]
    rw [e]
    exact (h₂.add h₁).smul (Complex.zero_le_real.mpr (by positivity))
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hA.det_nonneg
  refine ⟨hre, him.symm, ?_⟩
  by_cases h0 : A.det = 0
  · obtain ⟨v, hv0, hAv⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have e1 : star v ⬝ᵥ (((c : ℂ) • A - H) *ᵥ v) = -(star v ⬝ᵥ (H *ᵥ v)) := by
      rw [sub_mulVec, smul_mulVec, hAv, smul_zero, zero_sub, dotProduct_neg]
    have e2 : star v ⬝ᵥ (((c : ℂ) • A + H) *ᵥ v) = star v ⬝ᵥ (H *ᵥ v) := by
      rw [add_mulVec, smul_mulVec, hAv, smul_zero, zero_add]
    have p1 := h₁.dotProduct_mulVec_nonneg v
    have p2 := h₂.dotProduct_mulVec_nonneg v
    rw [e1] at p1
    rw [e2] at p2
    have hz : star v ⬝ᵥ (H *ᵥ v) = 0 := le_antisymm (neg_nonneg.mp p1) p2
    have hw := (h₁.dotProduct_mulVec_zero_iff v).mp (by rw [e1, hz, neg_zero])
    rw [sub_mulVec, smul_mulVec, hAv, smul_zero, zero_sub, neg_eq_zero] at hw
    rw [exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hw⟩, norm_zero]
    exact mul_nonneg (pow_nonneg hc.le _) hre
  · obtain ⟨L, hL⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
    rw [star_eq_conjTranspose] at hL
    have hLu : IsUnit L.det := isUnit_iff_ne_zero.mpr fun hl => h0 (by rw [hL, det_mul, hl, mul_zero])
    have hLHu : IsUnit Lᴴ.det := by
      rw [det_conjTranspose]
      exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr (isUnit_iff_ne_zero.mp hLu))
    set M := (L⁻¹)ᴴ * H * L⁻¹ with hMdef
    have hHM : H = Lᴴ * M * L := by
      rw [hMdef, conjTranspose_nonsing_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hLHu, Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hLu,
        Matrix.mul_one]
    have hA1 : (L⁻¹)ᴴ * A * L⁻¹ = 1 := by
      rw [hL, conjTranspose_nonsing_inv, ← Matrix.mul_assoc (Lᴴ)⁻¹ Lᴴ L,
        Matrix.nonsing_inv_mul _ hLHu, Matrix.one_mul, Matrix.mul_nonsing_inv _ hLu]
    have hconj : ∀ s : ℝ, (L⁻¹)ᴴ * ((c : ℂ) • A + (s : ℂ) • H) * L⁻¹ = (c : ℂ) • 1 + (s : ℂ) • M := by
      intro s
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        hA1, hMdef]
    have hP : ∀ s : ℝ, s = 1 ∨ s = -1 → ((c : ℂ) • (1 : Matrix n n ℂ) + (s : ℂ) • M).PosSemidef := by
      rintro s (rfl | rfl)
      · rw [← hconj]
        simpa using h₂.conjTranspose_mul_mul_same L⁻¹
      · rw [← hconj]
        have e : (c : ℂ) • A + ((-1 : ℝ) : ℂ) • H = (c : ℂ) • A - H := by
          push_cast; rw [neg_one_smul, ← sub_eq_add_neg]
        rw [e]
        exact h₁.conjTranspose_mul_mul_same L⁻¹
    have hM : M.IsHermitian := by
      have h3 := (hP 1 (Or.inl rfl)).isHermitian
      rw [IsHermitian, conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_one] at h3
      simp only [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_one, map_one, one_smul] at h3
      exact add_left_cancel h3
    have hb : ∀ i, |hM.eigenvalues i| ≤ c := fun i => by
      have u := add_mul_eigenvalue_nonneg hM (hP 1 (Or.inl rfl)) i
      have l := add_mul_eigenvalue_nonneg hM (hP (-1) (Or.inr rfl)) i
      rw [abs_le]
      constructor <;> linarith
    have hdA : A.det = Lᴴ.det * L.det := by rw [hL, det_mul]
    have hnA : ‖A.det‖ = A.det.re := by
      rw [← Complex.re_add_im A.det, ← him]
      simp [Complex.norm_real, abs_of_nonneg hre]
    have hdH : ‖H.det‖ = ‖M.det‖ * ‖A.det‖ := by
      rw [hHM, det_mul, det_mul, hdA]
      simp only [norm_mul]
      ring
    have hdM : ‖M.det‖ ≤ c ^ Fintype.card n := by
      rw [hM.det_eq_prod_eigenvalues, norm_prod]
      refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_).trans_eq
        (by rw [Finset.prod_const, Finset.card_univ] : ∏ _i : n, c = c ^ Fintype.card n)
      have := hb i
      rwa [RCLike.norm_ofReal]
    rw [hdH, ← hnA]
    exact mul_le_mul_of_nonneg_right hdM (norm_nonneg _)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagIntMuOneDet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace FlagIntMuOne

open Matrix Finset

def invFactMat (j m : ℕ) : Matrix (Fin m) (Fin m) ℚ :=
  Matrix.of fun r k => if (k : ℕ) ≤ j + r then (((j + r - k : ℕ).factorial : ℚ))⁻¹ else 0

theorem det_vandermonde_shift (j m : ℕ) :
    (vandermonde fun r : Fin m => ((j + r : ℕ) : ℚ)).det = ∏ i : Fin m, ((i : ℕ).factorial : ℚ) := by
  have h : (fun r : Fin m => ((j + r : ℕ) : ℚ)) = fun r : Fin m => ((r : ℕ) : ℚ) + j := by
    ext r; push_cast; ring
  rw [h, det_vandermonde_add]
  cases m with
  | zero => simp
  | succ n =>
    rw [det_vandermonde_id_eq_superFactorial, ← Nat.prod_range_factorial_succ,
      Fin.prod_univ_eq_prod_range (fun i => ((i.factorial : ℕ) : ℚ)) (n + 1), prod_range_succ']
    push_cast
    simp

theorem det_invFactMat (j m : ℕ) :
    (invFactMat j m).det = ∏ i : Fin m, ((i : ℕ).factorial : ℚ) / ((j + i : ℕ).factorial : ℚ) := by
  have hB : (Matrix.of fun r k : Fin m => ((j + r : ℕ).factorial : ℚ) * invFactMat j m r k) =
      Matrix.of fun r k : Fin m => (descPochhammer ℚ k).eval (((j + r : ℕ) : ℚ)) := by
    ext r k
    simp only [invFactMat, Matrix.of_apply, descPochhammer_eval_eq_descFactorial]
    split_ifs with h
    · rw [← Nat.factorial_mul_descFactorial h]
      push_cast
      have : ((j + r - k : ℕ).factorial : ℚ) ≠ 0 := by positivity
      field_simp
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
      simp
  have hV := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun r : Fin m => ((j + r : ℕ) : ℚ)) (fun k => descPochhammer ℚ (k : ℕ))
    (fun k => descPochhammer_natDegree ℚ k) (fun k => monic_descPochhammer ℚ k)
  rw [← hB, det_mul_column, det_vandermonde_shift] at hV
  have hP : (∏ i : Fin m, ((j + i : ℕ).factorial : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => by positivity
  rw [prod_div_distrib, eq_div_iff hP, hV, mul_comm]

theorem prod_factorial_div_comm (j m : ℕ) :
    ∏ i : Fin m, ((i : ℕ).factorial : ℚ) / ((j + i : ℕ).factorial : ℚ) =
      ∏ i : Fin j, ((i : ℕ).factorial : ℚ) / ((m + i : ℕ).factorial : ℚ) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => ((i.factorial : ℕ) : ℚ) / ((j + i : ℕ).factorial : ℚ)) m,
    Fin.prod_univ_eq_prod_range (fun i => ((i.factorial : ℕ) : ℚ) / ((m + i : ℕ).factorial : ℚ)) j,
    prod_div_distrib, prod_div_distrib,
    div_eq_div_iff (prod_ne_zero_iff.mpr fun i _ => by positivity)
      (prod_ne_zero_iff.mpr fun i _ => by positivity)]
  have h1 := prod_range_add (fun i => ((i.factorial : ℕ) : ℚ)) m j
  have h2 := prod_range_add (fun i => ((i.factorial : ℕ) : ℚ)) j m
  rw [Nat.add_comm m j] at h1
  rw [← h1.symm.trans h2]

def flagMat (j m : ℕ) : Matrix (Fin (j + m)) (Fin (j + m)) ℚ :=
  Matrix.of fun i k =>
    if (i : ℕ) < j then (if (k : ℕ) = m + i then 1 else 0)
    else (if (k : ℕ) ≤ i then (((i - k : ℕ).factorial : ℚ))⁻¹ else 0)

def blockSwap (j m : ℕ) : Equiv.Perm (Fin (j + m)) := finAddFlip.trans (finCongr (Nat.add_comm m j))

theorem blockSwap_castAdd (j m : ℕ) (i : Fin j) : ((blockSwap j m (Fin.castAdd m i) : Fin (j + m)) : ℕ) = m + i := by
  simp [blockSwap]
  omega

theorem blockSwap_natAdd (j m : ℕ) (r : Fin m) : ((blockSwap j m (Fin.natAdd j r) : Fin (j + m)) : ℕ) = r := by
  simp [blockSwap]

theorem finRotate_pow_val (n k : ℕ) (x : Fin n) : (((finRotate n) ^ k) x : ℕ) = ((x : ℕ) + k) % n := by
  cases n with
  | zero => exact x.elim0
  | succ n =>
    induction k with
    | zero => simp [Nat.mod_eq_of_lt x.isLt]
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.val_add, ih, Fin.val_one',
        ← Nat.add_mod, Nat.add_assoc]

theorem blockSwap_eq_pow (j m : ℕ) : blockSwap j m = (finRotate (j + m)) ^ m := by
  ext x
  rw [finRotate_pow_val]
  induction x using Fin.addCases with
  | left i =>
    rw [blockSwap_castAdd, Fin.val_castAdd, Nat.mod_eq_of_lt (by omega), Nat.add_comm]
  | right r =>
    rw [blockSwap_natAdd, Fin.val_natAdd, show j + (r : ℕ) + m = r + (j + m) by ring, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

theorem sign_blockSwap (j m : ℕ) : Equiv.Perm.sign (blockSwap j m) = (-1) ^ (j * m) := by
  rw [blockSwap_eq_pow, map_pow, sign_finRotate, ← pow_mul]
  have h : (j + m - 1) * m = j * m + (m * (m - 1)) := by
    cases m with
    | zero => simp
    | succ n => rw [show j + (n + 1) - 1 = j + n by omega, Nat.add_sub_cancel]; ring
  rw [h, pow_add, (Nat.even_mul_pred_self m).neg_one_pow, mul_one]

theorem det_flagMat (j m : ℕ) :
    (flagMat j m).det = (-1) ^ (j * m) * ∏ i : Fin m, ((i : ℕ).factorial : ℚ) / ((j + i : ℕ).factorial : ℚ) := by
  have h1 := det_permute' (blockSwap j m) (flagMat j m)
  have h2 : ((flagMat j m).submatrix id (blockSwap j m)).det = (invFactMat j m).det := by
    rw [← det_submatrix_equiv_self finSumFinEquiv]
    have : ((flagMat j m).submatrix id (blockSwap j m)).submatrix finSumFinEquiv finSumFinEquiv =
        fromBlocks 1 0 (Matrix.of fun r k => flagMat j m (Fin.natAdd j r) (blockSwap j m (Fin.castAdd m k)))
          (invFactMat j m) := by
      ext (i | r) (k | r')
      · simp only [submatrix_apply, id, finSumFinEquiv_apply_left, fromBlocks_apply₁₁, flagMat, of_apply,
          Fin.val_castAdd, blockSwap_castAdd, Matrix.one_apply, Fin.ext_iff]
        rw [if_pos i.isLt]
        by_cases h : (i : ℕ) = k
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h]
      · simp only [submatrix_apply, id, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          fromBlocks_apply₁₂, flagMat, of_apply, Fin.val_castAdd, blockSwap_natAdd, Matrix.zero_apply]
        rw [if_pos i.isLt, if_neg (by omega)]
      · simp
      · simp only [submatrix_apply, id, finSumFinEquiv_apply_right, fromBlocks_apply₂₂, flagMat, of_apply,
          Fin.val_natAdd, blockSwap_natAdd, invFactMat]
        rw [if_neg (by omega)]
    rw [this, det_fromBlocks_zero₁₂, det_one, one_mul]
  rw [h2, sign_blockSwap, det_invFactMat] at h1
  push_cast at h1
  have hs : ((-1 : ℚ) ^ (j * m)) * (-1) ^ (j * m) = 1 := by rw [← mul_pow]; simp
  linear_combination (-((-1 : ℚ) ^ (j * m))) * h1 - (flagMat j m).det * hs

end FlagIntMuOne

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHoloInjDerivInj
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

def HoloInjDerivInj.Statement : Prop :=
  ∀ (m : ℕ) (f : (Fin m → ℂ) → (Fin m → ℂ)) (U : Set (Fin m → ℂ)), IsOpen U → AnalyticOnNhd ℂ f U →
    Set.InjOn f U → ∀ u ∈ U, Function.Injective (fderiv ℂ f u)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHookFactorBranch
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

def hookFactor {j : ℕ} (u : Fin j → ℕ) : ℚ :=
  (Matrix.vandermonde fun r => (u r : ℚ)).det / ∏ r, ((u r).factorial : ℚ)

def HookFactorBranch.Statement : Prop :=
  ∀ (j : ℕ) (u : Fin j → ℕ),
    ∑ p, (if 0 < u p ∧ ∀ q, u q ≠ u p - 1 then hookFactor (Function.update u p (u p - 1)) else 0) =
      (∑ r, (u r : ℚ) - ∑ r : Fin j, ((r : ℕ) : ℚ)) * hookFactor u

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsInvDerivDecay
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

def InvDerivDecay.Statement : Prop :=
  ∀ (v G : ℂ → ℝ) (ρ R : ℝ), 0 < ρ → ContDiffOn ℝ 2 G (Metric.ball 0 ρ) →
    (∀ y : ℂ, R < ‖y‖ → v y = G y⁻¹) →
    ∃ C R₀ : ℝ, ∀ y : ℂ, R₀ < ‖y‖ →
      ‖fderiv ℝ v y‖ ≤ C / ‖y‖ ^ 2 ∧ ‖iteratedFDeriv ℝ 2 v y‖ ≤ C / ‖y‖ ^ 3

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLaplacianDecayZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian

def LaplacianDecayZero.Statement : Prop :=
  ∀ (v : ℂ → ℝ) (C R₀ : ℝ), ContDiff ℝ 2 v →
    (∀ y : ℂ, R₀ < ‖y‖ →
      ‖fderiv ℝ v y‖ ≤ C / ‖y‖ ^ 2 ∧ ‖iteratedFDeriv ℝ 2 v y‖ ≤ C / ‖y‖ ^ 3) →
    MeasureTheory.Integrable (Δ v) ∧ ∫ y, Δ v y = 0

def LaplacianDecayZero.bump : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLaplacianLogGrowth
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian Real

def LaplacianLogGrowth.Statement : Prop :=
  ∀ (u F : ℂ → ℝ) (a r : ℝ), ContDiff ℝ 2 u → 0 < r → ContDiffOn ℝ 2 F (Metric.ball 0 r) →
    (∀ y : ℂ, r⁻¹ < ‖y‖ → u y = a * Real.log ‖y‖ + F y⁻¹) →
    MeasureTheory.Integrable (Δ u) ∧ ∫ y, Δ u y = 2 * π * a

def fsPotPlane (y : ℂ) : ℝ := Real.log (1 + ‖y‖ ^ 2) / 2

theorem contDiff_fsPotPlane : ContDiff ℝ 2 fsPotPlane := by
  unfold fsPotPlane
  exact ((contDiff_const.add (contDiff_norm_sq ℝ)).log fun y => by positivity).div_const _

theorem fsPotPlane_eq {y : ℂ} (hy : 1⁻¹ < ‖y‖) : fsPotPlane y = 1 * Real.log ‖y‖ + fsPotPlane y⁻¹ := by
  have hy0 : 0 < ‖y‖ := lt_trans (by norm_num) hy
  unfold fsPotPlane
  rw [norm_inv]
  have h1 : 1 + ‖y‖ ^ 2 = ‖y‖ ^ 2 * (1 + ‖y‖⁻¹ ^ 2) := by
    field_simp
    ring
  rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  push_cast
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLevelSetLocalInj
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

def LevelSetLocalInj.Statement : Prop :=
  ∀ (J : Type) [Fintype J] (R : Type) [Fintype R] (f : R → MvPolynomial J ℂ) (w₀ : J → ℂ),
    LinearIndependent ℂ (fun i => fun j => eval w₀ (pderiv j (f i))) →
    ∀ m : ℕ, m + Fintype.card R = Fintype.card J →
      ∃ U : Set (J → ℂ), IsOpen U ∧ w₀ ∈ U ∧ ∃ π : (J → ℂ) →L[ℂ] (Fin m → ℂ),
        Set.InjOn π (U ∩ {w | ∀ i, eval w (f i) = eval w₀ (f i)})

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsVandermondeBranch
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

def VandermondeBranch.Statement : Prop :=
  ∀ (j : ℕ) (v : Fin j → ℚ),
    ∑ a, v a * (Matrix.vandermonde (Function.update v a (v a - 1))).det =
      (∑ a, v a - ∑ a : Fin j, ((a : ℕ) : ℚ)) * (Matrix.vandermonde v).det

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

