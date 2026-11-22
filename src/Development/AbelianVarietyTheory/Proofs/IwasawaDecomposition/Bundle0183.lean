import Mathlib
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.CyclotomicNorms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GChiApproximationSum
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.GoodCharacterSum

theorem gChi_add_sum_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x z : ℝ)
    (hx : 0 ≤ x) (hz : x ≤ z) :
    GlobalTheoryTheory.gChi χ x + ∑ n ∈ Icc 1 ⌊z⌋₊, (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod q) =
      -((x : ℂ) * (-GlobalTheoryTheory.logDerivativeAtOne χ -
        ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ))) := by
  have h1 : GlobalTheoryTheory.sumLamChi χ x = ∑ n ∈ Icc 1 ⌊z⌋₊,
      ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((max (x / n - 1) 0 : ℝ) : ℂ) := by
    unfold GlobalTheoryTheory.sumLamChi
    apply Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.floor_le_floor hz))
    intro n hn hn'
    have h1n : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hlt : ⌊x⌋₊ < n := by
      by_contra h
      exact hn' (Finset.mem_Icc.2 ⟨h1n, not_lt.1 h⟩)
    have hxn : x < n := (Nat.floor_lt hx).1 hlt
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1n
    have : x / n - 1 ≤ 0 := by
      have := (div_le_one hn0).2 hxn.le
      linarith
    rw [max_eq_right this]
    simp
  have h2 : ∀ n ∈ Icc 1 ⌊z⌋₊,
      ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((max (x / n - 1) 0 : ℝ) : ℂ) +
        (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod q) =
      (x : ℂ) * (((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)) := by
    intro n _
    have hm : max (x / n - 1) 0 + min 1 (x / n) = x / n := by
      rcases le_total 1 (x / n) with h | h
      · rw [max_eq_left (by linarith), min_eq_left h]; ring
      · rw [max_eq_right (by linarith), min_eq_right h]; ring
    have hm' : ((max (x / n - 1) 0 : ℝ) : ℂ) + ((min 1 (x / n) : ℝ) : ℂ) = (x : ℂ) / (n : ℂ) := by
      rw [← Complex.ofReal_add, hm]; push_cast; rfl
    unfold GlobalTheoryTheory.cn
    rw [Complex.ofReal_mul]
    linear_combination (((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) * hm'
  unfold GlobalTheoryTheory.gChi
  rw [if_neg hχ, h1, mul_sub, Finset.mul_sum, ← Finset.sum_congr rfl h2, Finset.sum_add_distrib]
  ring

theorem gChi_add_sum_bound : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x → ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 0 < Q → x ^ (eps / 6) ≤ Real.log Q → Real.log Q ≤ x ^ (eps / 4) → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ → ‖GlobalTheoryTheory.gChi χ x + ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (GlobalTheoryTheory.cn x n : ℂ) * χ (n : ZMod q)‖ ≤ x ^ eps ∧ ‖GlobalTheoryTheory.logDerivativeAtOne χ‖ ≤ C * Real.log x := by
  intro hZ hC hL hN hF eps h0 h1
  obtain ⟨C₁, hC₁, H1⟩ := GlobalTheory.T.psi_chi_power_saving_bound hC hL hN hF hZ
  obtain ⟨C₂, c₂, hC₂, hc₂, H2⟩ := GlobalTheory.T.psi_chi_sqrt_log_bound hC hL hN hF hZ
  obtain ⟨CM, hCM, HM⟩ : ∃ CM : ℝ, 0 ≤ CM ∧ ∀ y : ℝ, 1 ≤ y →
      |∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) - Real.log y| ≤ CM := GlobalTheory.mertens_first_vonMangoldt
  have HS := GlobalTheory.T.log_deriv_series_of_explicit hZ hC hL hN hF
  obtain ⟨x₀, C, HT⟩ := GlobalTheory.GoodCharacterTail.tail_and_sum_bound eps h0 (by linarith)
    (max C₁ C₂) c₂ CM (lt_max_of_lt_left hC₁) hc₂ hCM
  refine ⟨max x₀ (max 1 ((2 : ℝ) ^ (6 / eps))), max C 1, lt_max_of_lt_right one_pos, ?_⟩
  intro x hx Q q _ χ hQ hl hu hχ hg
  have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : (2 : ℝ) ^ (6 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have h2 : (2 : ℝ) ≤ x ^ (eps / 6) := by
    have := Real.rpow_le_rpow (by positivity) hx2 (by positivity : 0 ≤ eps / 6)
    rw [← Real.rpow_mul (by norm_num), show 6 / eps * (eps / 6) = 1 by field_simp, Real.rpow_one] at this
    exact this
  have hQ3 : 3 ≤ Q := by
    have := Real.log_le_sub_one_of_pos hQ
    linarith
  have key := HT x hx0 Q hQ hl hu (fun n => ((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) (-GlobalTheoryTheory.logDerivativeAtOne χ)
    (HS q χ hχ) ?_ ?_ ?_
  · refine ⟨?_, ?_⟩
    · have hz : x ≤ x ^ (400 : ℝ) := by
        have := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 : ℝ) ≤ 400)
        rwa [Real.rpow_one] at this
      rw [gChi_add_sum_eq χ hχ x _ (by linarith) hz, norm_neg]
      exact key.1
    · have := key.2
      rw [norm_neg] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg hx1))
  · intro y hy
    have := (abs_le.1 (HM y hy)).2
    refine le_trans (Finset.sum_le_sum fun n _ => ?_) (by linarith : ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) ≤ _)
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_right vonMangoldt_nonneg (χ.norm_le_one _)
  · intro u hu2
    refine le_trans (H1 Q q χ hQ3 hχ hg u hu2) (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    have : 0 < u := by linarith
    positivity
  · intro u hu2
    have : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hu2
    refine le_trans (H2 Q q χ hQ3 hχ hg u hu2) ?_
    gcongr
    exact le_max_right _ _

end GlobalTheory.GoodCharacterSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianInnerEqInvariantKernel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

theorem kerAlg_exponent {P Q : ℕ} (B : Matrix (Fin P) (Fin Q) ℂ) (C : Matrix (Fin Q) (Fin P) ℂ)
    (h : IsUnit (1 - C * B).det) (a c : Fin P → ℂ) (b d s u : Fin Q → ℂ) :
    -(b ⬝ᵥ s) + -(d ⬝ᵥ u) + (a ⬝ᵥ (1 - B * C)⁻¹ *ᵥ c + d ⬝ᵥ (1 - C * B)⁻¹ *ᵥ b
      + a ⬝ᵥ ((1 - B * C)⁻¹ * B) *ᵥ b + d ⬝ᵥ ((1 - C * B)⁻¹ * C) *ᵥ c) =
    ((a + s ᵥ* C) ⬝ᵥ (c + B *ᵥ u) - s ⬝ᵥ u) -
      (a ᵥ* B + d - s ᵥ* (1 - C * B)) ⬝ᵥ (1 - C * B)⁻¹ *ᵥ (-(b + C *ᵥ c) + (1 - C * B) *ᵥ u) := by
  have h1 := Matrix.nonsing_inv_mul _ h
  have h2 := Matrix.mul_nonsing_inv _ h
  generalize (1 - C * B)⁻¹ = N at h1 h2 ⊢
  have h3 : C * B * N = N - 1 := by rw [← h2, Matrix.sub_mul, Matrix.one_mul, sub_sub_cancel]
  have h4 : N * (C * B) = N - 1 := by rw [← h1, Matrix.mul_sub, Matrix.mul_one, sub_sub_cancel]
  have hM : (1 - B * C)⁻¹ = 1 + B * N * C := by
    apply Matrix.inv_eq_right_inv
    have : B * C * (B * N * C) = B * (C * B * N) * C := by simp only [Matrix.mul_assoc]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, this, h3, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mul_one]
    abel
  have hMB : (1 + B * N * C) * B = B * N := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, h4, Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [hM, hMB]
  have e1 : N *ᵥ (-(b + C *ᵥ c) + (1 - C * B) *ᵥ u) = u - N *ᵥ (b + C *ᵥ c) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_neg]; abel
  have e2 : (s ᵥ* (1 - C * B)) ⬝ᵥ N *ᵥ (b + C *ᵥ c) = s ⬝ᵥ (b + C *ᵥ c) := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [e1, dotProduct_sub, sub_dotProduct _ _ (N *ᵥ _), e2]
  simp only [add_dotProduct, sub_dotProduct, dotProduct_add, ← Matrix.dotProduct_mulVec, Matrix.mulVec_add,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, dotProduct_sub,
    dotProduct_comm b s]
  ring

theorem kerAlg_proj {P Q : ℕ} (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (h : IsUnit Y.toRows₂.det)
    (h' : IsUnit Y'.toRows₂.det) :
    Y' * (Yᴴ * Jm P Q * Y')⁻¹ * Yᴴ * Jm P Q =
      Matrix.fromRows (matA Y') 1 * (1 - (matA Y)ᴴ * matA Y')⁻¹ * Matrix.fromCols (-(matA Y)ᴴ) 1 := by
  have hH : IsUnit (Y.toRows₂ᴴ).det := by rw [Matrix.det_conjTranspose]; exact h.star
  have e0 : Yᴴ * Jm P Q * Y' = (-Y.toRows₂ᴴ) * (1 - (matA Y)ᴴ * matA Y') * Y'.toRows₂ := by
    rw [Matrix.neg_mul, Matrix.neg_mul, ← form_factor Y Y' h h', neg_neg]
  have e1 : Yᴴ * Jm P Q = (-Y.toRows₂ᴴ) * Matrix.fromCols (-(matA Y)ᴴ) 1 := by
    conv_lhs => rw [frame_eq Y h]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, baseY, Jm, Formalism.UG.Jpq,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks, Matrix.neg_mul,
      ← Matrix.mul_neg]
    congr 1
    ext i (j | j) <;> simp
  have hN : IsUnit (-Y.toRows₂ᴴ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det] at hH ⊢; exact hH.neg
  rw [e0, Matrix.mul_assoc _ Yᴴ, e1, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have e2 := frame_eq Y' h'
  generalize matA Y' = B at e2 ⊢
  generalize Y'.toRows₂ = Z at e2 h' ⊢
  subst e2
  simp only [Matrix.mul_assoc, baseY]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ h', Matrix.nonsing_inv_mul_cancel_left _ _ hN]

theorem kerAlg : ∀ (P Q : ℕ) (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (v φ v' φ' : Ix P Q → ℂ), IsUnit Y.toRows₂.det → IsUnit Y'.toRows₂.det → IsUnit (1 - (matA Y)ᴴ * matA Y').det → let A := matA Y; let B := matA Y'; let a : Fin P → ℂ := fun i => star (linX Y v φ (Sum.inl i)); let b : Fin Q → ℂ := fun j => star (linX Y v φ (Sum.inr j)); let c : Fin P → ℂ := fun i => linX Y' v' φ' (Sum.inl i); let d : Fin Q → ℂ := fun j => linX Y' v' φ' (Sum.inr j); let M := (1 - B * Aᴴ)⁻¹; let N := (1 - Aᴴ * B)⁻¹; star (scal Y v φ) * scal Y' v' φ' * (((1 - Aᴴ * B).det)⁻¹ * Complex.exp (a ⬝ᵥ M *ᵥ c + d ⬝ᵥ N *ᵥ b + a ⬝ᵥ (M * B) *ᵥ b + d ⬝ᵥ (N * Aᴴ) *ᵥ c)) = ker Y v φ Y' v' φ' := by
  intro P Q Y Y' v φ v' φ' h h' hK A B a b c d M N
  have hs : star (scal Y v φ) = ((Y.toRows₂ᴴ).det)⁻¹ * Complex.exp (-(b ⬝ᵥ star (v ∘ Sum.inr))) := by
    rw [scal, star_mul', star_inv₀, Matrix.det_conjTranspose, Complex.star_def, ← Complex.exp_conj]
    congr 2
    simp [b, dotProduct]
  have hs' : scal Y' v' φ' = (Y'.toRows₂.det)⁻¹ * Complex.exp (-(d ⬝ᵥ (v' ∘ Sum.inr))) := rfl
  have ha : star (v ∘ Sum.inl) = a + star (v ∘ Sum.inr) ᵥ* Aᴴ := by
    have : a = star (v ∘ Sum.inl - A *ᵥ (v ∘ Sum.inr)) := rfl
    rw [this, star_sub, Matrix.star_mulVec]; abel
  have hb : b = Aᴴ *ᵥ star (φ ∘ Sum.inl) + star (φ ∘ Sum.inr) := by
    have : b = star ((φ ∘ Sum.inl) ᵥ* A + φ ∘ Sum.inr) := rfl
    rw [this, star_add, Matrix.star_vecMul]
  have hc : v' ∘ Sum.inl = c + B *ᵥ (v' ∘ Sum.inr) := by
    have : c = v' ∘ Sum.inl - B *ᵥ (v' ∘ Sum.inr) := rfl
    rw [this]; abel
  have hd : d = (φ' ∘ Sum.inl) ᵥ* B + φ' ∘ Sum.inr := rfl
  have hJ1 : star v ᵥ* Jm P Q = Sum.elim (star (v ∘ Sum.inl)) (-star (v ∘ Sum.inr)) := by
    rw [Jm, Formalism.UG.Jpq, Matrix.vecMul_fromBlocks]
    ext (i | i) <;> simp [Matrix.vecMul_neg]
  have hJ2 : Jm P Q *ᵥ star φ = Sum.elim (star (φ ∘ Sum.inl)) (-star (φ ∘ Sum.inr)) := by
    rw [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_mulVec]
    ext (i | i) <;> simp [Matrix.neg_mulVec]
  have e0 : (star v ᵥ* Jm P Q) ⬝ᵥ v' = (a + star (v ∘ Sum.inr) ᵥ* Aᴴ) ⬝ᵥ (c + B *ᵥ (v' ∘ Sum.inr))
      - star (v ∘ Sum.inr) ⬝ᵥ (v' ∘ Sum.inr) := by
    rw [← ha, ← hc, hJ1]
    simp [dotProduct, Fintype.sum_sum_type, sub_eq_add_neg]
  have e1 : (star v ᵥ* Jm P Q + φ') ᵥ* Matrix.fromRows B 1 =
      a ᵥ* B + d - star (v ∘ Sum.inr) ᵥ* (1 - Aᴴ * B) := by
    have : star v ᵥ* Jm P Q + φ' = Sum.elim (star (v ∘ Sum.inl) + φ' ∘ Sum.inl)
        (-star (v ∘ Sum.inr) + φ' ∘ Sum.inr) := by
      rw [hJ1]; ext (i | i) <;> rfl
    rw [this, Matrix.sumElim_vecMul_fromRows, ha, hd]
    simp only [Matrix.add_vecMul, Matrix.vecMul_one, Matrix.vecMul_sub, Matrix.vecMul_vecMul]
    abel
  have e2 : Matrix.fromCols (-Aᴴ) 1 *ᵥ (Jm P Q *ᵥ star φ + v') =
      -(b + Aᴴ *ᵥ c) + (1 - Aᴴ * B) *ᵥ (v' ∘ Sum.inr) := by
    have : Jm P Q *ᵥ star φ + v' = Sum.elim (star (φ ∘ Sum.inl) + v' ∘ Sum.inl)
        (-star (φ ∘ Sum.inr) + v' ∘ Sum.inr) := by
      rw [hJ2]; ext (i | i) <;> rfl
    rw [this, Matrix.fromCols_mulVec_sumElim, hb]
    conv_lhs => rw [hc]
    simp only [Matrix.mulVec_add, Matrix.one_mulVec, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.neg_mulVec,
      Matrix.neg_mul]
    abel
  have key := kerAlg_exponent B Aᴴ hK a c b d (star (v ∘ Sum.inr)) (v' ∘ Sum.inr)
  rw [ker, kerAlg_proj Y Y' h h', form_factor Y Y' h h', ← Matrix.mulVec_mulVec _ (Matrix.fromRows _ _ * _),
    ← Matrix.mulVec_mulVec _ (Matrix.fromRows _ _), Matrix.dotProduct_mulVec _ (Matrix.fromRows _ _), e0, e1, e2,
    ← key, hs, hs', Complex.exp_add (-_ + -_), Complex.exp_add (-_) (-_), Matrix.det_mul, Matrix.det_mul]
  simp only [mul_inv, M, N, A, B]
  ring

end GlobalTheory.OscGauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtOfWeakDerivOnInvariantTotalSet
section
namespace GlobalTheory.Mem.Osc

theorem hasDerivAt_of_weak_on_invariant_total
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : ℝ → H →L[ℂ] H) (D : Set H) (x w : H) (h0 : U 0 = 1)
    (hadd : ∀ s t, U (s + t) = U s * U t) (hn : ∀ t y, ‖U t y‖ = ‖y‖)
    (hc : ∀ y, Continuous fun t => U t y) (hD : Dense (Submodule.span ℂ D : Set H))
    (hinv : ∀ t, ∀ y ∈ D, U t y ∈ D)
    (hw : ∀ y ∈ D, HasDerivAt (fun t : ℝ => inner ℂ (U t x) y) (inner ℂ w y) 0) :
    HasDerivAt (fun t : ℝ => U t x) w 0 := by
  have hiso : ∀ t a b, inner ℂ (U t a) (U t b) = inner ℂ a b := fun t a b =>
    (⟨(U t).toLinearMap, hn t⟩ : H →ₗᵢ[ℂ] H).inner_map_map a b
  have hadj : ∀ t a y, inner ℂ (U t a) y = inner ℂ a (U (-t) y) := by
    intro t a y
    have : U t (U (-t) y) = y := by
      have := congrArg (fun A : H →L[ℂ] H => A y) (hadd t (-t))
      simpa [h0] using this.symm
    rw [← hiso t a (U (-t) y), this]
  have hI : ∀ t : ℝ, HasDerivAt (fun u : ℝ => ∫ s in (0:ℝ)..u, U s w) (U t w) t := fun t =>
    ((hc w).integral_hasStrictDerivAt 0 t).hasDerivAt
  have hall : ∀ y ∈ D, ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => inner ℂ (U u x) y) (inner ℂ (U t w) y) t := by
    intro y hy t
    have h1 := hw _ (hinv (-t) y hy)
    rw [← hadj] at h1
    have h2 : HasDerivAt (fun u : ℝ => inner ℂ (U u x) (U (-t) y)) (inner ℂ (U t w) y) (t - t) := by
      simpa using h1
    have h3 := h2.comp_sub_const t t
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    have h4 : U u x = U t (U (u - t) x) := by
      have := congrArg (fun A : H →L[ℂ] H => A x) (hadd t (u - t))
      simpa using this
    simp only
    rw [← hadj, ← h4]
  have hz : ∀ y ∈ D, ∀ t : ℝ, inner ℂ (U t x - x - ∫ s in (0:ℝ)..t, U s w) y = 0 := by
    intro y hy t
    have hd : ∀ u : ℝ, HasDerivAt
        (fun u : ℝ => inner ℂ (U u x) y - inner ℂ (∫ s in (0:ℝ)..u, U s w) y) (0:ℂ) u := by
      intro u
      have h5 := (hI u).inner ℂ (hasDerivAt_const u y)
      have h6 := (hall y hy u).sub h5
      simp only [inner_zero_right, zero_add, sub_self] at h6
      exact h6
    have h7 := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
      (fun u => (hd u).deriv) t 0
    simp only [h0, intervalIntegral.integral_same, inner_zero_left, sub_zero,
      one_apply_eq_self] at h7
    rw [inner_sub_left, inner_sub_left, ← h7]
    ring
  have hF : ∀ t : ℝ, U t x = x + ∫ s in (0:ℝ)..t, U s w := by
    intro t
    have h8 : U t x - x - ∫ s in (0:ℝ)..t, U s w = 0 := by
      refine hD.eq_zero_of_inner_left (𝕜 := ℂ) ?_
      intro v hv
      induction hv using Submodule.span_induction with
      | mem y hy => exact hz y hy t
      | zero => simp
      | add a b _ _ ha hb => simp only [inner_add_right] at *; rw [ha, hb, add_zero]
      | smul c a _ ha => simp only [inner_smul_right] at *; rw [ha, mul_zero]
    rw [sub_sub, sub_eq_zero] at h8
    exact h8
  have h9 := (hI 0).const_add x
  simp only [h0, one_apply_eq_self] at h9
  exact h9.congr_of_eventuallyEq (Filter.Eventually.of_forall hF)

end GlobalTheory.Mem.Osc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesHasRootOfUnity
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Pj

namespace GlobalTheory.Mem

theorem exp_div_mul_eq_zpow_mul_zpow {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h : Nat.Coprime p q) :
    ∃ a b : ℤ, Complex.exp (2 * Real.pi * Complex.I / ((p * q : ℕ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I / ((p * (p - 1) : ℕ) : ℂ)) ^ a *
        Complex.exp (2 * Real.pi * Complex.I / ((q * (q - 1) : ℕ) : ℂ)) ^ b := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 h
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  refine ⟨v * p', u * q', ?_⟩
  rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  have h1 : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h2 : (q' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h3 : (p' : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  have h4 : (q' : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
  have h5 : (u : ℂ) * (p' + 1) + v * (q' + 1) = 1 := by exact_mod_cast huv
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  linear_combination (-1 : ℂ) * h5

theorem Base.exists_root_mul (B : Base) : ∃ y : B.O, B.embLL (B.OtoLL y) =
    Complex.exp (2 * Real.pi * Complex.I / ((B.host.g 0 * B.host.g 1 : ℕ) : ℂ)) := by
  have p0 := B.host.g_prime 0
  have p1 := B.host.g_prime 1
  obtain ⟨z₀, hz₀, e₀⟩ := B.roots_Ks (B.host.g 0 * (B.host.g 0 - 1)) (by simp)
  obtain ⟨z₁, hz₁, e₁⟩ := B.roots_Ks (B.host.g 1 * (B.host.g 1 - 1)) (by simp)
  obtain ⟨a, b, hab⟩ := exp_div_mul_eq_zpow_mul_zpow p0.two_le p1.two_le
    ((Nat.coprime_primes p0 p1).2 B.host.g_ne)
  have hmem : z₀ ^ a * z₁ ^ b ∈ B.Ks := mul_mem (zpow_mem hz₀ a) (zpow_mem hz₁ b)
  have he : B.embLL (z₀ ^ a * z₁ ^ b) =
      Complex.exp (2 * Real.pi * Complex.I / ((B.host.g 0 * B.host.g 1 : ℕ) : ℂ)) := by
    rw [map_mul, map_zpow₀, map_zpow₀, e₀, e₁, hab]
  have hne : B.host.g 0 * B.host.g 1 ≠ 0 := mul_ne_zero p0.ne_zero p1.ne_zero
  have hint : IsIntegral ℤ (B.embLL (z₀ ^ a * z₁ ^ b)) := by
    rw [he]
    exact (Complex.isPrimitiveRoot_exp _ hne).isIntegral (Nat.pos_of_ne_zero hne)
  have hint' : IsIntegral ℤ (z₀ ^ a * z₁ ^ b) :=
    (isIntegral_algHom_iff B.embLL.toIntAlgHom B.embLL.injective).1 hint
  refine ⟨⟨⟨z₀ ^ a * z₁ ^ b, hmem⟩, ?_⟩, he⟩
  exact (isIntegral_algHom_iff (B.Ks.val : B.Ks →+* B.LL).toIntAlgHom Subtype.val_injective).1 hint'

theorem hermitianCodeWordStages_has_rootOfUnity : ∀ X : Stages, OZeta X.toD7 := fun X => X.B.exists_root_mul

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerLieActionAdjointGaussianPolynomial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

variable {P Q : ℕ}

theorem act_sum_blocks (Z : Mat P Q) (A E : Matrix (Fin P) (Fin Q) ℂ) (x d : Ix P Q → ℂ) (t : ℂ) :
    (∑ i, ∑ k, Z (.inl k) (.inl i) * (x (.inl i) * d (.inl k) + ∑ j, A i j * E k j + if i = k then t / 2 else 0) -
      ∑ i, ∑ j, Z (.inr j) (.inl i) * (x (.inl i) * (x (.inr j) * t + ∑ m, A m j * d (.inl m)) +
        (∑ k, A i k * (x (.inr j) * d (.inr k) + ∑ m, A m j * E m k) + A i j * t))) +
    (∑ j, ∑ i, Z (.inl i) (.inr j) * E i j -
      ∑ j, ∑ k, Z (.inr k) (.inr j) * (x (.inr k) * d (.inr j) + ∑ i, A i k * E i j + if j = k then t / 2 else 0)) =
    (Z.trace / 2 + dS Z A x) * t + (∑ i, ∑ j, dA Z A i j * E i j + ∑ l, dX Z A x l * d l) := by
  induction Z using Matrix.induction_on' with
  | h_zero =>
    have h11 : (0 : Mat P Q).toBlocks₁₁ = 0 := rfl
    have h12 : (0 : Mat P Q).toBlocks₁₂ = 0 := rfl
    have h21 : (0 : Mat P Q).toBlocks₂₁ = 0 := rfl
    have h22 : (0 : Mat P Q).toBlocks₂₂ = 0 := rfl
    simp [dS, dA, dX, h11, h12, h21, h22]
  | h_add Z W hZ hW =>
    have h11 : (Z + W).toBlocks₁₁ = Z.toBlocks₁₁ + W.toBlocks₁₁ := rfl
    have h12 : (Z + W).toBlocks₁₂ = Z.toBlocks₁₂ + W.toBlocks₁₂ := rfl
    have h21 : (Z + W).toBlocks₂₁ = Z.toBlocks₂₁ + W.toBlocks₂₁ := rfl
    have h22 : (Z + W).toBlocks₂₂ = Z.toBlocks₂₂ + W.toBlocks₂₂ := rfl
    have hS : dS (Z + W) A x = dS Z A x + dS W A x := by
      simp only [dS, h21, h22, Matrix.add_mul, Matrix.trace_add, Matrix.add_mulVec, dotProduct_add]; ring
    have hA : dA (Z + W) A = dA Z A + dA W A := by
      simp only [dA, h11, h12, h21, h22, Matrix.add_mul, Matrix.mul_add]; abel
    have hX : dX (Z + W) A x = dX Z A x + dX W A x := by
      simp only [dX, h11, h21, h22, Matrix.add_mul, Matrix.mul_add, Matrix.add_mulVec, Matrix.sub_mulVec,
        Matrix.vecMul_add]
      ext (i | j) <;> simp <;> ring
    simp only [hS, hA, hX, Matrix.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib, Matrix.trace_add]
    simp only [add_mul] at hZ hW
    linear_combination hZ + hW
  | h_std_basis a b c =>
    rcases a with a | a <;> rcases b with b | b <;>
    simp [dS, dA, dX, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.single_apply, Matrix.mul_apply, Matrix.trace, Matrix.mulVec, Matrix.vecMul, dotProduct, ite_and,
      Fintype.sum_sum_type]
    · simp only [mul_add, Finset.mul_sum, mul_assoc]
      split_ifs <;> ring
    · rw [Finset.sum_comm (f := fun i k => A i a * (c * A b k) * E i k)]
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc, mul_left_comm]
      ring
    · simp only [mul_add, Finset.mul_sum, mul_assoc, mul_left_comm]
      split_ifs <;> ring

open MvPolynomial GlobalTheory.Oscillator in

theorem inner_omAct0_adjZ : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (v : F.H), (∀ (i : Fin P) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inl i) * f)) v = x (Sum.inl i) * inner ℂ (F.ι f) v + ∑ j, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inr j) f)) v) → (∀ (j : Fin Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (MvPolynomial.X (Sum.inr j) * f)) v = x (Sum.inr j) * inner ℂ (F.ι f) v + ∑ i, A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) f)) v) → ∀ (Z : Mat P Q) (f : MvPolynomial (Ix P Q) ℂ), inner ℂ (F.ι (omAct0 P Q (adjZ Z) f)) v = (Z.trace / 2 + dS Z A x) * inner ℂ (F.ι f) v + (∑ i, ∑ j, dA Z A i j * inner ℂ (F.ι (MvPolynomial.pderiv (Sum.inl i) (MvPolynomial.pderiv (Sum.inr j) f))) v + ∑ l, dX Z A x l * inner ℂ (F.ι (MvPolynomial.pderiv l f)) v) := by
  intro P Q F A x v h1 h2 Z f
  have hh : ∀ (p : Prop) [Decidable p], inner ℂ (F.ι (if p then (1 / 2 : ℂ) • f else 0)) v =
      if p then inner ℂ (F.ι f) v / 2 else 0 := by
    intro p _
    split_ifs
    · rw [map_smul, inner_smul_left]; simp [map_ofNat]; ring
    · simp
  have hd : ∀ k j : Fin Q, inner ℂ (F.ι (pderiv (Sum.inr k) (X (Sum.inr j) * f))) v =
      x (.inr j) * inner ℂ (F.ι (pderiv (.inr k) f)) v +
        ∑ m, A m j * inner ℂ (F.ι (pderiv (.inl m) (pderiv (.inr k) f))) v +
        if k = j then inner ℂ (F.ι f) v else 0 := by
    intro k j
    rw [← h2, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, inner_add_left, pderiv_X]
    by_cases h : k = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [← act_sum_blocks Z A (fun i j => inner ℂ (F.ι (pderiv (Sum.inl i) (pderiv (Sum.inr j) f))) v) x
    (fun l => inner ℂ (F.ι (pderiv l f)) v) (inner ℂ (F.ι f) v), omAct0_eq, oscAct_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, sum_inner, inner_smul_left,
    adjZ_apply, Fintype.sum_sum_type, Finset.sum_add_distrib, LinearMap.add_apply, map_add, inner_add_left]
  simp only [unitOp_inl_inl, unitOp_inl_inr, unitOp_inr_inl, unitOp_inr_inr, map_add, map_sub, map_neg,
    inner_add_left, inner_sub_left, inner_neg_left, hh, h1, h2, hd, sgn, map_mul, Complex.conj_conj,
    Int.cast_one, Int.cast_neg, map_one, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  have hc : ∀ (j : Fin Q) (i : Fin P), pderiv (Sum.inr j) (pderiv (Sum.inl i) f) =
      pderiv (Sum.inl i) (pderiv (Sum.inr j) f) := fun j i => pderiv_pderiv_comm _ _ _
  rw [add_add_add_comm]
  simp only [hc, mul_add (A _ _), Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 2 <;> refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_ <;> ring

end GlobalTheory.OscGauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetOneSubConjTransposeMulContractions
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem isUnit_det_one_sub_conjTranspose_mul_of_contractions (P Q : ℕ)
    (A B : Matrix (Fin P) (Fin Q) ℂ) (hA : (1 - Aᴴ * A).PosDef) (hB : (1 - Bᴴ * B).PosDef) :
    IsUnit (1 - Aᴴ * B).det := by
  rw [isUnit_iff_ne_zero]
  intro h
  obtain ⟨u, hu, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hsum : ((1 - Aᴴ * A) + (1 - Bᴴ * B) + (A - B)ᴴ * (A - B)).PosDef :=
    (hA.add hB).add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _)
  have heq : (1 - Aᴴ * A) + (1 - Bᴴ * B) + (A - B)ᴴ * (A - B)
      = (1 - Aᴴ * B) + (1 - Aᴴ * B)ᴴ := by
    simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
      conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [heq] at hsum
  have hpos := hsum.dotProduct_mulVec_pos hu
  have h2 : star u ⬝ᵥ ((1 - Aᴴ * B)ᴴ *ᵥ u) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, h0]
    simp
  rw [Matrix.add_mulVec, dotProduct_add, h0, h2] at hpos
  simp at hpos

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeNormalFormModuloUnipotentSemidirectStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeNormalForm_modulo_unipotentSemidirect : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalForm := by
  first | exact @GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect.latticeNormalForm | exact GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect.latticeNormalForm | (intros; apply GlobalTheory.Proof.latticeNormalForm_modulo_unipotentSemidirect.latticeNormalForm <;> assumption)
end

