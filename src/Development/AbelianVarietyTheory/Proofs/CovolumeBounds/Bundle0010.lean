import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.LevelGroupUnitaryHermitian
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.BlockEmbConjTranspose
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B GlobalTheory.HCXi

noncomputable section

namespace GlobalTheory.HCXi

theorem blockEmb_conjTranspose (k i r' : ℕ)
    (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    (ιLev k i r' g)ᴴ = ιLev k i r' gᴴ := by
  rw [PI.QnLevBasicsW.ιLev_eq, PI.QnLevBasicsW.ιLev_eq, conjTranspose_submatrix, fromBlocks_conjTranspose]
  simp

theorem blockEmb_mem_Kset : ∀ k r' : ℕ, ∀ y ∈ Kset k r', ιLev k 1 r' y ∈ Kset k (1 + r') := by
  intro k r' y hy
  refine ⟨PI.QnLevBasicsW.level_group_unitary_hermitian k 1 r' y hy.1, ?_⟩
  rw [blockEmb_conjTranspose, ← (PI.QnLevBasicsW.level_group_homomorphism k 1 r').2, hy.2]
  exact (PI.QnLevBasicsW.level_group_homomorphism k 1 r').1

end GlobalTheory.HCXi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsUnitaryOfGramEq
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.UnitaryExtension

theorem exists_isometry_comp {W V : Type} [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (a b : W →ₗ[ℂ] V)
    (h : ∀ x, ‖b x‖ = ‖a x‖) : ∃ u : V →ₗᵢ[ℂ] V, ∀ x, u (a x) = b x := by
  have hk : LinearMap.ker a ≤ LinearMap.ker b := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← norm_eq_zero, h, hx, norm_zero]
  let l : LinearMap.range a →ₗ[ℂ] V :=
    ((LinearMap.ker a).liftQ b hk) ∘ₗ (a.quotKerEquivRange.symm : LinearMap.range a →ₗ[ℂ] _)
  have hl : ∀ x, l ⟨a x, LinearMap.mem_range_self a x⟩ = b x := by
    intro x
    simp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    simp
  let L : LinearMap.range a →ₗᵢ[ℂ] V :=
    { toLinearMap := l
      norm_map' := by
        rintro ⟨y, x, rfl⟩
        rw [hl, h]; rfl }
  refine ⟨L.extend, fun x => ?_⟩
  have := L.extend_apply ⟨a x, LinearMap.mem_range_self a x⟩
  rw [← hl]
  exact this

theorem exists_unitary_mul_eq {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix (Fin n) ι ℂ) (h : Aᴴ * A = Bᴴ * B) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * A = B := by
  have key : ∀ (C : Matrix (Fin n) ι ℂ) (x : EuclideanSpace ℂ ι),
      inner ℂ (Matrix.toEuclideanLin C x) (Matrix.toEuclideanLin C x)
        = inner ℂ x (Matrix.toEuclideanLin (Cᴴ * C) x) := by
    intro C x
    rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    congr 1
    simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  obtain ⟨u, hu⟩ := exists_isometry_comp (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) (by
    intro x
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ (Matrix.toEuclideanLin A x), key, key, h])
  refine ⟨Matrix.toEuclideanLin.symm u.toLinearMap, ?_, ?_⟩
  · apply (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin n) (n := Fin n)).injective
    ext1 x
    apply ext_inner_left ℂ
    intro y
    have e : Matrix.toEuclideanLin ((Matrix.toEuclideanLin.symm u.toLinearMap)ᴴ * Matrix.toEuclideanLin.symm u.toLinearMap) x
        = Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap)ᴴ (Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap) x) := by
      generalize Matrix.toEuclideanLin.symm u.toLinearMap = U
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    rw [e, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]
    simp [Matrix.toLpLin_apply]
  · apply (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin n) (n := ι)).injective
    ext1 x
    have e : Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap * A) x
        = Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm u.toLinearMap) (Matrix.toEuclideanLin A x) := by
      generalize Matrix.toEuclideanLin.symm u.toLinearMap = U
      simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
    rw [e, LinearEquiv.apply_symm_apply]
    exact hu x

theorem exists_unitary_of_gram_eq : ∀ (n m : ℕ) (E : Matrix (Fin n) (Fin n) ℂ) (A B : Matrix (Fin n) (Fin m) ℂ), Eᴴ = E → E * E = E → E * A = A → E * B = B → Aᴴ * A = Bᴴ * B → ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * E = E * U ∧ U * (1 - E) = 1 - E ∧ U * A = B := by
  intro n m E A B hE hEE hA hB hG
  have hP : (1 - E)ᴴ = 1 - E := by rw [conjTranspose_sub, conjTranspose_one, hE]
  have hPA : (1 - E) * A = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hA, sub_self]
  have hPB : (1 - E) * B = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hB, sub_self]
  have hAP : Aᴴ * (1 - E) = 0 := by
    rw [← hP, ← conjTranspose_mul, hPA, conjTranspose_zero]
  have hBP : Bᴴ * (1 - E) = 0 := by
    rw [← hP, ← conjTranspose_mul, hPB, conjTranspose_zero]
  obtain ⟨U, hU, hUA⟩ := exists_unitary_mul_eq (Matrix.fromCols A (1 - E))
    (Matrix.fromCols B (1 - E)) (by
      rw [conjTranspose_fromCols_eq_fromRows_conjTranspose,
        conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols,
        fromRows_mul_fromCols, hP, hG, hPA, hPB, hAP, hBP])
  rw [mul_fromCols, fromCols_ext_iff] at hUA
  obtain ⟨h1, h2⟩ := hUA
  refine ⟨U, hU, ?_, h2, h1⟩
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have h3 : (1 - E) * Uᴴ = 1 - E := by
    have := congrArg conjTranspose h2
    rwa [conjTranspose_mul, hP] at this
  have h4 : (1 - E) * U = 1 - E := by
    calc (1 - E) * U = (1 - E) * Uᴴ * U := by rw [h3]
      _ = 1 - E := by rw [Matrix.mul_assoc, hU, Matrix.mul_one]
  have h5 : U * (1 - E) = (1 - E) * U := by rw [h2, h4]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul] at h5
  exact sub_right_injective h5

end GlobalTheory.UnitaryExtension
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FrameIsotropicOrthonormal
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi.FrameOrth

theorem entry (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Fin (r + 1)) :
    ((frame k r)ᴴ * M * frame k r) a b =
      star (fvec k r (isoVec k r) a) ⬝ᵥ (M *ᵥ fvec k r (isoVec k r) b) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, frame, Matrix.conjTranspose_apply, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply]

theorem bvec_pair {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    star (bvec i) ⬝ᵥ (M *ᵥ bvec j) = M i j := by
  simp [bvec, Pi.star_single]

theorem fvec_castSucc (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    fvec k r z a.castSucc = bvec (eI k r a) := by
  simp [fvec]

theorem fvec_last (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

theorem half : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * 2) = 1 := by
  have h : (Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹ * 2) = (1 : ℝ) := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h3 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    nlinarith
  exact_mod_cast h

theorem star_isoVec (k r : ℕ) : star (isoVec k r) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
    (star (bvec (wI k r 0)) + star (bvec (wI k r (Fin.last k)))) := by
  rw [isoVec, star_smul, star_add, Complex.star_def, Complex.conj_ofReal]

theorem frame_orthonormal_isotropic : ∀ k r : ℕ, 1 ≤ k →
    (frame k r)ᴴ * frame k r = 1 ∧ (frame k r)ᴴ * Hpk k r * frame k r = 0 := by
  intro k r hk
  constructor
  · rw [← Matrix.mul_one (frame k r)ᴴ]
    ext a b
    rw [entry]
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp only [fvec_last, fvec_castSucc, star_isoVec] <;>
      simp only [isoVec, Matrix.mulVec_smul, Matrix.mulVec_add, dotProduct_smul, smul_dotProduct,
        add_dotProduct, dotProduct_add, bvec_pair, smul_eq_mul]
    · have h : wI k r 0 ≠ wI k r (Fin.last k) := by
        simp only [wI, ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last]; omega
      rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h.symm, Matrix.one_apply_eq,
        Matrix.one_apply_eq, Matrix.one_apply_eq]
      linear_combination half
    · rename_i b
      have := b.isLt
      rw [Matrix.one_apply_ne, Matrix.one_apply_ne, Matrix.one_apply_ne]
      · simp
      all_goals simp only [wI, eI, ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last, Fin.val_castSucc]; omega
    · rename_i b
      have := b.isLt
      rw [Matrix.one_apply_ne, Matrix.one_apply_ne, Matrix.one_apply_ne]
      · simp
      all_goals simp only [wI, eI, ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last, Fin.val_castSucc]; omega
    · simp [Matrix.one_apply, eI, Fin.ext_iff]
  · ext a b
    rw [entry]
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp only [fvec_last, fvec_castSucc, star_isoVec] <;>
      simp only [isoVec, Matrix.mulVec_smul, Matrix.mulVec_add, dotProduct_smul, smul_dotProduct,
        add_dotProduct, dotProduct_add, bvec_pair, smul_eq_mul, Matrix.zero_apply]
    · have h1 : Hpk k r (wI k r 0) (wI k r 0) = 1 := by
        unfold Hpk
        have e : (wI k r 0).val = r := by simp [wI]
        rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩, if_neg (by omega)]
      have h2 : Hpk k r (wI k r 0) (wI k r (Fin.last k)) = 0 := by
        simp only [Hpk, wI, Fin.ext_iff, Fin.val_zero, Fin.val_last]
        split_ifs <;> first | rfl | omega
      have h3 : Hpk k r (wI k r (Fin.last k)) (wI k r 0) = 0 := by
        simp only [Hpk, wI, Fin.ext_iff, Fin.val_zero, Fin.val_last]
        split_ifs <;> first | rfl | omega
      have h4 : Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) = -1 := by
        unfold Hpk
        have e : (wI k r (Fin.last k)).val = r + k := by simp [wI]
        rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩, if_pos e]
      rw [h1, h2, h3, h4]
      ring
    · rename_i b
      have := b.isLt
      have h1 : ∀ j, Hpk k r (wI k r j) (eI k r b) = 0 := by
        intro j
        have := j.isLt
        simp only [Hpk, wI, eI, Fin.ext_iff]
        split_ifs <;> first | rfl | omega
      rw [h1, h1]
      ring
    · rename_i b
      have := b.isLt
      have h1 : ∀ j, Hpk k r (eI k r b) (wI k r j) = 0 := by
        intro j
        have := j.isLt
        simp only [Hpk, wI, eI, Fin.ext_iff]
        split_ifs <;> first | rfl | omega
      rw [h1, h1]
      ring
    · rename_i a b
      have := a.isLt
      have := b.isLt
      simp only [Hpk, eI, Fin.ext_iff]
      split_ifs <;> first | rfl | omega

end GlobalTheory.HCXi.FrameOrth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.GramMinorDetTriangularMul
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi

theorem submatrix_mul_upperTriangular_castLE {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ)
    (u : Matrix (Fin m) (Fin m) ℂ) {j : ℕ} (hj : j ≤ m) (hu : u.BlockTriangular id) :
    (A * u).submatrix id (Fin.castLE hj) =
      A.submatrix id (Fin.castLE hj) * u.submatrix (Fin.castLE hj) (Fin.castLE hj) := by
  ext i b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, id]
  symm
  refine Finset.sum_of_injOn (Fin.castLE hj) ?_ ?_ ?_ ?_
  · intro a _ c _ h
    exact Fin.castLE_injective hj h
  · intro a _
    exact Finset.mem_univ _
  · intro c _ hc
    have hlt : Fin.castLE hj b < c := by
      by_contra hle
      apply hc
      have h1 : c.val ≤ b.val := by
        have := not_lt.mp hle
        exact this
      refine ⟨⟨c.val, lt_of_le_of_lt h1 b.2⟩, by simp, ?_⟩
      ext
      simp
    rw [hu (show id (Fin.castLE hj b) < id c from hlt), mul_zero]
  · intro a _
    rfl

theorem det_leading_gram_mul_upperTriangular :
    ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℂ) (u : Matrix (Fin m) (Fin m) ℂ) (j : ℕ) (hj : j ≤ m), u.BlockTriangular id → (((A * u)ᴴ * (A * u)).submatrix (Fin.castLE hj) (Fin.castLE hj)).det = ((∏ b : Fin j, Complex.normSq (u (Fin.castLE hj b) (Fin.castLE hj b)) : ℝ) : ℂ) * ((Aᴴ * A).submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
  intro n m A u j hj hu
  have key : ∀ B : Matrix (Fin n) (Fin m) ℂ,
      (Bᴴ * B).submatrix (Fin.castLE hj) (Fin.castLE hj) =
        (B.submatrix id (Fin.castLE hj))ᴴ * B.submatrix id (Fin.castLE hj) := by
    intro B
    ext a b
    simp [Matrix.mul_apply]
  have hu' : (u.submatrix (Fin.castLE hj) (Fin.castLE hj)).BlockTriangular id := by
    intro a b hab
    exact hu (show id (Fin.castLE hj b) < id (Fin.castLE hj a) from hab)
  rw [key, key, submatrix_mul_upperTriangular_castLE A u hj hu, Matrix.conjTranspose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (u.submatrix (Fin.castLE hj) (Fin.castLE hj)),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_of_upperTriangular hu']
  simp only [Matrix.submatrix_apply]
  rw [← map_prod Complex.normSq, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

end GlobalTheory.HCXi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.GramPositiveVolumeContinuous
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi.GramPos

theorem sq_half : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num

theorem bvec_pair {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    star (bvec i) ⬝ᵥ M *ᵥ bvec j = M i j := by
  have : star (bvec i : Fin n → ℂ) = bvec i := by
    ext l; by_cases h : l = i <;> simp [bvec, h]
  rw [this]; simp [bvec]

theorem frame_pair (k r : ℕ) (M : Mat k r) (a b : Fin (r + 1)) :
    ((frame k r)ᴴ * M * frame k r) a b =
      star (fvec k r (isoVec k r) a) ⬝ᵥ M *ᵥ fvec k r (isoVec k r) b := by
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, frame, dotProduct, mulVec]

theorem pair_iso_left (k r : ℕ) (M : Mat k r) (j) :
    star (isoVec k r) ⬝ᵥ M *ᵥ bvec j =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (M (wI k r 0) j + M (wI k r (Fin.last k)) j) := by
  rw [isoVec, star_smul, star_add, smul_dotProduct, add_dotProduct, bvec_pair, bvec_pair]
  simp

theorem pair_iso_right (k r : ℕ) (M : Mat k r) (v) :
    star v ⬝ᵥ M *ᵥ isoVec k r =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (star v ⬝ᵥ M *ᵥ bvec (wI k r 0) + star v ⬝ᵥ M *ᵥ bvec (wI k r (Fin.last k))) := by
  rw [isoVec, mulVec_smul, mulVec_add, dotProduct_smul, dotProduct_add]
  simp

theorem frame_orthonormal (k r : ℕ) (hk : 1 ≤ k) : (frame k r)ᴴ * frame k r = 1 := by
  ext a b
  have := frame_pair k r 1 a b
  rw [Matrix.mul_one] at this
  rw [this]
  have ha := a.isLt
  have hb := b.isLt
  unfold fvec
  split_ifs with h1 h2 h2
  · rw [bvec_pair]; simp [one_apply, eI, Fin.ext_iff]
  · rw [pair_iso_right, bvec_pair, bvec_pair]
    simp only [one_apply, eI, wI, Fin.ext_iff, Fin.val_last, Fin.val_zero]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
  · rw [pair_iso_left]
    simp only [one_apply, eI, wI, Fin.ext_iff, Fin.val_last, Fin.val_zero]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
  · rw [pair_iso_right, pair_iso_left, pair_iso_left]
    simp only [one_apply, wI, Fin.ext_iff, Fin.val_last, Fin.val_zero]
    have e : a.val = b.val := by omega
    have h3 : ¬ (r + k = r + 0) := by omega
    have h4 : ¬ (r + 0 = r + k) := by omega
    simp only [if_pos e, h3, h4, if_true, if_false]
    linear_combination 2 * sq_half

lemma mulVec_inj (k r : ℕ) (hk : 1 ≤ k) (g : Mat k r) (hg : g ∈ GV k r) :
    Function.Injective (g * frame k r).mulVec := by
  have hH : Hpk k r * Hpk k r = 1 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1
  have hF : (frame k r)ᴴ * frame k r = 1 := frame_orthonormal k r hk
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have h1 : ((frame k r)ᴴ * (Hpk k r * (gᴴ * Hpk k r))) * (g * frame k r) = 1 := by
    calc ((frame k r)ᴴ * (Hpk k r * (gᴴ * Hpk k r))) * (g * frame k r)
        = (frame k r)ᴴ * ((Hpk k r * (gᴴ * Hpk k r * g)) * frame k r) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hH, Matrix.one_mul, hF]
  intro x y hxy
  have := congrArg (fun v => ((frame k r)ᴴ * (Hpk k r * (gᴴ * Hpk k r))) *ᵥ v) hxy
  simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this

lemma gram_pos (k r : ℕ) (hk : 1 ≤ k) (g : Mat k r) (hg : g ∈ GV k r) (a : Fin (r + 1)) :
    0 < gram k r g a := by
  have hP : ((g * frame k r)ᴴ * (g * frame k r)).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self _ (mulVec_inj k r hk g hg)
  have hS := hP.submatrix (Fin.castLE_injective (Nat.succ_le_of_lt a.isLt))
  have hd := hS.det_pos
  exact (Complex.pos_iff.mp hd).1

lemma gram_continuous (k r : ℕ) (a : Fin (r + 1)) : Continuous fun g : Mat k r => gram k r g a := by
  unfold gram
  have h : Continuous fun g : Mat k r => g * frame k r := continuous_id.matrix_mul continuous_const
  exact Complex.continuous_re.comp
    ((h.matrix_conjTranspose.matrix_mul h).matrix_submatrix _ _).matrix_det

lemma gram_measurable (k r : ℕ) (a : Fin (r + 1)) :
    Measurable fun x : Mt k r => gram k r (Matrix.of x) a := by
  have h : Continuous fun x : Mt k r => gram k r (Matrix.of x) a := gram_continuous k r a
  exact h.measurable

theorem gram_vHalf_pos_measurable_continuousOn : ∀ k r : ℕ, 1 ≤ k → (∀ g ∈ GV k r, ∀ a : Fin (r + 1), 0 < gram k r g a) ∧ (∀ g ∈ GV k r, 0 < vHalf k r g) ∧ (Measurable fun x : Mt k r => vHalf k r (Matrix.of x)) ∧ ContinuousOn (vHalf k r) (GV k r) := by
  intro k r hk
  refine ⟨gram_pos k r hk, fun g hg => ?_, ?_, ?_⟩
  · unfold vHalf
    exact mul_pos (Finset.prod_pos fun a _ => inv_pos.mpr (gram_pos k r hk g hg _))
      (Real.rpow_pos_of_pos (gram_pos k r hk g hg _) _)
  · unfold vHalf
    exact (Finset.measurable_prod _ fun a _ => (gram_measurable k r _).inv).mul
      ((gram_measurable k r _).pow_const _)
  · unfold vHalf
    refine ContinuousOn.mul (continuousOn_finsetProd _ fun a _ => ?_) ?_
    · exact (gram_continuous k r _).continuousOn.inv₀ fun g hg => (gram_pos k r hk g hg _).ne'
    · exact (gram_continuous k r _).continuousOn.rpow_const
        fun g hg => Or.inl (gram_pos k r hk g hg _).ne'

end GlobalTheory.HCXi.GramPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MaximalCompactSubgroupProperties
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

noncomputable section

namespace GlobalTheory.HCXi.KGroup

theorem closedSubgroup (k r : ℕ) : IsClosedSubgroup (Kset k r) := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  refine ⟨⟨hG.one_mem, by simp⟩, ?_, ?_, fun a ha => hG.unit a ha.1, ?_⟩
  · intro a ha b hb
    refine ⟨hG.mul_mem a ha.1 b hb.1, ?_⟩
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc aᴴ, ha.2, Matrix.one_mul, hb.2]
  · intro a ha
    refine ⟨hG.inv_mem a ha.1, ?_⟩
    rw [Matrix.inv_eq_left_inv ha.2, conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp ha.2
  · have hc : Continuous fun g : Mat k r => gᴴ * g :=
      (continuous_id.matrix_conjTranspose).matrix_mul continuous_id
    exact hG.closed.inter (isClosed_singleton.preimage hc)

theorem compact (k r : ℕ) : IsCompact (Kset k r) := by
  have hB : IsCompact (Set.pi Set.univ fun _ : Fin (2 * r + k + 1) =>
      Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset (s := (Set.pi Set.univ fun _ : Fin (2 * r + k + 1) =>
      Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) 1)) hB
      (closedSubgroup k r).closed ?_
  intro g hg i _ j _
  have hu : Matrix.of g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ :=
    Matrix.mem_unitaryGroup_iff'.mpr hg.2
  simpa using entry_norm_bound_of_unitary hu i j

theorem hpk_mem (k r : ℕ) : Hpk k r ∈ Kset k r := by
  obtain ⟨h1, h2, -⟩ := hermitian_pos_facts_hold k r
  refine ⟨?_, by rw [h1, h2]⟩
  show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
  rw [h1, h2, Matrix.one_mul]

theorem star_mem {k r : ℕ} {κ : Mat k r} (h : κ ∈ Kset k r) : κᴴ ∈ Kset k r := by
  have := (closedSubgroup k r).inv_mem κ h
  rwa [Matrix.inv_eq_left_inv h.2] at this

theorem comm_hpk {k r : ℕ} {κ : Mat k r} (h : κ ∈ Kset k r) : κ * Hpk k r = Hpk k r * κ := by
  have h1 : κᴴ * Hpk k r * κ = Hpk k r := h.1
  have h2 : κ * κᴴ = 1 := mul_eq_one_comm.mp h.2
  calc κ * Hpk k r = κ * (κᴴ * Hpk k r * κ) := by rw [h1]
    _ = (κ * κᴴ) * Hpk k r * κ := by simp only [Matrix.mul_assoc]
    _ = Hpk k r * κ := by rw [h2, Matrix.one_mul]

theorem sum_normSq_eq_trace {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, ∑ j, Complex.normSq (g i j) = (trace (gᴴ * g)).re := by
  rw [Finset.sum_comm]
  simp only [trace, diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.normSq_apply]

theorem gN_biinv {k r : ℕ} {κ κ' : Mat k r} (h : κ ∈ Kset k r) (h' : κ' ∈ Kset k r) (g : Mat k r) :
    gN (κ * g * κ') = gN g := by
  have h2 : κ' * κ'ᴴ = 1 := mul_eq_one_comm.mp h'.2
  unfold gN
  rw [sum_normSq_eq_trace, sum_normSq_eq_trace]
  have e : (κ * g * κ')ᴴ * (κ * g * κ') = κ'ᴴ * (gᴴ * g * κ') := by
    calc (κ * g * κ')ᴴ * (κ * g * κ') = κ'ᴴ * (gᴴ * (κᴴ * κ) * g * κ') := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h.2, Matrix.mul_one]
  rw [e, trace_mul_comm, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem kset_facts : ∀ k r : ℕ, IsClosedSubgroup (Kset k r) ∧ IsCompact (Kset k r) ∧ Hpk k r ∈ Kset k r ∧ (∀ κ ∈ Kset k r, κᴴ ∈ Kset k r ∧ κ * Hpk k r = Hpk k r * κ) ∧ ∀ κ ∈ Kset k r, ∀ κ' ∈ Kset k r, ∀ g : Mat k r, gN (κ * g * κ') = gN g :=
  fun k r => ⟨closedSubgroup k r, compact k r, hpk_mem k r, fun _ h => ⟨star_mem h, comm_hpk h⟩,
    fun _ h _ h' g => gN_biinv h h' g⟩

end GlobalTheory.HCXi.KGroup
end
end

