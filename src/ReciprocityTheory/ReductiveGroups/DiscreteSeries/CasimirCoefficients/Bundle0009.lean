import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0006
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0007
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0002
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0008

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousConjProjection
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

private lemma toMatrix_mul_alt (a b : KG ε) : toMK (a * b) = toMK a * toMK b := rfl

private lemma toMatrix_one_alt : toMK (1 : KG ε) = 1 := rfl

private lemma toMatrix_inv_mul (a : KG ε) : toMK a⁻¹ * toMK a = 1 := by
  rw [← toMatrix_mul_alt, inv_mul_cancel, toMatrix_one_alt]

private lemma toMatrix_mul_inv (a : KG ε) : toMK a * toMK a⁻¹ = 1 := by
  rw [← toMatrix_mul_alt, mul_inv_cancel, toMatrix_one_alt]

private lemma kType_op_mul (T : KType ε Λ) (a b : KG ε) : T.op (a * b) = T.op a * T.op b := by
  unfold KType.op
  rw [map_mul]
  rfl

private lemma kType_op_one (T : KType ε Λ) : T.op 1 = 1 := by
  unfold KType.op
  rw [map_one]
  rfl

private lemma kType_op_mul_inv (T : KType ε Λ) (a : KG ε) : T.op a * T.op a⁻¹ = 1 := by
  rw [← kType_op_mul, mul_inv_cancel, kType_op_one]

private lemma kType_op_inv_mul (T : KType ε Λ) (a : KG ε) : T.op a⁻¹ * T.op a = 1 := by
  rw [← kType_op_mul, inv_mul_cancel, kType_op_one]

private def ps2E (T : KType ε Λ) (k : KG ε) : T.V ≃L[ℂ] T.V :=
  ContinuousLinearEquiv.equivOfInverse (T.op k) (T.op k⁻¹)
    (fun v => by
      have := congrArg (fun A : T.V →L[ℂ] T.V => A v) (kType_op_inv_mul T k)
      simpa using this)
    (fun v => by
      have := congrArg (fun A : T.V →L[ℂ] T.V => A v) (kType_op_mul_inv T k)
      simpa using this)

private def ps2C (T : KType ε Λ) (k : KG ε) : (T.V →L[ℂ] T.V) ≃L[ℂ] (T.V →L[ℂ] T.V) :=
  (ps2E T k).arrowCongr (ps2E T k)

private lemma conjAction_apply (T : KType ε Λ) (k : KG ε) (A : T.V →L[ℂ] T.V) :
    ps2C T k A = T.op k * A * T.op k⁻¹ := by
  ext v
  rfl

private lemma kType_schur_lemma (T : KType ε Λ) (A : T.V →L[ℂ] T.V) (hA : ∀ k, T.op k * A = A * T.op k) :
    ∃ c : ℂ, A = c • (1 : T.V →L[ℂ] T.V) := by
  have hw : T.w ≠ 0 := fun h => by
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  haveI : Nontrivial T.V := ⟨⟨T.w, 0, hw⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (A : Module.End ℂ T.V)
  refine ⟨c, ?_⟩
  have key : ∀ k v, A (T.op k v) = T.op k (A v) := fun k v => by
    have := congrArg (fun B : T.V →L[ℂ] T.V => B v) (hA k)
    simp only [ContinuousLinearMap.mul_apply] at this
    exact this.symm
  have hinv : ∀ k : KG ε, ∀ v ∈ Module.End.eigenspace (A : Module.End ℂ T.V) c,
      ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) v ∈
        Module.End.eigenspace (A : Module.End ℂ T.V) c := by
    intro k v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    change A (T.op k v) = c • T.op k v
    rw [key, show A v = c • v from hv, map_smul]
  rcases T.irred _ hinv with h | h
  · exfalso
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    have hv1 : v ∈ Module.End.eigenspace (A : Module.End ℂ T.V) c := by
      rw [Module.End.mem_eigenspace_iff]
      exact hv.apply_eq_smul
    rw [h] at hv1
    exact hv.2 ((Submodule.mem_bot ℂ).1 hv1)
  · ext v
    have hv : v ∈ Module.End.eigenspace (A : Module.End ℂ T.V) c := by
      rw [h]
      exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hv
    simpa using hv

private lemma continuous_kType_op (T : KType ε Λ) : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont

private lemma continuous_conj_projection (T : KType ε Λ) :
    Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ := ((continuous_kType_op T).mul continuous_const).mul ((continuous_kType_op T).comp continuous_inv)

private lemma integral_conj_equivariant (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε) (x : Matrix (Fin n) (Fin n) ℂ) :
    ∫ k', PhiM μ (toMK k'⁻¹ * (toMK k * x * toMK k⁻¹) * toMK k') • (T.op k' * projW T * T.op k'⁻¹) ∂(muK ε) =
      ps2C T k (∫ k', PhiM μ (toMK k'⁻¹ * x * toMK k') • (T.op k' * projW T * T.op k'⁻¹) ∂(muK ε)) := by
  haveI : (muK ε).IsMulLeftInvariant := by
    unfold muK
    infer_instance
  rw [← ContinuousLinearEquiv.integral_comp_comm (ps2C T k)]
  calc _ = ∫ k', PhiM μ (toMK (k * k')⁻¹ * (toMK k * x * toMK k⁻¹) * toMK (k * k')) •
        (T.op (k * k') * projW T * T.op (k * k')⁻¹) ∂(muK ε) :=
        (MeasureTheory.integral_mul_left_eq_self (fun k' => PhiM μ (toMK k'⁻¹ * (toMK k * x * toMK k⁻¹) *
          toMK k') • (T.op k' * projW T * T.op k'⁻¹)) k).symm
    _ = _ := by
        congr 1
        funext k'
        rw [map_smul, conjAction_apply]
        congr 1
        · congr 1
          rw [_root_.mul_inv_rev, toMatrix_mul_alt, toMatrix_mul_alt]
          calc _ = toMK k'⁻¹ * (toMK k⁻¹ * toMK k) * x * (toMK k⁻¹ * toMK k) * toMK k' := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [toMatrix_inv_mul, Matrix.mul_one, Matrix.mul_one]
        · rw [_root_.mul_inv_rev, kType_op_mul, kType_op_mul]
          simp only [mul_assoc]

theorem psM_conj (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε) (x : Matrix (Fin n) (Fin n) ℂ) :
    psM T μ (toMK k * x * toMK k⁻¹) = T.op k * psM T μ x * T.op k⁻¹ := by
  simp only [psM]
  rw [integral_conj_equivariant, conjAction_apply, mul_smul_comm, smul_mul_assoc]

theorem psM_one (T : KType ε Λ) (μ : Fin n → ℤ) : psM T μ 1 = 1 := by
  have hw : T.w ≠ 0 := fun h => by
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  haveI : Nontrivial T.V := ⟨⟨T.w, 0, hw⟩⟩
  haveI : CompactSpace (KG ε) := compactSpace_KG ε
  haveI : IsFiniteMeasureOnCompacts (muK ε) := by
    unfold muK
    infer_instance
  have hPhi1 : PhiM μ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    unfold PhiM
    refine Finset.prod_eq_one fun i _ => ?_
    unfold lead
    rw [dif_pos (by have := i.isLt; omega), Matrix.submatrix_one _ (Fin.castLE_injective _),
      Matrix.det_one, _root_.one_zpow]
  have hcomm : ∀ k : KG ε, T.op k * psM T μ 1 = psM T μ 1 * T.op k := by
    intro k
    have h := psM_conj T μ k 1
    rw [Matrix.mul_one, toMatrix_mul_inv] at h
    calc T.op k * psM T μ 1 = T.op k * psM T μ 1 * (T.op k⁻¹ * T.op k) := by
          rw [kType_op_inv_mul, mul_one]
      _ = T.op k * psM T μ 1 * T.op k⁻¹ * T.op k := by simp only [mul_assoc]
      _ = psM T μ 1 * T.op k := by rw [← h]
  obtain ⟨c, hc⟩ := kType_schur_lemma T (psM T μ 1) hcomm
  obtain ⟨tr, htr⟩ : ∃ tr : (T.V →L[ℂ] T.V) →L[ℂ] ℂ,
      ∀ A, tr A = LinearMap.trace ℂ T.V (A : T.V →ₗ[ℂ] T.V) :=
    ⟨LinearMap.toContinuousLinearMap ((LinearMap.trace ℂ T.V).comp (ContinuousLinearMap.coeLM ℂ)),
      fun A => rfl⟩
  have hP : LinearMap.trace ℂ T.V (projW T : T.V →ₗ[ℂ] T.V) = 1 := by
    have e2 : (projW T : T.V →ₗ[ℂ] T.V) =
        ((innerSL ℂ T.w : T.V →L[ℂ] ℂ) : T.V →ₗ[ℂ] ℂ).smulRight T.w := LinearMap.ext fun v => rfl
    rw [e2, LinearMap.trace_smulRight]
    simp [inner_self_eq_norm_sq_to_K, T.w_norm]
  have htrk : ∀ k, tr (T.op k * projW T * T.op k⁻¹) = 1 := by
    intro k
    rw [htr]
    have e1 : ((T.op k * projW T * T.op k⁻¹ : T.V →L[ℂ] T.V) : T.V →ₗ[ℂ] T.V) =
        (ps2E T k).toLinearEquiv.conj (projW T : T.V →ₗ[ℂ] T.V) := LinearMap.ext fun v => rfl
    rw [e1, LinearMap.trace_conj', hP]
  have hint : Integrable (fun k : KG ε => T.op k * projW T * T.op k⁻¹) (muK ε) :=
    (continuous_conj_projection T).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  have hv : ((muK ε Set.univ).toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (muK_univ_pos ε).ne'
  have hd : (Module.finrank ℂ T.V : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have h1 : tr (psM T μ 1) = c * (Module.finrank ℂ T.V : ℂ) := by
    rw [htr, hc]
    simp [LinearMap.trace_one]
  have hI : psM T μ 1 = ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
      ∫ k, (T.op k * projW T * T.op k⁻¹) ∂(muK ε) := by
    simp only [psM]
    congr 1
    congr 1
    funext k
    rw [Matrix.mul_one, toMatrix_inv_mul, hPhi1, one_smul]
  have h2 : tr (psM T μ 1) = (Module.finrank ℂ T.V : ℂ) := by
    rw [hI, map_smul, ← ContinuousLinearMap.integral_comp_comm tr hint]
    simp only [htrk, integral_const, smul_eq_mul, Complex.real_smul, mul_one]
    exact div_mul_cancel₀ _ hv
  have hc1 : c = 1 := by
    have := h1.symm.trans h2
    exact mul_right_cancel₀ hd (this.trans (one_mul _).symm)
  rw [hc, hc1, one_smul]

private def ps2J (ε : Fin n → Bool) : KG ε :=
  ⟨⟨⟨Jm ε, Jm ε, Jm_mul_self ε, Jm_mul_self ε⟩, by
      show (Jm ε)ᴴ * Jm ε * Jm ε = Jm ε
      rw [Jm_conjTranspose, Jm_mul_self, Matrix.one_mul]⟩,
    by
      show Jm ε ∈ Kset ε
      refine ⟨?_, rfl⟩
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Jm_conjTranspose, Jm_mul_self]⟩

private lemma toMatrix_signElement : toMK (ps2J ε) = Jm ε := rfl

private lemma signElement_inv : (ps2J ε)⁻¹ = ps2J ε := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show Jm ε * Jm ε = 1
  exact Jm_mul_self ε

private lemma signElement_central (k : KG ε) : ps2J ε * k = k * ps2J ε := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show Jm ε * toMK k = toMK k * Jm ε
  exact (show toMK k ∈ Kset ε from k.2).2.symm

theorem psM_exp_neg (T : KType ε Λ) (μ : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    psM T μ (NormedSpace.exp (-X)) = psM T μ (NormedSpace.exp X) := by
  have hJ : Jm ε * X * Jm ε = -X := by
    calc Jm ε * X * Jm ε = Jm ε * (X * Jm ε) := Matrix.mul_assoc _ _ _
      _ = Jm ε * -(Jm ε * X) := by rw [hX.2]
      _ = -X := by rw [Matrix.mul_neg, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]
  have hinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv (Jm_mul_self ε)
  have hU : IsUnit (Jm ε) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse (Jm_mul_self ε))
  have hE := Matrix.exp_conj (Jm ε) X hU
  rw [hinv, hJ] at hE
  have hE' : NormedSpace.exp (-X) = toMK (ps2J ε) * NormedSpace.exp X * toMK (ps2J ε)⁻¹ := by
    rw [signElement_inv, toMatrix_signElement]
    exact hE
  rw [hE', psM_conj]
  obtain ⟨c, hc⟩ := kType_schur_lemma T (T.op (ps2J ε)) (fun k => by
    rw [← kType_op_mul, ← kType_op_mul, signElement_central])
  have hm := kType_op_mul_inv T (ps2J ε)
  rw [hc] at hm ⊢
  calc c • (1 : T.V →L[ℂ] T.V) * psM T μ (NormedSpace.exp X) * T.op (ps2J ε)⁻¹ =
        psM T μ (NormedSpace.exp X) * (c • (1 : T.V →L[ℂ] T.V) * T.op (ps2J ε)⁻¹) := by
        simp only [smul_mul_assoc, one_mul, mul_smul_comm]
    _ = psM T μ (NormedSpace.exp X) := by rw [hm, mul_one]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecMoments
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

lemma dm_rank_add (A B : Matrix (Fin n) (Fin n) ℂ) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank ℂ (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank ℂ ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) := by
        apply Submodule.finrank_mono
        rintro _ ⟨v, rfl⟩
        exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

lemma dm_zero_of_eq {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hYp : inP ε Y) (a b : Fin n)
    (hab : ε a = ε b) : Y a b = 0 := by
  have h := congrFun (congrFun hYp.2 a) b
  simp only [Jm, Matrix.mul_diagonal, Matrix.neg_apply, Matrix.diagonal_mul, hab] at h
  split_ifs at h
  · linear_combination (1 / 2 : ℂ) * h
  · linear_combination (-1 / 2 : ℂ) * h

lemma dm_rank_le {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hYp : inP ε Y) :
    Y.rank ≤ 2 * q0 ε := by
  classical
  set P : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun a => if ε a then 1 else 0 with hPd
  set Q : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun a => if ε a then 0 else 1 with hQd
  have hY : Y = P * Y * Q + Q * Y * P := by
    ext a b
    simp only [hPd, hQd, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases ha : ε a <;> by_cases hb : ε b <;> simp [ha, hb] <;>
      exact dm_zero_of_eq hYp a b (by simp [ha, hb])
  have hP : P.rank = pOf ε := by
    rw [hPd, Matrix.rank_diagonal, Fintype.card_subtype]
    unfold pOf
    congr 1; ext a; by_cases h : ε a <;> simp [h]
  have hQ : Q.rank = qOf ε := by
    rw [hQd, Matrix.rank_diagonal, Fintype.card_subtype]
    unfold qOf
    congr 1; ext a; by_cases h : ε a <;> simp [h]
  have h1 : (P * Y * Q).rank ≤ q0 ε :=
    le_min ((Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_left _ _).trans hP.le))
      ((Matrix.rank_mul_le_right _ _).trans hQ.le)
  have h2 : (Q * Y * P).rank ≤ q0 ε :=
    le_min ((Matrix.rank_mul_le_right _ _).trans hP.le)
      ((Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_left _ _).trans hQ.le))
  calc Y.rank = (P * Y * Q + Q * Y * P).rank := congrArg Matrix.rank hY
    _ ≤ (P * Y * Q).rank + (Q * Y * P).rank := dm_rank_add _ _
    _ ≤ q0 ε + q0 ε := add_le_add h1 h2
    _ = 2 * q0 ε := by ring

lemma dm_card_le {ε : Fin n → Bool} {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hYp : inP ε Y) : (univ.filter fun j => y j ≠ 0).card ≤ 2 * q0 ε := by
  have hdet : IsUnit U.det := Matrix.isUnit_det_of_left_inverse (Matrix.mem_unitaryGroup_iff'.1 hU)
  have hdet' : IsUnit Uᴴ.det := Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff'.1 hU)
  have h1 : Y.rank = (univ.filter fun j => y j ≠ 0).card := by
    rw [hY, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet',
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet, Matrix.rank_diagonal, Fintype.card_subtype]
    simp [Complex.ofReal_eq_zero]
  rw [← h1]
  exact dm_rank_le hYp

lemma dm_range {ε : Fin n → Bool} {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hYp : inP ε Y) (J : Finset (Fin n)) :
    |∑ j ∈ J, y j| ≤ Real.sqrt (2 * q0 ε) * Real.sqrt (hs Y) := by
  unfold hs
  have key : ∀ M : Matrix (Fin n) (Fin n) ℂ, (((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ)) : ℂ) = (M * Mᴴ).trace := by
    intro M
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    first
      | (rw [Complex.star_def, Complex.mul_conj'])
      | (rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring)
      | simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hUU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have h2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, Uᴴ * (U * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have htr : (Y * Yᴴ).trace = (((∑ j, y j ^ 2 : ℝ)) : ℂ) := by
    rw [hY]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, h2]
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hUU, Matrix.mul_one,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.conj_ofReal, sq]
  have hsum : ∑ i, ∑ j, ‖Y i j‖ ^ 2 = ∑ j, y j ^ 2 := by
    have h := key Y
    rw [htr] at h
    exact_mod_cast h
  have hT : ∑ j ∈ J, y j = ∑ j ∈ J.filter (fun j => y j ≠ 0), y j :=
    (Finset.sum_filter_ne_zero _).symm
  have hcard : (J.filter fun j => y j ≠ 0).card ≤ 2 * q0 ε :=
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ J))).trans
      (dm_card_le hU hY hYp)
  have hcs : (∑ j ∈ J.filter (fun j => y j ≠ 0), y j) ^ 2 ≤
      ((J.filter fun j => y j ≠ 0).card : ℝ) * ∑ j, y j ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (J.filter fun j => y j ≠ 0) (fun _ => (1 : ℝ)) y
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => sq_nonneg _)
  rw [hsum, ← Real.sqrt_mul (by positivity), hT]
  apply Real.abs_le_sqrt
  refine hcs.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun j _ => sq_nonneg _))
  exact_mod_cast hcard

theorem dec_moments {ε : Fin n → Bool} {Y U : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hYp : inP ε Y) (i : ℕ) (hi : i ≤ n) :
    (∑ J : {J : Finset (Fin n) // J.card = i},
        ‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 = 1) ∧
    (∑ J : {J : Finset (Fin n) // J.card = i},
        ‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 * (∑ j ∈ J.1, y j) = 0) ∧
    (∑ J : {J : Finset (Fin n) // J.card = i},
        ‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2 * (∑ j ∈ J.1, y j) ^ 2 =
      ∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) < i ∧ i ≤ (a : ℕ) then ‖Y a b‖ ^ 2 else 0) ∧
    (∀ J : {J : Finset (Fin n) // J.card = i},
        |∑ j ∈ J.1, y j| ≤ Real.sqrt (2 * q0 ε) * Real.sqrt (hs Y)) := by
  have hd : ∀ a, Y a a = 0 := fun a => dm_zero_of_eq hYp a a rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := dm_mass hU hi
    have h2 : ∑ J : {J : Finset (Fin n) // J.card = i}, dmW U hi J = 1 := by exact_mod_cast h
    exact h2
  · have h := dm_mean hU hY hd hi
    have h2 : ∑ J : {J : Finset (Fin n) // J.card = i}, dmW U hi J * (∑ j ∈ J.1, y j) = 0 := by
      exact_mod_cast h
    exact h2
  · have h := (dm_var hU hY hd hi).trans (dm_rhs hY i)
    have h2 : ∑ J : {J : Finset (Fin n) // J.card = i}, dmW U hi J * (∑ j ∈ J.1, y j) ^ 2 =
        ∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) < i ∧ i ≤ (a : ℕ) then ‖Y a b‖ ^ 2 else 0 := by
      exact_mod_cast h
    exact h2
  · intro J
    exact dm_range hU hY hYp J.1

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LocalB
section
noncomputable section

open Matrix Filter Topology Set

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}

section PathL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma lcB_path (z Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℝ => z * NormedSpace.exp ((s : ℂ) • Y)) (z * Y) 0 := by
  have h1 := hasDerivAt_exp_smul_const Y ((0 : ℝ) : ℂ)
  have hof : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 (0 : ℝ) := Complex.ofRealCLM.hasDerivAt
  have h2 := HasDerivAt.scomp (h := fun y : ℝ => (y : ℂ)) (0 : ℝ) h1 hof
  have h3 := h2.const_mul z
  exact h3.congr_deriv (by simp)

end PathL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma lcB_hasDerivAt (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hUo : IsOpen U)
    (hdiff : DifferentiableOn ℂ (psM T μ) U) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hid : ∀ z ∈ U, fderiv ℂ (psM T μ) z (z * Y) = -(T.dτ Y * psM T μ z))
    (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (A : Matrix (Fin n) (Fin n) ℂ) {t : ℝ} (ht : A * NormedSpace.exp ((t : ℂ) • Y) ∈ U) :
    HasDerivAt (fun s : ℝ => T.op (γ s) * psM T μ (A * NormedSpace.exp ((s : ℂ) • Y))) 0 t := by
  set z := A * NormedSpace.exp ((t : ℂ) • Y) with hz
  have hcomm : ∀ s : ℝ, A * NormedSpace.exp ((s : ℂ) • Y) =
      z * NormedSpace.exp (((s - t : ℝ) : ℂ) • Y) := by
    intro s
    rw [hz, mul_assoc, ← Matrix.exp_add_of_commute _ _
      (((Commute.refl Y).smul_left _).smul_right _), ← add_smul]
    rw [show ((t : ℂ) + ((s - t : ℝ) : ℂ)) = (s : ℂ) by push_cast; ring]
  have h1 := lcB_path z Y
  have h2 := hasDerivAt_iff_tendsto_slope.1 h1
  have h3 : HasDerivAt (fun s : ℝ => z * NormedSpace.exp ((s : ℂ) • Y)) (z * Y) 0 :=
    hasDerivAt_iff_tendsto_slope.2 h2
  have h4 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h3)
  have hp : HasDerivAt (fun s : ℝ => A * NormedSpace.exp ((s : ℂ) • Y)) (z * Y) t := by
    rw [show (fun s : ℝ => A * NormedSpace.exp ((s : ℂ) • Y)) =
      fun s => z * NormedSpace.exp (((s - t : ℝ) : ℂ) • Y) from funext hcomm]
    exact h4
  have hF : HasFDerivAt (psM T μ) (fderiv ℂ (psM T μ) z) z :=
    (hdiff.differentiableAt (hUo.mem_nhds ht)).hasFDerivAt
  have hF' : HasFDerivAt (psM T μ) ((fderiv ℂ (psM T μ) z).restrictScalars ℝ) z :=
    hF.restrictScalars ℝ
  have hq0 := hF'.comp_hasDerivAt t hp
  have e : ((fderiv ℂ (psM T μ) z).restrictScalars ℝ) (z * Y) = -(T.dτ Y * psM T μ z) := hid z ht
  have hq : HasDerivAt (fun s : ℝ => psM T μ (A * NormedSpace.exp ((s : ℂ) • Y)))
      (-(T.dτ Y * psM T μ z)) t := hq0.congr_deriv e
  have ho1 : HasDerivAt (fun s : ℝ => T.op (γ s)) (T.op (γ t) * T.dτ Y) t := by
    have h5 := (T.hasDeriv Y hY γ hγ).const_mul (T.op (γ t))
    have h6 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h5)
    have he : (fun s : ℝ => T.op (γ s)) =
        fun s => T.op (γ t) * ((T.τ (γ (s - t)) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) := by
      funext s
      have hs := hmul t (s - t)
      rw [show t + (s - t) = s by ring] at hs
      simp only [KType.op]
      rw [hs, map_mul]
      rfl
    rw [he]
    exact h6
  have hprod := ho1.mul hq
  have hzero : T.op (γ t) * T.dτ Y * psM T μ (A * NormedSpace.exp ((t : ℂ) • Y)) +
      T.op (γ t) * -(T.dτ Y * psM T μ z) = 0 := by
    rw [mul_neg, mul_assoc]
    exact add_neg_cancel _
  exact hzero ▸ hprod

theorem lcB_const (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hUo : IsOpen U)
    (hdiff : DifferentiableOn ℂ (psM T μ) U) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hid : ∀ z ∈ U, fderiv ℂ (psM T μ) z (z * Y) = -(T.dτ Y * psM T μ z))
    (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (A : Matrix (Fin n) (Fin n) ℂ) (hpath : ∀ t ∈ Icc (0 : ℝ) 1, A * NormedSpace.exp ((t : ℂ) • Y) ∈ U) :
    T.op (γ 1) * psM T μ (A * NormedSpace.exp Y) = psM T μ A := by
  have h0 : γ 0 = 1 := by simpa using hmul 0 0
  let g : ℝ → T.V →L[ℂ] T.V := fun t => T.op (γ t) * psM T μ (A * NormedSpace.exp ((t : ℂ) • Y))
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g 0 t := fun t ht =>
    lcB_hasDerivAt T μ hUo hdiff hid hY γ hγ hmul A (hpath t ht)
  have hcont : ContinuousOn g (Icc 0 1) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hc := constant_of_has_deriv_right_zero hcont
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩
  simpa [g, h0, KType.op] using hc

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

