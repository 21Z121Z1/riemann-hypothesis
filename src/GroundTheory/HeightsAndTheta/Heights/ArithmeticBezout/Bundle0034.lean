import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0006

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentGaussInvariant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped Matrix

open scoped ENNReal

noncomputable section

def unitMat {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis U.toLinearMap

theorem unitMat_mem {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    unitMat U ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  U.toMatrix_mem_unitaryGroup _ _

theorem unitary_apply_eq_sum {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (v : EuclideanSpace ℂ (Fin n)) (k : Fin n) : U v k = ∑ j, unitMat U k j * v j := by
  have h := LinearMap.toMatrix_mulVec_repr (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis U.toLinearMap v
  have h2 := congrFun h k
  simpa [unitMat, Matrix.mulVec, dotProduct] using h2.symm

theorem unitMat_mul_symm {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    unitMat U * unitMat U.symm = 1 := by
  rw [unitMat, unitMat, ← LinearMap.toMatrix_mul]
  have : U.toLinearMap * U.symm.toLinearMap = 1 := LinearMap.ext fun x => by simp
  rw [this, LinearMap.toMatrix_one]

theorem sum_norm_sq_vecMul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) (r : Fin n → ℂ) :
    ∑ j, ‖(r ᵥ* A) j‖ ^ 2 = ∑ j, ‖r j‖ ^ 2 := by
  have key : ∀ s : Fin n → ℂ, ((∑ j, ‖s j‖ ^ 2 : ℝ) : ℂ) = s ⬝ᵥ star s := by
    intro s
    simp [dotProduct, Complex.mul_conj']
  apply Complex.ofReal_injective
  rw [key (r ᵥ* A), key r, Matrix.star_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff).1 hA, Matrix.vecMul_one]

theorem measurePreserving_vecMul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (fun r : Fin n → ℂ => r ᵥ* A) volume volume := by
  set f : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' Aᵀ).restrictScalars ℝ with hf
  have hfun : (fun r : Fin n → ℂ => r ᵥ* A) = f := by
    funext r
    simp [hf, Matrix.toLin'_apply, Matrix.mulVec_transpose]
  have hdet : LinearMap.det f = 1 := by
    have hd : ‖A.det‖ = 1 := by
      have h1 : A.det ∈ unitary ℂ := Matrix.det_of_mem_unitary hA
      exact CStarRing.norm_of_mem_unitary h1
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose,
      Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, hd]
    norm_num
  have hmeas : Measurable (fun r : Fin n → ℂ => r ᵥ* A) := by
    apply Continuous.measurable
    fun_prop
  refine ⟨hmeas, ?_⟩
  rw [hfun, Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
  simp

def matSub {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (π : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ :=
  fun i => π i ᵥ* unitMat U

theorem measurePreserving_matSub {m n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving (matSub (m := m) U) volume volume :=
  volume_preserving_pi fun _ => measurePreserving_vecMul (unitMat_mem U)

theorem matSub_symm_matSub {m n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) (π : Fin m → Fin n → ℂ) :
    matSub U.symm (matSub U π) = π := by
  funext i
  simp [matSub, Matrix.vecMul_vecMul, unitMat_mul_symm]

def matSubEquiv {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    (Fin m → Fin n → ℂ) ≃ᵐ (Fin m → Fin n → ℂ) where
  toFun := matSub U
  invFun := matSub U.symm
  left_inv := matSub_symm_matSub U
  right_inv π := by simpa using matSub_symm_matSub U.symm π
  measurable_toFun := (measurePreserving_matSub U).measurable
  measurable_invFun := (measurePreserving_matSub U.symm).measurable

theorem linProj_matSub {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (π : Fin m → Fin n → ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    linProj (matSub U π) v = linProj π (U v) := by
  simp only [linProj, matSub, unitary_apply_eq_sum, Matrix.vecMul, dotProduct]
  congr 1
  funext i
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem matGauss_matSub {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (π : Fin m → Fin n → ℂ) : matGauss (matSub U π) = matGauss π := by
  simp only [matGauss, matSub, sum_norm_sq_vecMul (unitMat_mem U)]

theorem firstCoordVec_eq_basisFun {n : ℕ} (hn : 0 < n) :
    firstCoordVec n = EuclideanSpace.basisFun (Fin n) ℂ ⟨0, hn⟩ := by
  ext j
  simp [firstCoordVec, EuclideanSpace.basisFun_apply, Fin.ext_iff]

theorem exists_unitary_leadCoordPlane {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (T : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hT : finrank ℂ T = m)
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ T) :
    ∃ U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n),
      (∀ v ∈ leadCoordPlane n m, U v ∈ T) ∧ (∀ t ∈ T, ∃ v ∈ leadCoordPlane n m, U v = t) ∧
        U ((‖y‖ : ℂ) • firstCoordVec n) = y := by
  classical
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  obtain ⟨u, huT, hu1, hyu⟩ : ∃ u ∈ T, ‖u‖ = 1 ∧ (‖y‖ : ℂ) • u = y := by
    by_cases hy0 : y = 0
    · have hTne : T ≠ ⊥ := by
        intro h
        rw [h, finrank_bot] at hT
        omega
      obtain ⟨t, htT, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTne
      exact ⟨(‖t‖⁻¹ : ℂ) • t, T.smul_mem _ htT, norm_smul_inv_norm ht0, by simp [hy0]⟩
    · refine ⟨(‖y‖⁻¹ : ℂ) • y, T.smul_mem _ hy, norm_smul_inv_norm hy0, ?_⟩
      rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast norm_ne_zero_iff.2 hy0), one_smul]
  obtain ⟨bT, hbT⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ) (E := T)
    (ι := Fin m) (v := fun _ => (⟨u, huT⟩ : T)) (s := {⟨0, hm⟩}) (by simp [hT]) (by
      refine ⟨fun i => by simpa using hu1, fun i j hij => ?_⟩
      exact absurd (Subtype.ext ((Set.mem_singleton_iff.1 i.2).trans
        (Set.mem_singleton_iff.1 j.2).symm)) hij)
  have hbT0 : (bT ⟨0, hm⟩ : EuclideanSpace ℂ (Fin n)) = u := by
    rw [hbT _ (Set.mem_singleton _)]
  set v : Fin n → EuclideanSpace ℂ (Fin n) :=
    fun j => if h : (j : ℕ) < m then (bT ⟨j, h⟩ : EuclideanSpace ℂ (Fin n)) else 0 with hv
  obtain ⟨B, hB⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
    (E := EuclideanSpace ℂ (Fin n)) (ι := Fin n) (v := v) (s := {j | (j : ℕ) < m}) (by simp) (by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      have hi' : (i : ℕ) < m := hi
      have hj' : (j : ℕ) < m := hj
      simp only [Set.domRestrict, hv, dif_pos hi', dif_pos hj']
      rw [← Submodule.coe_inner, orthonormal_iff_ite.1 bT.orthonormal]
      simp [Fin.ext_iff])
  have hBv : ∀ j : Fin n, ∀ h : (j : ℕ) < m, B j = (bT ⟨j, h⟩ : EuclideanSpace ℂ (Fin n)) := by
    intro j h
    rw [hB j h]
    simp [hv, h]
  set e := EuclideanSpace.basisFun (Fin n) ℂ with he
  have hU : ∀ w, e.equiv B (Equiv.refl _) w = ∑ j, w j • B j := by
    intro w
    conv_lhs => rw [← e.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply]
    rfl
  refine ⟨e.equiv B (Equiv.refl _), ?_, ?_, ?_⟩
  · intro w hw
    have hw' : ∀ j : Fin n, m ≤ (j : ℕ) → w j = 0 := hw
    rw [hU]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases h : (j : ℕ) < m
    · rw [hBv j h]
      exact T.smul_mem _ (bT _).2
    · rw [hw' j (by omega), zero_smul]
      exact T.zero_mem
  · intro t ht
    have hBk : ∀ k : Fin m, B (Fin.castLE hmn k) = (bT k : EuclideanSpace ℂ (Fin n)) :=
      fun k => hBv _ (by simp)
    refine ⟨∑ k : Fin m, (bT.repr ⟨t, ht⟩ k) • e (Fin.castLE hmn k), ?_, ?_⟩
    · refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
      show ∀ j : Fin n, m ≤ (j : ℕ) → (e (Fin.castLE hmn k)) j = 0
      intro j hj
      have hne : j ≠ Fin.castLE hmn k := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [he, EuclideanSpace.basisFun_apply, hne]
    · calc e.equiv B (Equiv.refl _) (∑ k : Fin m, (bT.repr ⟨t, ht⟩ k) • e (Fin.castLE hmn k))
            = ∑ k : Fin m, (bT.repr ⟨t, ht⟩ k) • (bT k : EuclideanSpace ℂ (Fin n)) := by
              simp [map_sum, map_smul, OrthonormalBasis.equiv_apply_basis, hBk]
        _ = ((∑ k : Fin m, (bT.repr ⟨t, ht⟩ k) • bT k : T) : EuclideanSpace ℂ (Fin n)) := by
              simp
        _ = t := by rw [bT.sum_repr]
  · rw [firstCoordVec_eq_basisFun hn, map_smul, OrthonormalBasis.equiv_apply_basis,
      Equiv.refl_apply, hBv _ hm]
    rw [show (⟨((⟨0, hn⟩ : Fin n) : ℕ), hm⟩ : Fin m) = ⟨0, hm⟩ from rfl, hbT0, hyu]

theorem TangentGaussInvariant.proof : TangentGaussInvariant.Statement := by
  intro n m hm hmn T hT y hy
  obtain ⟨U, hLT, hTL, hUy⟩ := exists_unitary_leadCoordPlane hm hmn T hT y hy
  set L := leadCoordPlane n m with hL
  let W : L →ₗᵢ[ℂ] T :=
    { toFun := fun x => ⟨U x, hLT x x.2⟩
      map_add' := fun x x' => by ext1; simp
      map_smul' := fun c x => by ext1; simp
      norm_map' := fun x => by simp }
  have hWx : ∀ x : L, (W x : EuclideanSpace ℂ (Fin n)) = U x := fun _ => rfl
  have hWsurj : Function.Surjective W := by
    intro t
    obtain ⟨w, hw, hwt⟩ := hTL t t.2
    exact ⟨⟨w, hw⟩, Subtype.ext hwt⟩
  have hfin : finrank ℂ L = finrank ℂ T :=
    (LinearEquiv.ofBijective W.toLinearMap ⟨W.injective, hWsurj⟩).finrank_eq
  have hJ : ∀ π : Fin m → Fin n → ℂ, tangentJac (matSub U π) L = tangentJac π T := by
    intro π
    have hcomp : (linProjₗ (matSub U π)).comp L.subtype =
        ((linProjₗ π).comp T.subtype).comp W.toLinearMap := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearIsometry.coe_toLinearMap,
        hWx]
      exact linProj_matSub U π x
    unfold tangentJac
    have h2 := LinearMap.normDet_comp_of_finrank_eq (𝕜 := ℂ) (U := L) (V := T)
      (W := EuclideanSpace ℂ (Fin m)) W.toLinearMap ((linProjₗ π).comp T.subtype) (by exact hfin)
    rw [hcomp, h2, LinearIsometry.normDet_eq_one, mul_one]
  have hemb : MeasurableEmbedding (matSub (m := m) U) := (matSubEquiv U).measurableEmbedding
  have key := (measurePreserving_matSub (m := m) U).lintegral_comp_emb hemb
    (fun π => matGauss π *
      (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
        (linProj π (((‖y‖ : ℝ) : ℂ) • firstCoordVec n)) *
      ENNReal.ofReal (tangentJac π (leadCoordPlane n m)))
  unfold tangentGaussProfile
  refine Eq.trans ?_ key
  refine lintegral_congr fun π => ?_
  simp only [matGauss_matSub, linProj_matSub, hUy, ← hL, hJ]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentGaussMoment
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

theorem linProj_smul_left {m n : ℕ} (π : Fin m → Fin n → ℂ) (c : ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    linProj π (c • y) = c • linProj π y :=
  (linProjₗ π).map_smul c y

theorem tangentGauss_indicator_eq {m n : ℕ} (π : Fin m → Fin n → ℂ) (r : ℝ) :
    (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π ((r : ℂ) • firstCoordVec n)) =
      if |r| * ‖linProj π (firstCoordVec n)‖ < 1 then (1 : ℝ≥0∞) else 0 := by
  simp only [Set.indicator, Metric.mem_ball, dist_zero_right, linProj_smul_left, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, Pi.one_apply]

theorem tangentGaussProfile_abs (n m : ℕ) (r : ℝ) :
    tangentGaussProfile n m |r| = tangentGaussProfile n m r := by
  unfold tangentGaussProfile
  simp only [tangentGauss_indicator_eq, abs_abs]

theorem tangentGaussProfile_antitoneOn (n m : ℕ) :
    AntitoneOn (tangentGaussProfile n m) (Set.Ici 0) := by
  intro r hr s hs hrs
  unfold tangentGaussProfile
  refine lintegral_mono fun π => ?_
  simp only [tangentGauss_indicator_eq, abs_of_nonneg (Set.mem_Ici.1 hr),
    abs_of_nonneg (Set.mem_Ici.1 hs)]
  have key : s * ‖linProj π (firstCoordVec n)‖ < 1 → r * ‖linProj π (firstCoordVec n)‖ < 1 :=
    fun h => lt_of_le_of_lt (mul_le_mul_of_nonneg_right hrs (norm_nonneg _)) h
  gcongr
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (key h1) h2
  · exact zero_le_one
  · exact le_rfl

theorem measurable_tangentGaussProfile (n m : ℕ) : Measurable (tangentGaussProfile n m) := by
  have hψ : Antitone fun t : ℝ => tangentGaussProfile n m (max t 0) := fun a b hab =>
    tangentGaussProfile_antitoneOn n m (Set.mem_Ici.2 (le_max_right a 0))
      (Set.mem_Ici.2 (le_max_right b 0)) (max_le_max hab le_rfl)
  have h : tangentGaussProfile n m = fun r => tangentGaussProfile n m (max |r| 0) := by
    funext r
    rw [max_eq_left (abs_nonneg r), tangentGaussProfile_abs]
  rw [h]
  exact hψ.measurable.comp measurable_abs

theorem pow_two_mul_sub_one_le {r : ℝ} (hr : 0 ≤ r) (m : ℕ) : r ^ (2 * m - 1) ≤ (1 + r ^ 2) ^ m := by
  rcases le_total r 1 with h | h
  · exact (pow_le_one₀ hr h).trans (one_le_pow₀ (by nlinarith))
  · calc r ^ (2 * m - 1) ≤ r ^ (2 * m) := pow_le_pow_right₀ h (Nat.sub_le _ _)
      _ = (r ^ 2) ^ m := by rw [pow_mul]
      _ ≤ (1 + r ^ 2) ^ m := pow_le_pow_left₀ (sq_nonneg r) (by linarith) m

theorem TangentGaussMoment.proof (hA : LeadPlaneJac.Statement) (hB : LeadBlockGaussTail.Statement) :
    TangentGaussMoment.Statement := by
  intro n m hm hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hk : ∀ r : ℝ, tangentGaussProfile (m + k) m r = ∫⁻ π : Fin m → Fin (m + k) → ℂ, matGauss π *
      (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
        (linProj π ((r : ℂ) • firstCoordVec (m + k))) *
      ENNReal.ofReal (‖(coordPlaneBlock π).det‖ ^ 2) := by
    intro r
    unfold tangentGaussProfile
    simp only [hA m k]
  have hpos : ∀ r : ℝ, 0 < tangentGaussProfile (m + k) m r := by
    intro r
    rw [hk r]
    have hcont : Continuous fun π : Fin m → Fin (m + k) → ℂ =>
        linProj π ((r : ℂ) • firstCoordVec (m + k)) := by
      unfold linProj
      exact (PiLp.continuous_toLp 2 _).comp (by fun_prop)
    have hdet : Continuous fun π : Fin m → Fin (m + k) → ℂ => (coordPlaneBlock π).det :=
      Continuous.matrix_det (by unfold coordPlaneBlock; fun_prop)
    have hmeas : Measurable fun π : Fin m → Fin (m + k) → ℂ => matGauss π *
        (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
          (linProj π ((r : ℂ) • firstCoordVec (m + k))) *
        ENNReal.ofReal (‖(coordPlaneBlock π).det‖ ^ 2) := by
      refine Measurable.mul (Measurable.mul ?_ ?_) ?_
      · unfold matGauss
        exact ENNReal.measurable_ofReal.comp (by fun_prop)
      · exact (measurable_one.indicator Metric.isOpen_ball.measurableSet).comp hcont.measurable
      · exact ENNReal.measurable_ofReal.comp ((continuous_norm.comp hdet).pow 2).measurable
    rw [lintegral_pos_iff_support hmeas]
    set U := {π : Fin m → Fin (m + k) → ℂ |
      linProj π ((r : ℂ) • firstCoordVec (m + k)) ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1}
    have hU : IsOpen U := Metric.isOpen_ball.preimage hcont
    have hU0 : (0 : Fin m → Fin (m + k) → ℂ) ∈ U := by
      have h0 : linProj (0 : Fin m → Fin (m + k) → ℂ) ((r : ℂ) • firstCoordVec (m + k)) = 0 := by
        ext i
        simp [linProj]
      simp only [U, Set.mem_ofPred_eq, h0, Metric.mem_ball, dist_self, zero_lt_one]
    have : (volume : Measure (Fin m → Fin (m + k) → ℂ)).IsAddHaarMeasure :=
      Measure.pi.isAddHaarMeasure _
    refine (hU.measure_pos volume ⟨0, hU0⟩).trans_le (measure_mono_ae ?_)
    filter_upwards [ae_coordPlaneBlock_det_ne_zero m k] with π hπdet hπU
    show matGauss π * _ * _ ≠ 0
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    · rw [Set.indicator_of_mem hπU]
      exact one_ne_zero
    · exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  obtain ⟨C, hC⟩ := hB m k hm
  have hmeasM : Measurable fun r : ℝ =>
      tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) :=
    (measurable_tangentGaussProfile _ _).mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  refine ⟨measurable_tangentGaussProfile _ _, tangentGaussProfile_antitoneOn _ _, hpos, ?_, ?_⟩
  · rw [setLIntegral_pos_iff hmeasM]
    have hsub : Set.Ioi (0 : ℝ) ⊆
        Function.support (fun r : ℝ =>
          tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))) ∩
          Set.Ioi 0 := by
      intro r hr
      refine ⟨?_, hr⟩
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      exact mul_ne_zero (hpos r).ne' (ENNReal.ofReal_pos.2 (by
        have := Set.mem_Ioi.1 hr
        positivity)).ne'
    exact lt_of_lt_of_le (by simp) (measure_mono hsub)
  · have hle : ∀ r ∈ Set.Ioi (0 : ℝ),
        tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) ≤
          ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) := by
      intro r hr
      have hr0 : 0 ≤ r := le_of_lt hr
      have h1 := pow_two_mul_sub_one_le hr0 m
      have hx : 0 < 1 + r ^ 2 := by positivity
      have hC0 : 0 ≤ max C 0 := le_max_right _ _
      calc tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))
          ≤ ENNReal.ofReal (C / (1 + r ^ 2) ^ (m + 1)) * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) := by
            rw [hk r]
            gcongr
            exact hC r
        _ = ENNReal.ofReal (C / (1 + r ^ 2) ^ (m + 1) * (2 * m * r ^ (2 * m - 1))) :=
            (ENNReal.ofReal_mul' (by positivity)).symm
        _ ≤ ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) := by
            refine ENNReal.ofReal_le_ofReal ?_
            calc C / (1 + r ^ 2) ^ (m + 1) * (2 * m * r ^ (2 * m - 1))
                ≤ max C 0 / (1 + r ^ 2) ^ (m + 1) * (2 * m * (1 + r ^ 2) ^ m) := by
                  gcongr
                  exact le_max_left _ _
              _ = 2 * m * max C 0 * (1 + r ^ 2)⁻¹ := by
                  field_simp
                  ring
    calc ∫⁻ r in Set.Ioi (0 : ℝ), tangentGaussProfile (m + k) m r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1))
        ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) :=
          setLIntegral_mono' measurableSet_Ioi hle
      _ ≤ ∫⁻ r, ENNReal.ofReal (2 * m * max C 0 * (1 + r ^ 2)⁻¹) := setLIntegral_le_lintegral _ _
      _ < ⊤ := (integrable_inv_one_add_sq.const_mul _).lintegral_lt_top

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentJacCompress
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

noncomputable section

theorem det_starProjection_compress {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : E →L[ℂ] F) (T : Submodule ℂ E) :
    (T.starProjection ∘L A.adjoint ∘L A ∘L T.starProjection + (1 - T.starProjection)).det =
      (LinearMap.adjoint ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype) ∘ₗ ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype)).det := by
  obtain ⟨Q, hQdef⟩ : ∃ Q : E →L[ℂ] E,
      Q = T.starProjection ∘L A.adjoint ∘L A ∘L T.starProjection + (1 - T.starProjection) := ⟨_, rfl⟩
  rw [← hQdef]
  have hQx : ∀ x : E, Q x =
      T.starProjection (A.adjoint (A (T.starProjection x))) + (x - T.starProjection x) := by
    intro x; subst hQdef; simp
  have hQT : T ≤ T.comap (Q : E →ₗ[ℂ] E) := by
    intro x hx
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, hQx,
      Submodule.starProjection_eq_self_iff.mpr hx, sub_self, add_zero]
    exact T.starProjection_apply_mem _
  have hres : (Q : E →ₗ[ℂ] E).restrict hQT =
      LinearMap.adjoint ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype) ∘ₗ ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype) := by
    ext1 x
    apply ext_inner_right ℂ
    intro z
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, Submodule.coe_inner,
      LinearMap.coe_restrict_apply, ContinuousLinearMap.coe_coe, hQx,
      Submodule.starProjection_eq_self_iff.mpr x.2, sub_self, add_zero,
      Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr z.2,
      ContinuousLinearMap.adjoint_inner_left]
    rfl
  have hquot : T.mapQ T (Q : E →ₗ[ℂ] E) hQT = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.id_comp, ContinuousLinearMap.coe_coe]
    rw [Submodule.Quotient.eq, hQx]
    have h : T.starProjection (A.adjoint (A (T.starProjection x))) + (x - T.starProjection x) - x =
        T.starProjection (A.adjoint (A (T.starProjection x))) - T.starProjection x := by abel
    rw [h]
    exact T.sub_mem (T.starProjection_apply_mem _) (T.starProjection_apply_mem _)
  rw [ContinuousLinearMap.det, LinearMap.det_eq_det_mul_det T _ hQT, hres, hquot, LinearMap.det_id,
    mul_one]

theorem TangentJacCompress.proof : TangentJacCompress.Statement := by
  intro n m π T
  unfold tangentJac
  have h := LinearMap.normDet_sq (𝕜 := ℂ) (U := T) (V := EuclideanSpace ℂ (Fin m)) ((linProjₗ π).comp T.subtype)
  exact h.trans (det_starProjection_compress (LinearMap.toContinuousLinearMap (linProjₗ π)) T).symm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeChartArea
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)

def chartGramDensity {n e : ℕ} (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (S : Matrix (Fin n) (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℝ) (y : Fin e → ℂ) (w : ((k : Unit) → PBlk n k) → ℂ) : ℝ := by
  classical
  exact if hγ : ∃ γ, IsSheet P Ψ y w γ then
    g (fun i => hγ.choose y ⟨(), i⟩) *
      ((e.factorial : ℝ) / Real.pi ^ e *
          gramVol (fun y' => S *ᵥ fun i => hγ.choose y' ⟨(), i⟩) y /
        ‖WithLp.toLp 2 (S *ᵥ fun i => hγ.choose y ⟨(), i⟩)‖ ^ (2 * (e + 1)))
  else 0

def ConeChartArea.Statement : Prop :=
  ∀ (n e : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (g : (Fin n → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → Measurable g →
      (∀ (c : ℂ) (z : Fin n → ℂ), c ≠ 0 → g (c • z) = g z) →
      IntegrableOn (fun y => g ((ObjectsHeight.ofPointMatrix S hS).pointOf y))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧
          ∀ q ∈ complexFibreIdeal P, eval ((ObjectsHeight.ofPointMatrix S hS).pointOf y) q = 0}
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) →
      coneIntegral (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P) e g =
        ∫ y, ∑ᶠ w ∈ fibre P Ψ y, chartGramDensity P Ψ S g y w

end GroundTheory.Heights₂.Heights
end
end

