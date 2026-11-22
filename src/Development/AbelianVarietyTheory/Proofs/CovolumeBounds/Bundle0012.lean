import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0010
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsUnitaryCommMulEqOfGram
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi

open Matrix MeasureTheory in
open scoped ENNReal ComplexOrder in
private lemma exists_unitary_fix_proj_of_gram_eq_of_mul_eq_zero {n m : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : Qᴴ = Q)
    (X Y : Matrix (Fin n) (Fin m) ℂ) (h : Xᴴ * X = Yᴴ * Y) (hX : Q * X = 0) (hY : Q * Y = 0) :
    ∃ W : Matrix (Fin n) (Fin n) ℂ, Wᴴ * W = 1 ∧ W * Q = Q ∧ W * X = Y := by
  have hXQ : Xᴴ * Q = 0 := by rw [← hQ, ← conjTranspose_mul, hX, conjTranspose_zero]
  have hYQ : Yᴴ * Q = 0 := by rw [← hQ, ← conjTranspose_mul, hY, conjTranspose_zero]
  have e2 : Xᴴ * Q = Yᴴ * Q := by rw [hXQ, hYQ]
  have e3 : Qᴴ * X = Qᴴ * Y := by rw [hQ, hX, hY]
  have hG : (fromCols X Q)ᴴ * fromCols X Q = (fromCols Y Q)ᴴ * fromCols Y Q := by
    ext (i | i) (j | j)
    · simpa [Matrix.mul_apply] using congrFun (congrFun h i) j
    · simpa [Matrix.mul_apply] using congrFun (congrFun e2 i) j
    · simpa [Matrix.mul_apply] using congrFun (congrFun e3 i) j
    · simp [Matrix.mul_apply]
  obtain ⟨W, hWu, hW⟩ := _root_.GlobalTheory.UnitaryExtension.exists_unitary_mul_eq _ _ hG
  rw [mul_fromCols, fromCols_inj.eq_iff] at hW
  exact ⟨W, hWu, hW.2, hW.1⟩

open Matrix MeasureTheory in
open scoped ENNReal ComplexOrder in

theorem _root_.GlobalTheory.HCXi.exists_unitary_comm_mul_eq_of_gram {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : Hᴴ = H) (hHH : H * H = 1)
    (A B : Matrix (Fin n) (Fin m) ℂ) (h1 : Aᴴ * A = Bᴴ * B) (h2 : Aᴴ * H * A = Bᴴ * H * B) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * H = H * U ∧ U * A = B := by
  obtain ⟨Pp, hPp⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = (1 / 2 : ℂ) • (1 + H) := ⟨_, rfl⟩
  obtain ⟨Pm, hPm⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = (1 / 2 : ℂ) • (1 - H) := ⟨_, rfl⟩
  have hPpH : Ppᴴ = Pp := by simp [hPp, hH, conjTranspose_smul]
  have hPmH : Pmᴴ = Pm := by simp [hPm, hH, conjTranspose_smul]
  have hPpPp : Pp * Pp = Pp := by
    simp only [hPp, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hHH]
    module
  have hPmPm : Pm * Pm = Pm := by
    simp only [hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hHH]
    module
  have hPpPm : Pp * Pm = 0 := by
    simp only [hPp, hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.add_mul,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hHH]
    module
  have hPmPp : Pm * Pp = 0 := by
    simp only [hPp, hPm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.sub_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hHH]
    module
  have hsum : Pp + Pm = 1 := by rw [hPp, hPm]; module
  have hHdec : H = Pp - Pm := by rw [hPp, hPm]; module
  have h2' : Aᴴ * (H * A) = Bᴴ * (H * B) := by simpa only [Matrix.mul_assoc] using h2
  have gramP : ∀ Z : Matrix (Fin n) (Fin m) ℂ,
      (Pp * Z)ᴴ * (Pp * Z) = (1 / 2 : ℂ) • (Zᴴ * Z + Zᴴ * (H * Z)) := by
    intro Z
    rw [conjTranspose_mul, hPpH, Matrix.mul_assoc, ← Matrix.mul_assoc Pp, hPpPp, hPp]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul]
  have gramM : ∀ Z : Matrix (Fin n) (Fin m) ℂ,
      (Pm * Z)ᴴ * (Pm * Z) = (1 / 2 : ℂ) • (Zᴴ * Z - Zᴴ * (H * Z)) := by
    intro Z
    rw [conjTranspose_mul, hPmH, Matrix.mul_assoc, ← Matrix.mul_assoc Pm, hPmPm, hPm]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul]
  obtain ⟨Wp, hWpu, hWpP, hWpA⟩ := exists_unitary_fix_proj_of_gram_eq_of_mul_eq_zero Pm hPmH (Pp * A) (Pp * B)
    (by rw [gramP, gramP, h1, h2']) (by rw [← Matrix.mul_assoc, hPmPp, Matrix.zero_mul])
    (by rw [← Matrix.mul_assoc, hPmPp, Matrix.zero_mul])
  obtain ⟨Wm, hWmu, hWmP, hWmA⟩ := exists_unitary_fix_proj_of_gram_eq_of_mul_eq_zero Pp hPpH (Pm * A) (Pm * B)
    (by rw [gramM, gramM, h1, h2']) (by rw [← Matrix.mul_assoc, hPpPm, Matrix.zero_mul])
    (by rw [← Matrix.mul_assoc, hPpPm, Matrix.zero_mul])
  have hWpHPm : Wpᴴ * Pm = Pm := by rw [← hWpP, ← Matrix.mul_assoc, hWpu, Matrix.one_mul, hWpP]
  have hWmHPp : Wmᴴ * Pp = Pp := by rw [← hWmP, ← Matrix.mul_assoc, hWmu, Matrix.one_mul, hWmP]
  have hPmWp : Pm * Wp = Pm := by
    have := congrArg conjTranspose hWpHPm
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, hPmH] at this
  have hPpWm : Pp * Wm = Pp := by
    have := congrArg conjTranspose hWmHPp
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, hPpH] at this
  have hA : Pp * Wp * Pp = Wp * Pp := calc
    Pp * Wp * Pp = (Pp + Pm) * Wp * Pp - Pm * Wp * Pp := by
      rw [Matrix.add_mul, Matrix.add_mul]; abel
    _ = Wp * Pp := by rw [hsum, Matrix.one_mul, hPmWp, hPmPp, sub_zero]
  have hB : Pm * Wm * Pm = Wm * Pm := calc
    Pm * Wm * Pm = (Pp + Pm) * Wm * Pm - Pp * Wm * Pm := by
      rw [Matrix.add_mul, Matrix.add_mul]; abel
    _ = Wm * Pm := by rw [hsum, Matrix.one_mul, hPpWm, hPpPm, sub_zero]
  have hX1 : Pp * Wpᴴ * Wp = Pp := by rw [Matrix.mul_assoc, hWpu, Matrix.mul_one]
  have hX2 : Pm * Wmᴴ * Wm = Pm := by rw [Matrix.mul_assoc, hWmu, Matrix.mul_one]
  have hX3 : Pp * Wpᴴ * Wm * Pm = 0 := calc
    Pp * Wpᴴ * Wm * Pm = Pp * Wpᴴ * (Pm * Wm * Pm) := by rw [hB, Matrix.mul_assoc (Pp * Wpᴴ)]
    _ = Pp * (Wpᴴ * Pm) * Wm * Pm := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hWpHPm, hPpPm, Matrix.zero_mul, Matrix.zero_mul]
  have hX4 : Pm * Wmᴴ * Wp * Pp = 0 := calc
    Pm * Wmᴴ * Wp * Pp = Pm * Wmᴴ * (Pp * Wp * Pp) := by rw [hA, Matrix.mul_assoc (Pm * Wmᴴ)]
    _ = Pm * (Wmᴴ * Pp) * Wp * Pp := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hWmHPp, hPmPp, Matrix.zero_mul, Matrix.zero_mul]
  refine ⟨Wp * Pp + Wm * Pm, ?_, ?_, ?_⟩
  · simp only [conjTranspose_add, conjTranspose_mul, hPpH, hPmH, Matrix.add_mul, Matrix.mul_add,
      ← Matrix.mul_assoc, hX1, hX2, hX3, hX4, hPpPp, hPmPm]
    rw [add_zero, zero_add, hsum]
  · have hUH : (Wp * Pp + Wm * Pm) * H = Wp * Pp - Wm * Pm := by
      rw [hHdec]
      simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc, hPpPp, hPpPm, hPmPp, hPmPm,
        Matrix.mul_zero]
      abel
    have hHU : H * (Wp * Pp + Wm * Pm) = Wp * Pp - Wm * Pm := by
      rw [hHdec]
      simp only [Matrix.sub_mul, Matrix.mul_add, ← Matrix.mul_assoc, hPpWm, hPmWp, hPpPm, hPmPp,
        hA, hB]
      abel
    rw [hUH, hHU]
  · rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hWpA, hWmA, ← Matrix.add_mul, hsum,
      Matrix.one_mul]

end GlobalTheory.HCXi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FrameIsotropicOrthonormalStatement
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_isotropic_orthonormal : ∀ k r : ℕ, 1 ≤ k → (frame k r)ᴴ * frame k r = 1 ∧ (frame k r)ᴴ * Hpk k r * frame k r = 0 := by
  first | exact @GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic | exact GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic | (intros; apply GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.GramMinorDetTriangularMulStatement
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_minor_det_triangular_mul : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℂ) (u : Matrix (Fin m) (Fin m) ℂ) (j : ℕ) (hj : j ≤ m), u.BlockTriangular id → (((A * u)ᴴ * (A * u)).submatrix (Fin.castLE hj) (Fin.castLE hj)).det = ((∏ b : Fin j, Complex.normSq (u (Fin.castLE hj b) (Fin.castLE hj b)) : ℝ) : ℂ) * ((Aᴴ * A).submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
  first | exact @GlobalTheory.HCXi.det_leading_gram_mul_upperTriangular | exact GlobalTheory.HCXi.det_leading_gram_mul_upperTriangular | (intros; apply GlobalTheory.HCXi.det_leading_gram_mul_upperTriangular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.GramPositiveVolumeContinuousStatement
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_positive_volume_continuous : ∀ k r : ℕ, 1 ≤ k → (∀ g ∈ GV k r, ∀ a : Fin (r + 1), 0 < gram k r g a) ∧ (∀ g ∈ GV k r, 0 < vHalf k r g) ∧ (Measurable fun x : Mt k r => vHalf k r (Matrix.of x)) ∧ ContinuousOn (vHalf k r) (GV k r) := by
  first | exact @GlobalTheory.HCXi.GramPos.gram_vHalf_pos_measurable_continuousOn | exact GlobalTheory.HCXi.GramPos.gram_vHalf_pos_measurable_continuousOn | (intros; apply GlobalTheory.HCXi.GramPos.gram_vHalf_pos_measurable_continuousOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.KsetTransitive
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

namespace GlobalTheory.HCXi

theorem isUnit_det_gram_of_leftInverse {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (L : Matrix (Fin m) (Fin n) ℂ)
    (h : L * A = 1) : IsUnit (Aᴴ * A).det := by
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have h2 := congrArg L.mulVec hxy
    simpa [Matrix.mulVec_mulVec, h] using h2
  have hp : (Aᴴ * A).PosDef := Matrix.PosDef.conjTranspose_mul_self A hinj
  exact (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit

theorem Iwasawa.exists_unitary_comm {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (A B : Matrix (Fin n) (Fin m) ℂ) (h1 : Aᴴ * A = Bᴴ * B) (h2 : Aᴴ * H * A = Bᴴ * H * B) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * H = H * U ∧ U * A = B := by
  set P : Matrix (Fin n) (Fin n) ℂ := (2⁻¹ : ℂ) • (1 + H) with hP
  have hPh : Pᴴ = P := by
    simp [hP, conjTranspose_smul, conjTranspose_add, hH]
  have hPP : P * P = P := by
    simp only [hP, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, one_mul, mul_one, hHH]
    module
  have hHP : H = (2 : ℂ) • P - 1 := by
    simp only [hP]
    module
  have hG : Aᴴ * P * A = Bᴴ * P * B := by
    simp only [hP, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1, h2]
  clear_value P
  have hQh : (1 - P)ᴴ = 1 - P := by simp [hPh]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    simp only [mul_sub, sub_mul, one_mul, mul_one, hPP, sub_self, sub_zero]
  have hG' : Aᴴ * (1 - P) * A = Bᴴ * (1 - P) * B := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, hG]
  have key : ∀ E : Matrix (Fin n) (Fin n) ℂ, Eᴴ = E → E * E = E → Aᴴ * E * A = Bᴴ * E * B →
      ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * E = E * U ∧ U * (1 - E) = 1 - E ∧ U * (E * A) = E * B := by
    intro E hE hEE hg
    have e : ∀ C : Matrix (Fin n) (Fin m) ℂ, (E * C)ᴴ * (E * C) = Cᴴ * E * C := by
      intro C
      rw [conjTranspose_mul, hE, Matrix.mul_assoc, ← Matrix.mul_assoc E E, hEE, Matrix.mul_assoc]
    refine GlobalTheory.UnitaryExtension.exists_unitary_of_gram_eq n m E (E * A) (E * B) hE hEE ?_ ?_ ?_
    · rw [← Matrix.mul_assoc, hEE]
    · rw [← Matrix.mul_assoc, hEE]
    · rw [e, e, hg]
  obtain ⟨U, hU1, hU2, hU3, hU4⟩ := key P hPh hPP hG
  obtain ⟨V, hV1, hV2, hV3, hV4⟩ := key (1 - P) hQh hQQ hG'
  rw [sub_sub_cancel] at hV3
  have hV5 : V * P = P * V := by
    have := hV2
    simp only [mul_sub, sub_mul, one_mul, mul_one] at this
    exact sub_right_injective this
  refine ⟨U * V, ?_, ?_, ?_⟩
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU1, Matrix.one_mul, hV1]
  · have : U * V * P = P * (U * V) := by
      rw [mul_assoc, hV5, ← mul_assoc, hU2, mul_assoc]
    rw [hHP]
    simp only [mul_sub, sub_mul, one_mul, mul_one, mul_smul_comm, smul_mul_assoc, this]
  · have hA : A = P * A + (1 - P) * A := by
      rw [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
    have hB : B = P * B + (1 - P) * B := by
      rw [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
    calc U * V * A = U * (V * (P * A + (1 - P) * A)) := by rw [← hA, Matrix.mul_assoc]
      _ = U * (P * A + (1 - P) * B) := by
        rw [Matrix.mul_add, hV4, ← Matrix.mul_assoc V P, hV3]
      _ = P * B + (1 - P) * B := by
        rw [Matrix.mul_add, hU4, ← Matrix.mul_assoc U (1 - P), hU3]
      _ = B := hB.symm

theorem Iwasawa.kset_transitive : ∀ (k r m : ℕ) (A B : Matrix (Fin (2 * r + k + 1)) (Fin m) ℂ),
    Aᴴ * A = Bᴴ * B → Aᴴ * Hpk k r * A = Bᴴ * Hpk k r * B → ∃ κ ∈ Kset k r, κ * A = B := by
  intro k r m A B h1 h2
  have hF := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  obtain ⟨U, hU1, hU2, hU3⟩ := Iwasawa.exists_unitary_comm (Hpk k r) hF.1 hF.2.1 A B h1 h2
  refine ⟨U, ⟨?_, hU1⟩, hU3⟩
  show Uᴴ * Hpk k r * U = Hpk k r
  rw [Matrix.mul_assoc, ← hU2, ← Matrix.mul_assoc, hU1, Matrix.one_mul]

theorem iwasawa : ∀ k r : ℕ, 1 ≤ k → ∀ g ∈ GV k r, ∃ κ ∈ Kset k r, ∃ p ∈ Pset k r, g = κ * p := by
  intro k r hk g hg
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  obtain ⟨hF1, hF0⟩ := FrameOrth.frame_orthonormal_isotropic k r hk
  obtain ⟨-, -, hH, hK, -⟩ := KGroup.kset_facts k r
  have hHH : (Hpk k r)ᴴ * Hpk k r = 1 := hH.2
  have hL : ((frame k r)ᴴ * (Hpk k r)ᴴ * gᴴ * Hpk k r) * (g * frame k r) = 1 := by
    calc ((frame k r)ᴴ * (Hpk k r)ᴴ * gᴴ * Hpk k r) * (g * frame k r)
        = (frame k r)ᴴ * ((Hpk k r)ᴴ * (gᴴ * Hpk k r * g)) * frame k r := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hHH, Matrix.mul_one, hF1]
  obtain ⟨Q, u, hQ, hu, hud, hA⟩ := GlobalTheory.QRDecomp.exists_qr _ _ (g * frame k r)
    (isUnit_det_gram_of_leftInverse _ _ hL)
  have hQA : Q = g * frame k r * u⁻¹ := by
    rw [hA, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hud, Matrix.mul_one]
  have hQ0 : Qᴴ * Hpk k r * Q = 0 := by
    calc Qᴴ * Hpk k r * Q
        = (u⁻¹)ᴴ * ((frame k r)ᴴ * (gᴴ * Hpk k r * g) * frame k r) * u⁻¹ := by
          rw [hQA]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hg', hF0, Matrix.mul_zero, Matrix.zero_mul]
  obtain ⟨κ, hκ, hκF⟩ := Iwasawa.kset_transitive k r (r + 1) (frame k r) Q (by rw [hF1, hQ]) (by rw [hF0, hQ0])
  have hκ1 : κᴴ * κ = 1 := hκ.2
  have hκ2 : κ * κᴴ = 1 := mul_eq_one_comm.1 hκ1
  have hκs : κᴴᴴ * Hpk k r * κᴴ = Hpk k r := (hK κ hκ).1.1
  refine ⟨κ, hκ, κᴴ * g, ⟨?_, u, hu, ?_⟩, ?_⟩
  · show (κᴴ * g)ᴴ * Hpk k r * (κᴴ * g) = Hpk k r
    calc (κᴴ * g)ᴴ * Hpk k r * (κᴴ * g) = gᴴ * (κᴴᴴ * Hpk k r * κᴴ) * g := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r := by rw [hκs, hg']
  · rw [Matrix.mul_assoc, hA, ← hκF, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hκ1, Matrix.one_mul]
  · rw [← Matrix.mul_assoc, hκ2, Matrix.one_mul]

end GlobalTheory.HCXi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.LintegralHyperboloidFibrationStatement
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_hyperboloid_fibration : ∀ (k : ℕ) (ψ : (Fin (k + 1) → ℂ) → ℝ≥0∞) (F : ℝ → ℝ≥0∞), Measurable ψ → Measurable F → (∫⁻ v : Fin (k + 1) → ℂ in {v | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))}, F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) * ψ v) = (1 / 2 : ℝ≥0∞) * ∫⁻ τ : ℝ in Set.Ioi 0, F τ * ∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ψ (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))) := by
  first | exact @GlobalTheory.HCXi.lintegral_cone_polar | exact GlobalTheory.HCXi.lintegral_cone_polar | (intros; apply GlobalTheory.HCXi.lintegral_cone_polar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MaximalCompactSubgroupPropertiesStatement
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximal_compact_subgroup_properties : ∀ k r : ℕ, IsClosedSubgroup (Kset k r) ∧ IsCompact (Kset k r) ∧ Hpk k r ∈ Kset k r ∧ (∀ κ ∈ Kset k r, κᴴ ∈ Kset k r ∧ κ * Hpk k r = Hpk k r * κ) ∧ ∀ κ ∈ Kset k r, ∀ κ' ∈ Kset k r, ∀ g : Mat k r, gN (κ * g * κ') = gN g := by
  first | exact @GlobalTheory.HCXi.KGroup.kset_facts | exact GlobalTheory.HCXi.KGroup.kset_facts | (intros; apply GlobalTheory.HCXi.KGroup.kset_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ParabolicLineStabilizerLeviStatement
section
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_line_stabilizer_levi : ∀ (k r' : ℕ) (a : ℂ), ∀ p ∈ GV k (1 + r'), p *ᵥ e0 k r' = a • e0 k r' → a ≠ 0 ∧ ∃ g₁ ∈ GV k r', ∀ w : Fin (2 * r' + k + 1) → ℂ, ∃ c : ℂ, p *ᵥ liftVec k 1 r' w = liftVec k 1 r' (g₁ *ᵥ w) + c • e0 k r' := by
  first | exact @GlobalTheory.HCXi.LineStabiliser.acts_through_level_one | exact GlobalTheory.HCXi.LineStabiliser.acts_through_level_one | (intros; apply GlobalTheory.HCXi.LineStabiliser.acts_through_level_one <;> assumption)
end

