import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.BoundsY
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCBounds

open Matrix

noncomputable section

def entrySum {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : ℝ := ∑ j, ∑ k, |A j k|

theorem entrySum_nonneg {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : 0 ≤ entrySum A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem dot_self_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem mul_self_le_dot {ι : Type*} [Fintype ι] (x : ι → ℝ) (j : ι) : x j * x j ≤ x ⬝ᵥ x :=
  Finset.single_le_sum (f := fun i => x i * x i) (fun i _ => mul_self_nonneg (x i))
    (Finset.mem_univ j)

theorem abs_mul_le_dot {ι : Type*} [Fintype ι] (x : ι → ℝ) (j k : ι) :
    |x j| * |x k| ≤ x ⬝ᵥ x := by
  have hj := mul_self_le_dot x j
  have hk := mul_self_le_dot x k
  nlinarith [abs_mul_abs_self (x j), abs_mul_abs_self (x k), sq_nonneg (|x j| - |x k|)]

theorem abs_quad_le {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    |x ⬝ᵥ (A *ᵥ x)| ≤ entrySum A * (x ⬝ᵥ x) := by
  have h : x ⬝ᵥ (A *ᵥ x) = ∑ j, ∑ k, x j * A j k * x k := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [h, entrySum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul]
  calc |x j| * |A j k| * |x k| = |A j k| * (|x j| * |x k|) := by ring
    _ ≤ |A j k| * (x ⬝ᵥ x) := mul_le_mul_of_nonneg_left (abs_mul_le_dot x j k) (abs_nonneg _)

theorem quad_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (A : κ → Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ ((∑ j ∈ s, A j) *ᵥ x) = ∑ j ∈ s, x ⬝ᵥ (A j *ᵥ x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_mulVec, dotProduct_add, ih]

theorem quad_smul_one_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (l : ℝ)
    (x : ι → ℝ) : x ⬝ᵥ ((l • (1 : Matrix ι ι ℝ) - A) *ᵥ x) = l * (x ⬝ᵥ x) - x ⬝ᵥ (A *ᵥ x) := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

theorem quad_sub_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (l : ℝ)
    (x : ι → ℝ) : x ⬝ᵥ ((A - l • (1 : Matrix ι ι ℝ)) *ᵥ x) = x ⬝ᵥ (A *ᵥ x) - l * (x ⬝ᵥ x) := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

theorem posSemidef_of_real {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hs : Aᵀ = A)
    (h : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x)) : A.PosSemidef :=
  PosSemidef.of_dotProduct_mulVec_nonneg
    ((conjTranspose_eq_transpose_of_trivial A).trans hs) (by simpa using h)

theorem quad_nonneg {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (x : ι → ℝ) : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
  simpa using hA.dotProduct_mulVec_nonneg x

theorem transpose_of_posSemidef {ι : Type*} {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : Aᵀ = A :=
  (conjTranspose_eq_transpose_of_trivial A).symm.trans hA.isHermitian

theorem quad_symm {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hs : Aᵀ = A) (u v : ι → ℝ) :
    v ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ v) := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hs]

theorem quad_cs {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (u v : ι → ℝ) :
    (u ⬝ᵥ (A *ᵥ v)) ^ 2 ≤ (u ⬝ᵥ (A *ᵥ u)) * (v ⬝ᵥ (A *ᵥ v)) := by
  have hvu := quad_symm (transpose_of_posSemidef hA) u v
  have key : ∀ t : ℝ, 0 ≤ (v ⬝ᵥ (A *ᵥ v)) * (t * t) + (2 * (u ⬝ᵥ (A *ᵥ v))) * t +
      u ⬝ᵥ (A *ᵥ u) := by
    intro t
    have h := quad_nonneg hA (u + t • v)
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hvu] at h
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

theorem posDef_of_ge {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (h : (A - c • (1 : Matrix ι ι ℝ)).PosSemidef) : A.PosDef := by
  have hs : Aᵀ = A := by
    have := transpose_of_posSemidef h
    rw [transpose_sub, transpose_smul, transpose_one] at this
    exact sub_left_injective this
  refine posDef_iff_dotProduct_mulVec.mpr ⟨(conjTranspose_eq_transpose_of_trivial A).trans hs,
    fun x hx => ?_⟩
  have h1 := quad_nonneg h x
  rw [quad_sub_smul_one] at h1
  have h2 : 0 < x ⬝ᵥ x := by
    rcases (dot_self_nonneg x).lt_or_eq with h3 | h3
    · exact h3
    · exact absurd (dotProduct_self_eq_zero.mp h3.symm) hx
  simpa using (by nlinarith : 0 < x ⬝ᵥ (A *ᵥ x))

theorem inv_le_of_ge {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (h : (A - c • (1 : Matrix ι ι ℝ)).PosSemidef) :
    (c⁻¹ • (1 : Matrix ι ι ℝ) - A⁻¹).PosSemidef := by
  have hA : A.PosDef := posDef_of_ge hc h
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hs : Aᵀ = A := transpose_of_posSemidef hA.posSemidef
  refine posSemidef_of_real ?_ fun x => ?_
  · rw [transpose_sub, transpose_smul, transpose_one, transpose_nonsing_inv, hs]
  · rw [quad_smul_one_sub]
    set y := A⁻¹ *ᵥ x with hy
    have hx : A *ᵥ y = x := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have h1 : c * (y ⬝ᵥ y) ≤ x ⬝ᵥ y := by
      have := quad_nonneg h y
      rw [quad_sub_smul_one, hx, dotProduct_comm] at this
      linarith
    have h3 : 0 ≤ (x - c • y) ⬝ᵥ (x - c • y) := dot_self_nonneg _
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm y x] at h3
    have key : c * (x ⬝ᵥ y) ≤ x ⬝ᵥ x := by nlinarith
    have := mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hc.le)
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at this
    linarith

theorem inv_ge_of_le {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {l : ℝ}
    (hl : 0 < l) (hA : A.PosDef) (h : (l • (1 : Matrix ι ι ℝ) - A).PosSemidef) :
    (A⁻¹ - l⁻¹ • (1 : Matrix ι ι ℝ)).PosSemidef := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hs : Aᵀ = A := transpose_of_posSemidef hA.posSemidef
  refine posSemidef_of_real ?_ fun x => ?_
  · rw [transpose_sub, transpose_smul, transpose_one, transpose_nonsing_inv, hs]
  · rw [quad_sub_smul_one]
    set y := A⁻¹ *ᵥ x with hy
    have hx : A *ᵥ y = x := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have hcs := quad_cs hA.posSemidef y x
    have e1 : y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ x := by rw [← quad_symm hs, hx]
    have e2 : y ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y := by rw [hx, dotProduct_comm]
    rw [e1, e2] at hcs
    have hxy : 0 ≤ x ⬝ᵥ y := e2 ▸ quad_nonneg hA.posSemidef y
    have hlx : x ⬝ᵥ (A *ᵥ x) ≤ l * (x ⬝ᵥ x) := by
      have := quad_nonneg h x
      rw [quad_smul_one_sub] at this
      linarith
    have hxx := dot_self_nonneg x
    rcases hxx.lt_or_eq with hpos | hzero
    · have h4 : (x ⬝ᵥ x) * (x ⬝ᵥ x) ≤ (l * (x ⬝ᵥ y)) * (x ⬝ᵥ x) := by
        nlinarith [mul_le_mul_of_nonneg_left hlx hxy]
      have h5 : x ⬝ᵥ x ≤ l * (x ⬝ᵥ y) := le_of_mul_le_mul_right h4 hpos
      have := mul_le_mul_of_nonneg_left h5 (inv_nonneg.mpr hl.le)
      rw [← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul] at this
      linarith
    · rw [← hzero]; simpa using hxy

open scoped ComplexOrder in

theorem posSemidef_map_ofReal {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (A.map (fun x : ℝ => (x : ℂ))).PosSemidef := by
  have hs : ∀ j k, A k j = A j k := fun j k => by
    simpa using congrFun (congrFun (transpose_of_posSemidef hA) j) k
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun w => ?_
  · ext j k
    simp [conjTranspose_apply, hs]
  · set a : ι → ℝ := fun k => (w k).re
    set b : ι → ℝ := fun k => (w k).im
    have ha := quad_nonneg hA a
    have hb := quad_nonneg hA b
    have hre : (star w ⬝ᵥ (A.map (fun x : ℝ => (x : ℂ)) *ᵥ w)).re =
        a ⬝ᵥ (A *ᵥ a) + b ⬝ᵥ (A *ᵥ b) := by
      simp only [dotProduct, mulVec, map_apply, Pi.star_apply, Complex.re_sum, Complex.mul_re,
        Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im, a, b, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    have him : (star w ⬝ᵥ (A.map (fun x : ℝ => (x : ℂ)) *ᵥ w)).im = 0 := by
      have e : (star w ⬝ᵥ (A.map (fun x : ℝ => (x : ℂ)) *ᵥ w)).im =
          ∑ j, ∑ k, (w j).re * (A j k * (w k).im) - ∑ j, ∑ k, (w j).im * (A j k * (w k).re) := by
        simp only [dotProduct, mulVec, map_apply, Pi.star_apply, Complex.mul_im, Complex.mul_re,
          Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.im_sum, Complex.ofReal_re,
          Complex.ofReal_im, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
      have hsw : ∑ j, ∑ k, (w j).re * (A j k * (w k).im) =
          ∑ j, ∑ k, (w j).im * (A j k * (w k).re) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [hs]; ring
      rw [e, hsw, sub_self]
    exact Complex.nonneg_iff.mpr ⟨hre ▸ add_nonneg ha hb, him.symm⟩

end

end GroundTheory.Heights₂.Heights.MCBounds
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCDet

open Matrix
open scoped MatrixOrder ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

theorem det_eq_ofReal_re {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A.det = (RCLike.re A.det : 𝕜) := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod, RCLike.ofReal_re]

theorem re_det_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) : 0 ≤ RCLike.re A.det := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod, RCLike.ofReal_re]
  exact Finset.prod_nonneg fun i _ => hA.eigenvalues_nonneg i

theorem re_det_pos {A : Matrix n n 𝕜} (hA : A.PosDef) : 0 < RCLike.re A.det := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod, RCLike.ofReal_re]
  exact Finset.prod_pos fun i _ => hA.eigenvalues_pos i

theorem one_le_re_det_one_add {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) :
    1 ≤ RCLike.re (1 + Q).det := by
  have hspec := hQ.isHermitian.spectral_theorem
  set U := hQ.isHermitian.eigenvectorUnitary
  have hUU : (U : Matrix n n 𝕜) * star (U : Matrix n n 𝕜) = 1 := Unitary.coe_mul_star_self U
  have h1 : 1 + Q = (U : Matrix n n 𝕜) *
      ((1 : Matrix n n 𝕜) + diagonal (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues)) *
        star (U : Matrix n n 𝕜) := by
    conv_lhs => rw [hspec]
    rw [Unitary.conjStarAlgAut_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU]
  have hdet : (1 + Q).det =
      ((1 : Matrix n n 𝕜) + diagonal (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues)).det := by
    rw [h1, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul,
      Unitary.coe_star_mul_self, det_one, one_mul]
  rw [hdet, ← diagonal_one, diagonal_add, det_diagonal]
  have : ∏ i, ((1 : 𝕜) + (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues) i) =
      ((∏ i, (1 + hQ.isHermitian.eigenvalues i) : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp
  rw [this, RCLike.ofReal_re]
  exact Finset.one_le_prod fun i _ => by linarith [hQ.eigenvalues_nonneg i]

theorem re_det_le_re_det_add {A P : Matrix n n 𝕜} (hA : A.PosSemidef) (hP : P.PosSemidef) :
    RCLike.re A.det ≤ RCLike.re (A + P).det := by
  by_cases h0 : A.det = 0
  · rw [h0, map_zero]
    exact re_det_nonneg (hA.add hP)
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [star_eq_conjTranspose] at hB
  have hBdet : B.det ≠ 0 := by
    intro hb
    apply h0
    rw [hB, det_mul, hb, mul_zero]
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hBHu : IsUnit Bᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hBdet)
  set Q := (B⁻¹)ᴴ * P * B⁻¹ with hQdef
  have hQ : Q.PosSemidef := by
    have := hP.mul_mul_conjTranspose_same ((B⁻¹)ᴴ)
    simpa [hQdef, conjTranspose_conjTranspose] using this
  have hAP : A + P = Bᴴ * (1 + Q) * B := by
    rw [hQdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← hB]
    congr 1
    rw [conjTranspose_nonsing_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hBHu, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBu, Matrix.mul_one]
  have hdet : (A + P).det = A.det * (1 + Q).det := by
    rw [hAP, hB, det_mul, det_mul, det_mul]
    ring
  have h1 := one_le_re_det_one_add hQ
  have h2 := re_det_nonneg hA
  obtain ⟨a, ha⟩ : ∃ a : ℝ, A.det = a := ⟨_, det_eq_ofReal_re hA⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, (1 + Q).det = b := ⟨_, det_eq_ofReal_re (PosSemidef.one.add hQ)⟩
  rw [hdet, ha, hb, ← RCLike.ofReal_mul]
  simp only [RCLike.ofReal_re]
  rw [ha, RCLike.ofReal_re] at h2
  rw [hb, RCLike.ofReal_re] at h1
  nlinarith

theorem re_det_mono {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hAB : (B - A).PosSemidef) :
    RCLike.re A.det ≤ RCLike.re B.det := by
  have := re_det_le_re_det_add hA hAB
  rwa [add_sub_cancel] at this

theorem log_re_det_le {A : Matrix n n 𝕜} (hA : A.PosDef) :
    Real.log (RCLike.re A.det) ≤ RCLike.re A.trace - Fintype.card n := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, hA.isHermitian.trace_eq_sum_eigenvalues,
    ← RCLike.ofReal_prod, ← RCLike.ofReal_sum, RCLike.ofReal_re, RCLike.ofReal_re,
    Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne')]
  have : (Fintype.card n : ℝ) = ∑ _i : n, (1 : ℝ) := by simp
  rw [this, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i)

theorem norm_det_mul_sq_le (A B : Matrix m n 𝕜) :
    ‖(Bᴴ * A).det‖ ^ 2 ≤ RCLike.re (Bᴴ * B).det * RCLike.re (Aᴴ * A).det := by
  have hG := posSemidef_conjTranspose_mul_self A
  have hBB := posSemidef_conjTranspose_mul_self B
  by_cases h0 : (Aᴴ * A).det = 0
  · obtain ⟨x, hx0, hx⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have hAx : A *ᵥ x = 0 := by
      have h := congrArg (fun v => star x ⬝ᵥ v) hx
      simp only [dotProduct_zero] at h
      rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose] at h
      simp only [star_star] at h
      exact dotProduct_star_self_eq_zero.mp h
    have hC : (Bᴴ * A).det = 0 :=
      exists_mulVec_eq_zero_iff.mp ⟨x, hx0, by rw [← mulVec_mulVec, hAx, mulVec_zero]⟩
    rw [hC, h0, norm_zero, map_zero]
    simp
  · have hGpd : (Aᴴ * A).PosDef := hG.posDef_iff_det_ne_zero.mpr h0
    set G := Aᴴ * A with hGdef
    set C := Bᴴ * A with hCdef
    have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr h0
    have hGiG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hGu
    have hGiH : (G⁻¹)ᴴ = G⁻¹ := by
      rw [conjTranspose_nonsing_inv, hGpd.isHermitian.eq]
    have hCH : Cᴴ = Aᴴ * B := by
      rw [hCdef, conjTranspose_mul, conjTranspose_conjTranspose]
    set E := B - A * (G⁻¹ * Cᴴ) with hEdef
    have hcancel : ∀ Z : Matrix n n 𝕜, G⁻¹ * (Aᴴ * (A * Z)) = Z := by
      intro Z
      rw [← Matrix.mul_assoc Aᴴ, ← Matrix.mul_assoc, ← hGdef, hGiG, Matrix.one_mul]
    have hEE : Bᴴ * B = C * G⁻¹ * Cᴴ + Eᴴ * E := by
      rw [hEdef, hCH]
      simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, hGiH]
      rw [hCdef]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hcancel]
      abel
    have hPSD1 : (C * G⁻¹ * Cᴴ).PosSemidef := hGpd.inv.posSemidef.mul_mul_conjTranspose_same C
    have hPSD2 : (Eᴴ * E).PosSemidef := posSemidef_conjTranspose_mul_self E
    have hle := re_det_le_re_det_add hPSD1 hPSD2
    rw [← hEE] at hle
    have hg := re_det_pos hGpd
    have hdetC : (C * G⁻¹ * Cᴴ).det = ((‖C.det‖ ^ 2 * (RCLike.re G.det)⁻¹ : ℝ) : 𝕜) := by
      rw [det_mul, det_mul, det_conjTranspose, det_nonsing_inv, Ring.inverse_eq_inv',
        det_eq_ofReal_re hG, mul_comm (C.det), mul_assoc, RCLike.star_def, RCLike.mul_conj]
      push_cast
      ring
    rw [hdetC, RCLike.ofReal_re] at hle
    rw [← div_eq_mul_inv, div_le_iff₀ hg] at hle
    exact hle

theorem norm_det_mul_sq_le_of_posDef [DecidableEq m] {M : Matrix m m 𝕜} (hM : M.PosDef)
    (F W : Matrix m n 𝕜) :
    ‖(Wᴴ * F).det‖ ^ 2 ≤ RCLike.re (Wᴴ * M * W).det * RCLike.re (Fᴴ * M⁻¹ * F).det := by
  obtain ⟨L, hL⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.posSemidef.nonneg
  rw [star_eq_conjTranspose] at hL
  have hLdet : L.det ≠ 0 := by
    intro hl
    have := hM.det_pos.ne'
    rw [hL, det_mul, hl, mul_zero] at this
    exact this rfl
  have hLu : IsUnit L.det := isUnit_iff_ne_zero.mpr hLdet
  have hLHu : IsUnit Lᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hLdet)
  have h := norm_det_mul_sq_le ((Lᴴ)⁻¹ * F) (L * W)
  have e1 : (L * W)ᴴ * ((Lᴴ)⁻¹ * F) = Wᴴ * F := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Lᴴ,
      Matrix.mul_nonsing_inv _ hLHu, Matrix.one_mul]
  have e2 : (L * W)ᴴ * (L * W) = Wᴴ * M * W := by
    rw [conjTranspose_mul, hL, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  have e3 : ((Lᴴ)⁻¹ * F)ᴴ * ((Lᴴ)⁻¹ * F) = Fᴴ * M⁻¹ * F := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, conjTranspose_conjTranspose, hL,
      Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc L⁻¹]
  rw [e1, e2, e3] at h
  exact h

end GroundTheory.Heights₂.Heights.MCDet
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.HermValueIsLeast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCSchur

open Matrix

noncomputable section

def qf {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (u : ι → ℝ) : ℝ := u ⬝ᵥ (A *ᵥ u)

theorem hermValue_eq_qf {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (w : ι → ℂ) :
    hermValue A w = qf A (fun k => (w k).re) + qf A (fun k => (w k).im) := by
  simp only [hermValue, hermPair, qf, dotProduct, mulVec, Matrix.map_apply, Complex.re_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  ring

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem inv_toBlocks₂₂_eq (Y : Matrix (m ⊕ n) (m ⊕ n) ℝ) (hY : IsUnit Y.det)
    (hA : IsUnit (Y⁻¹).toBlocks₁₁.det) :
    (Y.toBlocks₂₂)⁻¹ = (Y⁻¹).toBlocks₂₂ - (Y⁻¹).toBlocks₂₁ * ((Y⁻¹).toBlocks₁₁)⁻¹ * (Y⁻¹).toBlocks₁₂ := by
  set Z := Y⁻¹ with hZ
  have hYZ : Y * Z = 1 := Matrix.mul_nonsing_inv Y hY
  rw [← fromBlocks_toBlocks Y, ← fromBlocks_toBlocks Z, fromBlocks_multiply, ← fromBlocks_one,
    fromBlocks_inj] at hYZ
  obtain ⟨-, -, h21, h22⟩ := hYZ
  apply Matrix.inv_eq_right_inv
  have e : Y.toBlocks₂₁ = -(Y.toBlocks₂₂ * Z.toBlocks₂₁) * (Z.toBlocks₁₁)⁻¹ := by
    have := congrArg (· * (Z.toBlocks₁₁)⁻¹) h21
    simp only [Matrix.add_mul, Matrix.zero_mul] at this
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ hA] at this
    rw [Matrix.neg_mul]
    exact eq_neg_of_add_eq_zero_left this
  rw [Matrix.mul_sub, ← h22, e]
  simp only [Matrix.neg_mul, Matrix.mul_assoc]
  abel

theorem qf_isLeast (Y : Matrix (m ⊕ n) (m ⊕ n) ℝ) (hY : Y.PosDef) (c : n → ℝ) :
    IsLeast (Set.range fun a : m → ℝ => qf Y⁻¹ (Sum.elim a c)) (qf (Y.toBlocks₂₂)⁻¹ c) := by
  have hZ : (Y⁻¹).PosDef := hY.inv
  set Z := Y⁻¹ with hZdef
  have hA : (Z.toBlocks₁₁).PosDef := hZ.submatrix Sum.inl_injective
  have hAu : IsUnit (Z.toBlocks₁₁).det := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have : Invertible Z.toBlocks₁₁ := hA.isUnit.invertible
  have h21 : Z.toBlocks₂₁ = (Z.toBlocks₁₂)ᴴ := by
    ext i j
    have := congrFun (congrFun hZ.1 (Sum.inr i)) (Sum.inl j)
    simpa [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.conjTranspose_apply] using this.symm
  have hZeq : Z = fromBlocks Z.toBlocks₁₁ Z.toBlocks₁₂ (Z.toBlocks₁₂)ᴴ Z.toBlocks₂₂ := by
    rw [← h21, fromBlocks_toBlocks]
  have hS : (Y.toBlocks₂₂)⁻¹ = Z.toBlocks₂₂ - (Z.toBlocks₁₂)ᴴ * (Z.toBlocks₁₁)⁻¹ * Z.toBlocks₁₂ := by
    rw [inv_toBlocks₂₂_eq Y ((Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit) hAu, h21]
  have key : ∀ a : m → ℝ, qf Z (Sum.elim a c) =
      qf Z.toBlocks₁₁ (a + ((Z.toBlocks₁₁)⁻¹ * Z.toBlocks₁₂) *ᵥ c) + qf (Y.toBlocks₂₂)⁻¹ c := by
    intro a
    have := schur_complement_eq₁₁ (A := Z.toBlocks₁₁) Z.toBlocks₁₂ Z.toBlocks₂₂ a c hA.1
    simp only [star_trivial] at this
    rw [hS, qf, qf, qf, dotProduct_mulVec, dotProduct_mulVec, dotProduct_mulVec, ← this, ← hZeq]
  refine ⟨⟨-(((Z.toBlocks₁₁)⁻¹ * Z.toBlocks₁₂) *ᵥ c), ?_⟩, ?_⟩
  · simp only
    rw [key, neg_add_cancel]
    simp [qf]
  · rintro _ ⟨a, rfl⟩
    simp only
    rw [key]
    have := hA.posSemidef.dotProduct_mulVec_nonneg (a + ((Z.toBlocks₁₁)⁻¹ * Z.toBlocks₁₂) *ᵥ c)
    simp only [star_trivial] at this
    unfold qf
    linarith

theorem hermValue_isLeast (Y : Matrix (m ⊕ n) (m ⊕ n) ℝ) (hY : Y.PosDef) (v : n → ℂ) :
    IsLeast (Set.range fun x : m → ℂ => hermValue Y⁻¹ (Sum.elim x v))
      (hermValue (Y.toBlocks₂₂)⁻¹ v) := by
  have hre := qf_isLeast Y hY (fun k => (v k).re)
  have him := qf_isLeast Y hY (fun k => (v k).im)
  have split : ∀ x : m → ℂ, hermValue Y⁻¹ (Sum.elim x v) =
      qf Y⁻¹ (Sum.elim (fun k => (x k).re) (fun k => (v k).re)) +
        qf Y⁻¹ (Sum.elim (fun k => (x k).im) (fun k => (v k).im)) := by
    intro x
    rw [hermValue_eq_qf]
    congr 2 <;> ext k <;> cases k <;> rfl
  obtain ⟨⟨a, ha⟩, hlre⟩ := hre
  obtain ⟨⟨b, hb⟩, hlim⟩ := him
  refine ⟨⟨fun k => ⟨a k, b k⟩, ?_⟩, ?_⟩
  · simp only at ha hb ⊢
    rw [split, hermValue_eq_qf]
    exact congrArg₂ (· + ·) ha hb
  · rintro _ ⟨x, rfl⟩
    simp only
    rw [split, hermValue_eq_qf]
    exact add_le_add (hlre ⟨_, rfl⟩) (hlim ⟨_, rfl⟩)

theorem schurQuotient : SchurQuotient.Statement := fun _ _ Y hY v => hermValue_isLeast Y hY v

end

end GroundTheory.Heights₂.Heights.MCSchur
end

