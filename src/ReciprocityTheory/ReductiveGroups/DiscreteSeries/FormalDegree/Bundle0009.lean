import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0008
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0006
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0007
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacBaseA

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FiPmatEqFiOneSmulPmat
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem wS_nonneg' {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n)
    (S : {S : Finset (Fin n) // S.card = i}) : 0 ≤ wS z hi S := by
  unfold wS
  positivity

theorem fi_eq_lse {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) (t : ℝ) :
    Fi ((t : ℂ) • pmat z) i = Real.log (∑ S, wS z hi S * Real.exp (t * yS z S.1)) := by
  unfold Fi
  rw [lemma3a z hi t]
  congr 1
  have h : (∑ S, ((wS z hi S : ℝ) : ℂ) * Complex.exp ((t * yS z S.1 : ℝ) : ℂ)) =
      ((∑ S, wS z hi S * Real.exp (t * yS z S.1) : ℝ) : ℂ) := by
    push_cast
    simp only [Complex.ofReal_exp, Complex.ofReal_mul]
  rw [h, Complex.ofReal_re]

theorem fi_pmat_eq_fi_one_smul_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) (i : ℕ) :
    Fi (pmat z) i = Fi (((1 : ℝ) : ℂ) • pmat z) i := by
  rw [Complex.ofReal_one, one_smul]

theorem fi_convex {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) :
    ConvexOn ℝ Set.univ (fun t : ℝ => Fi ((t : ℂ) • pmat z) i) := by
  have h : (fun t : ℝ => Fi ((t : ℂ) • pmat z) i) =
      fun t : ℝ => Real.log (∑ S, wS z hi S * Real.exp (t * yS z S.1)) := by
    funext t
    exact fi_eq_lse z hi t
  rw [h]
  exact lse_convexOn (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi)

theorem fi_zero (i : ℕ) : Fi (0 : Matrix (Fin n) (Fin n) ℂ) i = 0 := by
  unfold Fi Del
  rw [NormedSpace.exp_zero]
  split_ifs with h
  · rw [Matrix.submatrix_one _ (Fin.castLE_injective h)]
    simp
  · simp

theorem fi_nonneg {ε : Fin n → Bool} (z : PCoord ε → ℂ) (i : ℕ) : 0 ≤ Fi (pmat z) i := by
  by_cases hi : i ≤ n
  · rw [fi_pmat_eq_fi_one_smul_pmat, fi_eq_lse z hi]
    apply Real.log_nonneg
    have h := lse_one_le (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi) (lemma3c z hi)
    simpa only [one_mul] using h
  · unfold Fi Del
    rw [dif_neg hi]
    simp

theorem fi_lower {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) {ep : ℝ}
    (h1 : rhoP z ≤ ep) (h2 : ep ≤ 1) : Vi (pmat z) i / 2 * (1 - ep) ≤ Fi (pmat z) i := by
  have hr : 0 ≤ rhoP z := by
    unfold rhoP
    positivity
  rw [fi_pmat_eq_fi_one_smul_pmat, fi_eq_lse z hi, ← lemma3d z hi]
  have h := lse_lower (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi) (lemma3c z hi)
    (hr.trans h1) h2 (fun S => by
      have := abs_sum_pev_le z S.1
      unfold yS
      linarith)
  simpa only [one_mul] using h

theorem fi_upper {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) (h1 : rhoP z ≤ 1) :
    Fi (pmat z) i ≤ Vi (pmat z) i := by
  rw [fi_pmat_eq_fi_one_smul_pmat, fi_eq_lse z hi, ← lemma3d z hi]
  have h := lse_upper (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi) (lemma3c z hi)
    (fun S => by
      have := abs_sum_pev_le z S.1
      unfold yS
      linarith)
  simpa only [one_mul] using h

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacBase
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem actR_contDiff {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ContDiff ℝ 1 (actR (ε := ε) g) := by
  open Matrix.Norms.Operator in
  (refine contDiff_iff_contDiffAt.mpr fun z => ?_
   have hf := JacB.contDiffAt_of_exp (𝔸 := Matrix (Fin n) (Fin n) ℂ)
     (f := fun w => (2 : ℝ) • pmat (actR (ε := ε) g w)) (z := z)
     (((JacB.pmat_contDiff ε).continuous.comp (JacB.actR_continuous hg)).const_smul
       (2 : ℝ)).continuousAt
     (by
       refine ContDiffAt.congr_of_eventuallyEq
         ((((contDiff_const (c := gᴴ)).mul (JacB.contDiff_exp_alg.comp
           ((JacB.pmat_contDiff ε).const_smul (2 : ℝ)))).mul
             (contDiff_const (c := g))).contDiffAt)
         (Filter.Eventually.of_forall fun w => ?_)
       exact JacB.exp_two_actR hg w)
     (JacB.fderiv_exp_two_inj _)
   have h2 := (JacB.crdC ε).contDiff.contDiffAt.comp z (hf.const_smul (1 / 2 : ℝ))
   refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
   have e : (1 / 2 : ℝ) • (2 : ℝ) • pmat (actR (ε := ε) g w) = pmat (actR (ε := ε) g w) := by
     rw [smul_smul]
     norm_num
   show actR g w = JacB.crdC ε ((1 / 2 : ℝ) • (2 : ℝ) • pmat (actR (ε := ε) g w))
   rw [e]
   exact (JacB.crd_pmat _).symm)

theorem jacBase {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    |LinearMap.det ((fderiv ℝ (actR (ε := ε) (NormedSpace.exp (pmat y))) 0 :
      (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))| * Jac y = 1 := by
  set D : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ) :=
    ((fderiv ℝ (actR (ε := ε) (NormedSpace.exp (pmat y))) 0 :
      (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ)) with hD
  have hL : LinearMap.det (PolarJacobianDeterminant.shcAdCL y) = Jac y := by
    have h := detP y
    rw [PolarJacobianDeterminant.fderiv_shcAdC] at h
    simpa using h
  have hcomp : (PolarJacobianDeterminant.shcAdCL y).comp D = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    have h1 := JacB.crd_pmat (PolarJacobianDeterminant.shcAdCL y (D v))
    have h2 : shcAd y (pmat (D v)) = pmat v := JacB.shcAd_fderiv_actR y v
    rw [PolarJacobianDeterminant.pmat_shcAdCL, h2, JacB.crd_pmat] at h1
    exact h1.symm
  have hdet : LinearMap.det (PolarJacobianDeterminant.shcAdCL y) * LinearMap.det D = 1 := by
    rw [← LinearMap.det_comp, hcomp, LinearMap.det_id]
  rw [hL] at hdet
  rw [← abs_of_pos (JacB.jac_pos' y), ← abs_mul, mul_comm, hdet, abs_one]

end ReciprocityTheory.ChartRestriction.DS
end
end

