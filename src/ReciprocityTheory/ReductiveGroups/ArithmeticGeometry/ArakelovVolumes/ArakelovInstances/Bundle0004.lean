import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0003
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.KappaStatementHolds
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Matrix Topology Filter
open scoped Classical

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem nmat_lower (w : V (nd X)) (τ : X.Ψ) : (mat (nmat X w) τ).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : i < j := hij
  simp [mat, nmat, hij'.ne, not_lt.mpr hij'.le]

theorem ninv_lower (w : V (nd X)) (τ : X.Ψ) (x y : Fin r) (hxy : x < y) :
    Ring.inverse (mat (nmat X w) τ) x y = 0 := by
  have : Invertible (mat (nmat X w) τ) := (isUnit_nmat X τ w).invertible
  have h := Matrix.blockTriangular_inv_of_blockTriangular (nmat_lower X w τ)
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  exact h hxy

theorem ninv_diag (w : V (nd X)) (τ : X.Ψ) (a : Fin r) : Ring.inverse (mat (nmat X w) τ) a a = 1 := by
  have hu : IsUnit (mat (nmat X w) τ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_nmat X τ w)

  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv _ hu) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
  · rw [← Matrix.nonsing_inv_eq_ringInverse]
    simpa [mat, nmat] using h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have h0 : (mat (nmat X w) τ)⁻¹ k a = 0 := by
        rw [Matrix.nonsing_inv_eq_ringInverse]
        exact ninv_lower X w τ k a hlt
      rw [h0, mul_zero]
    · rw [nmat_lower X w τ hgt, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

def ninvF (w : V (nd X)) : Frame X.Ψ r := fun τ a c => Ring.inverse (mat (nmat X w) τ) a c

theorem det_lmulL_ninv (w : V (nd X)) : LinearMap.det (lmulL X (ninvF X w)) = 1 :=
  det_lmulL_unit X (ninvF X w) (fun τ a x h => ninv_lower X w τ a x h) (fun τ a => ninv_diag X w τ a)

theorem embF_lmulL (w : V (nd X)) (τ : X.Ψ) (v : V (nd X)) (x c : Fin r) :
    embF X (lmulL X (ninvF X w) (vecOf X v)) τ x c =
      (Ring.inverse (mat (nmat X w) τ) * Lin X τ v) x c := by
  have hl : ∀ (N : Frame X.Ψ r) (u : Ent X → ℂ) (e : Ent X),
      lmulL X N u e = ∑ k, N e.1 e.2.1.1 k * embF X u e.1 k e.2.1.2 := fun _ _ _ => rfl
  have hL : ∀ k c' : Fin r, Lin X τ v k c' = embF X (vecOf X v) τ k c' := fun _ _ => rfl
  rw [Matrix.mul_apply]
  by_cases h : c < x
  · rw [embF, dif_pos h, hl]
    rfl
  ·
    rw [embF, dif_neg h]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : c < k
    · rw [ninv_lower X w τ x k (lt_of_le_of_lt (not_lt.mp h) hk), zero_mul]
    · rw [hL, embF, dif_neg hk, mul_zero]

def vecL : V (nd X) ≃ₗ[ℂ] (Ent X → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).trans
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin (Ent X)))

theorem vecL_apply (v : V (nd X)) : vecL X v = vecOf X v := rfl

theorem kappa_statement_holds : KapGGStatement (E := E) := by
  intro r X x0 x1 γ U Φ bf hU hdiff hrel z hz
  obtain ⟨hdom, hbor, -⟩ := hrel z hz
  set Φ' := fderiv ℂ Φ z with hΦ'
  have hΦ : HasFDerivAt Φ Φ' z := ((hdiff z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt

  have hmat : ∀ z' ∈ U, ∀ τ : X.Ψ, mat x0 τ * mat (nmat X z') τ =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ) *
        (mat (nmat X (Φ z')) τ * mat (bf z') τ) := by
    intro z' hz' τ
    have h := congrFun (hrel z' hz').2.2 τ
    change mat x0 τ * mat (nmat X z') τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
      ((mat x1 τ * mat (nmat X (Φ z')) τ) * mat (bf z') τ) at h
    rw [h]
    simp only [Matrix.mul_assoc]

  have hG : ∀ τ : X.Ψ, IsUnit ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ).det := by
    intro τ
    have h0 : (mat x0 τ * mat (nmat X z) τ).det ≠ 0 := (hdom τ).1
    rw [hmat z hz τ, Matrix.det_mul] at h0
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul h0)
  have hrel' : ∀ τ : X.Ψ, ∀ z' ∈ U, mat (nmat X (Φ z')) τ * mat (bf z') τ =
      (((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ)⁻¹ * mat x0 τ) * mat (nmat X z') τ := by
    intro τ z' hz'
    rw [Matrix.mul_assoc, hmat z' hz' τ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hG τ),
      Matrix.one_mul]
  have hup : ∀ τ : X.Ψ, ∀ z' ∈ U, ∀ a c : Fin r, c < a → mat (bf z') τ a c = 0 :=
    fun τ z' hz' a c h => ((hrel z' hz').2.1 τ).2 a c h
  set b := bf z with hb

  have key : (rmulL X b) ∘ₗ (lmulL X (ninvF X (Φ z))) ∘ₗ
      ((vecL X : V (nd X) →ₗ[ℂ] (Ent X → ℂ)) ∘ₗ (Φ' : V (nd X) →ₗ[ℂ] V (nd X)) ∘ₗ
        ((vecL X).symm : (Ent X → ℂ) →ₗ[ℂ] V (nd X))) =
      (lmulL X b) ∘ₗ (lmulL X (ninvF X z)) := by
    refine LinearMap.ext fun u => funext fun e => ?_
    obtain ⟨h, rfl⟩ : ∃ h, vecL X h = u := ⟨(vecL X).symm u, (vecL X).apply_symm_apply u⟩
    rcases e with ⟨τ, ⟨⟨a, c⟩, hca⟩⟩
    have hld := lower_deriv X τ _ U hU Φ (fun z' => mat (bf z') τ) (hrel' τ) (hup τ) z hz Φ' hΦ h a c hca
    rw [Matrix.sub_apply, sub_eq_zero, Matrix.mul_apply, Matrix.mul_apply] at hld
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe]
    simp only [vecL_apply]
    show ∑ y, embF X (lmulL X (ninvF X (Φ z)) (vecOf X (Φ' h))) τ a y * b τ y c =
      ∑ x, b τ a x * embF X (lmulL X (ninvF X z) (vecOf X h)) τ x c
    simp only [embF_lmulL]
    exact hld.symm
  have hdet := congrArg LinearMap.det key
  simp only [LinearMap.det_comp, LinearMap.det_conj, det_lmulL_ninv, one_mul] at hdet
  have hupb : ∀ τ a x, x < a → b τ a x = 0 := fun τ a x h => (hbor τ).2 a x h
  rw [det_lmulL_upper X b hupb, det_rmulL_upper X b hupb] at hdet

  have hd : ∀ τ a, b τ a a ≠ 0 := by
    intro τ a
    have h0 := (hbor τ).1
    rw [Matrix.det_of_isUpperTriangular (M := mat b τ) (fun i j h => (hbor τ).2 i j h)] at h0
    exact Finset.prod_ne_zero_iff.mp h0 a (Finset.mem_univ a)
  have hcol : ∏ e : Ent X, b e.1 e.2.1.2 e.2.1.2 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun e _ => hd _ _
  rw [bchar_kap X b hd]
  show LinearMap.det (Φ' : V (nd X) →ₗ[ℂ] V (nd X)) = _
  exact eq_div_of_mul_eq hcol (by rw [mul_comm, hdet, mul_one])

end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LeviVReLine
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open ReciprocityTheory.AnForm ReciprocityTheory.L2DbarEstimates Filter Topology

theorem snd_affine {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (h : F → ℝ) (c : F) (L : E →L[ℝ] F) (x : E) (hh : ContDiffAt ℝ 2 h (c + L x))
    (w : E) :
    fderiv ℝ (fderiv ℝ (fun y => h (c + L y))) x w w = fderiv ℝ (fderiv ℝ h) (c + L x) (L w) (L w) := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ h (c + L y) := by
    have h1 : ∀ᶠ z in 𝓝 (c + L x), DifferentiableAt ℝ h z :=
      (hh.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
    have hg : ContinuousAt (fun y => c + L y) x := (continuous_const.add L.continuous).continuousAt
    exact hg.eventually h1
  have heq : fderiv ℝ (fun y => h (c + L y)) =ᶠ[𝓝 x] fun y => (fderiv ℝ h (c + L y)).comp L := by
    filter_upwards [hd] with y hy
    have hgd : HasFDerivAt (fun y => c + L y) L y := (L.hasFDerivAt).const_add c
    exact (hy.hasFDerivAt.comp y hgd).fderiv
  rw [heq.fderiv_eq]
  have hd2 : DifferentiableAt ℝ (fderiv ℝ h) (c + L x) :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hF : HasFDerivAt (fun y => fderiv ℝ h (c + L y)) ((fderiv ℝ (fderiv ℝ h) (c + L x)).comp L) x :=
    hd2.hasFDerivAt.comp x ((L.hasFDerivAt).const_add c)
  have hG : HasFDerivAt (fun y => (fderiv ℝ h (c + L y)).comp L)
      (((ContinuousLinearMap.compL ℝ E F ℝ).flip L).comp ((fderiv ℝ (fderiv ℝ h) (c + L x)).comp L)) x :=
    ((ContinuousLinearMap.compL ℝ E F ℝ).flip L).hasFDerivAt.comp x hF
  rw [hG.fderiv]
  rfl

def lineL {n : ℕ} (u : V n) : (Fin 1 → ℂ) →L[ℝ] V n :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight u).restrictScalars ℝ

theorem lineL_apply {n : ℕ} (u : V n) (v : Fin 1 → ℂ) : lineL u v = v 0 • u := rfl

theorem sum_bas_re {n : ℕ} (ξ : Fin n → ℂ) :
    (∑ k, ((ξ k).re • bas n k + (ξ k).im • (Complex.I • bas n k))) = WithLp.toLp 2 ξ := by
  have h : ∀ k, ((ξ k).re • bas n k + (ξ k).im • (Complex.I • bas n k)) = ξ k • bas n k := fun k => by
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul]
    congr 1
    exact Complex.re_add_im (ξ k)
  have hsum : ∑ k, ξ k • bas n k = WithLp.toLp 2 ξ := by
    ext j
    simp [bas, EuclideanSpace.single_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp_rw [h]
  exact hsum

theorem sum_bas_im {n : ℕ} (ξ : Fin n → ℂ) :
    (∑ k, ((ξ k).re • (Complex.I • bas n k) - (ξ k).im • bas n k)) = Complex.I • WithLp.toLp 2 ξ := by
  have h : ∀ k, ((ξ k).re • (Complex.I • bas n k) - (ξ k).im • bas n k) = Complex.I • (ξ k • bas n k) :=
      fun k => by
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul, ← sub_smul]
    congr 1
    apply Complex.ext <;> simp
  have hsum : ∑ k, ξ k • bas n k = WithLp.toLp 2 ξ := by
    ext j
    simp [bas, EuclideanSpace.single_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp_rw [h, ← Finset.smul_sum, hsum]

theorem leviV_re_line {n : ℕ} (h : V n → ℝ) (z : V n) (hh : ContDiffAt ℝ 2 h z) (ξ : Fin n → ℂ) :
    (leviV n (fun y => (h y : ℂ)) z ξ).re =
      levi (fun v : Fin 1 → ℂ => h (z + lineL (WithLp.toLp 2 ξ) v)) 0 (fun _ => 1) := by
  have e := Y.LocalMaximumSecondDerivative.leviV_re_eq hh ξ
  rw [sum_bas_re, sum_bas_im] at e
  have L0 : z + lineL (WithLp.toLp 2 ξ) 0 = z := by simp [lineL_apply]
  have L1 : lineL (WithLp.toLp 2 ξ) (fun _ => 1) = WithLp.toLp 2 ξ := by simp [lineL_apply]
  have L2 : lineL (WithLp.toLp 2 ξ) (Complex.I • fun _ => 1) = Complex.I • WithLp.toLp 2 ξ := by
    simp [lineL_apply]
  have h0 : ContDiffAt ℝ 2 h (z + lineL (WithLp.toLp 2 ξ) 0) := by rw [L0]; exact hh
  have s1 := snd_affine h z (lineL (WithLp.toLp 2 ξ)) 0 h0 (fun _ => 1)
  have s2 := snd_affine h z (lineL (WithLp.toLp 2 ξ)) 0 h0 (Complex.I • fun _ => 1)
  rw [L0, L1] at s1
  rw [L0, L2] at s2
  unfold levi
  rw [s1, s2]
  linarith

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
end
end

