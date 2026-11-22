import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0002

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.HasFDerivAtNmat
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Matrix Topology Filter
open scoped Classical

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def vecOf (z : V (nd X)) : Ent X → ℂ := fun e => z (Fintype.equivFin (Ent X) e)

def Lin (τ : X.Ψ) : V (nd X) →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ where
  toFun z := Matrix.of (embF X (vecOf X z) τ)
  map_add' z w := by
    ext a c
    simp only [Matrix.of_apply, Matrix.add_apply, embF, vecOf]
    split_ifs
    · rfl
    · simp
  map_smul' t z := by
    ext a c
    simp only [Matrix.of_apply, Matrix.smul_apply, embF, vecOf, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · rfl
    · simp

theorem nmat_eq (z : V (nd X)) (τ : X.Ψ) : mat (nmat X z) τ = 1 + Lin X τ z := by
  ext a c
  simp only [mat, nmat, Lin, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.add_apply,
    Matrix.one_apply, embF, vecOf]
  split_ifs with h1 h2 <;> first
    | (subst h2; exact absurd h1 (lt_irrefl _))
    | simp_all
    | omega

theorem hasFDerivAt_nmat (τ : X.Ψ) (z : V (nd X)) :
    HasFDerivAt (fun z' => mat (nmat X z') τ) (LinearMap.toContinuousLinearMap (Lin X τ)) z := by
  have e : (fun z' => mat (nmat X z') τ) = fun z' => 1 + LinearMap.toContinuousLinearMap (Lin X τ) z' :=
    funext fun z' => by rw [nmat_eq]; rfl
  rw [e]
  exact (LinearMap.toContinuousLinearMap (Lin X τ)).hasFDerivAt.const_add 1

theorem isUnit_nmat (τ : X.Ψ) (z : V (nd X)) : IsUnit (mat (nmat X z) τ) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_lowerTriangular]
  · simp [mat, nmat]
  · intro a c hac
    have h' : a < c := OrderDual.toDual_lt_toDual.mp hac
    simp only [mat, nmat, Matrix.of_apply]
    rw [dif_neg (not_lt.mpr h'.le), if_neg h'.ne]

def entryL (a c : Fin r) : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] ℂ where
  toFun M := M a c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lower_deriv (τ : X.Ψ) (A : Matrix (Fin r) (Fin r) ℂ) (U : Set (V (nd X))) (hU : IsOpen U)
    (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Matrix (Fin r) (Fin r) ℂ)
    (hrel : ∀ z ∈ U, mat (nmat X (Φ z)) τ * bf z = A * mat (nmat X z) τ)
    (hup : ∀ z ∈ U, ∀ a c : Fin r, c < a → bf z a c = 0)
    (z : V (nd X)) (hz : z ∈ U) (Φ' : V (nd X) →L[ℂ] V (nd X)) (hΦ : HasFDerivAt Φ Φ' z)
    (h : V (nd X)) (a c : Fin r) (hca : c < a) :
    (bf z * (Ring.inverse (mat (nmat X z) τ) * Lin X τ h) -
      (Ring.inverse (mat (nmat X (Φ z)) τ) * Lin X τ (Φ' h)) * bf z) a c = 0 := by
  obtain ⟨G, hG⟩ : ∃ G : V (nd X) → Matrix (Fin r) (Fin r) ℂ,
      G = fun w => Ring.inverse (mat (nmat X (Φ w)) τ) * A * mat (nmat X w) τ := ⟨_, rfl⟩
  have hbfG : ∀ w ∈ U, bf w = G w := by
    intro w hw
    rw [hG]
    dsimp only
    rw [mul_assoc, ← hrel w hw, ← mul_assoc,
      Ring.inverse_mul_cancel _ (isUnit_nmat X τ (Φ w)), one_mul]
  have hMd : HasFDerivAt (fun w => mat (nmat X (Φ w)) τ)
      ((LinearMap.toContinuousLinearMap (Lin X τ)).comp Φ') z :=
    (hasFDerivAt_nmat X τ (Φ z)).comp z hΦ
  have hinv : DifferentiableAt ℂ (fun w => Ring.inverse (mat (nmat X (Φ w)) τ)) z := by
    have hi := (differentiableAt_inverse (𝕜 := ℂ) (isUnit_nmat X τ (Φ z))).comp z hMd.differentiableAt
    exact hi
  have hGd : DifferentiableAt ℂ G z := by
    rw [hG]
    exact (hinv.mul (differentiableAt_const A)).mul (hasFDerivAt_nmat X τ z).differentiableAt
  have hGd' : HasFDerivAt G (fderiv ℂ G z) z := hGd.hasFDerivAt
  have hent : (fderiv ℂ G z h) a c = 0 := by
    have hE : HasFDerivAt (fun w => G w a c)
        ((LinearMap.toContinuousLinearMap (entryL a c)).comp (fderiv ℂ G z)) z :=
      (LinearMap.toContinuousLinearMap (entryL a c)).hasFDerivAt.comp z hGd'
    have heq : (fun w => G w a c) =ᶠ[𝓝 z] fun _ => (0 : ℂ) :=
      Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => by
        show G w a c = 0
        rw [← hbfG w hw]
        exact hup w hw a c hca
    have h0 : HasFDerivAt (fun w => G w a c) (0 : V (nd X) →L[ℂ] ℂ) z :=
      (hasFDerivAt_const (0 : ℂ) z).congr_of_eventuallyEq heq
    have := congrArg (fun T => T h) (hE.unique h0)
    exact this
  have hLHS := hMd.mul' hGd'
  have hRHS : HasFDerivAt (fun w => A * mat (nmat X w) τ)
      (A • LinearMap.toContinuousLinearMap (Lin X τ)) z := (hasFDerivAt_nmat X τ z).const_mul A
  have heq2 : (fun w => A * mat (nmat X w) τ) =ᶠ[𝓝 z] fun w => mat (nmat X (Φ w)) τ * G w :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun w hw => by
      show A * mat (nmat X w) τ = mat (nmat X (Φ w)) τ * G w
      rw [← hbfG w hw]
      exact (hrel w hw).symm
  have hU2 := (hLHS.congr_of_eventuallyEq heq2).unique hRHS
  have I : mat (nmat X (Φ z)) τ * fderiv ℂ G z h + Lin X τ (Φ' h) * G z = A * Lin X τ h := by
    have := congrArg (fun T => T h) hU2
    exact this
  have e1 : Ring.inverse (mat (nmat X (Φ z)) τ) * mat (nmat X (Φ z)) τ = 1 :=
    Ring.inverse_mul_cancel _ (isUnit_nmat X τ (Φ z))
  have e2 : mat (nmat X z) τ * Ring.inverse (mat (nmat X z) τ) = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_nmat X τ z)
  have hGh : fderiv ℂ G z h =
      Ring.inverse (mat (nmat X (Φ z)) τ) * (A * Lin X τ h - Lin X τ (Φ' h) * G z) := by
    rw [← I, add_sub_cancel_right, ← mul_assoc, e1, one_mul]
  have hGz : G z * (Ring.inverse (mat (nmat X z) τ) * Lin X τ h) =
      Ring.inverse (mat (nmat X (Φ z)) τ) * A * Lin X τ h := by
    rw [hG]
    simp only
    rw [mul_assoc (Ring.inverse (mat (nmat X (Φ z)) τ) * A), ← mul_assoc (mat (nmat X z) τ), e2, one_mul]
  rw [hbfG z hz, hGz, ← hent, hGh, mul_sub]
  simp only [mul_assoc]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LogpdAnalytic
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology

variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)

theorem fn_zero_ne (hD : ∀ k, D k ≠ 0) : fn hm D Y 0 ≠ 0 := by
  unfold fn
  simp only [Pi.zero_apply]
  have h : Gnz hm D Y 0 = Matrix.diagonal fun a : Fin m => ((D (Fin.castLE hm a) : ℝ) : ℂ) := by
    simp only [Gnz, Gz, zero_smul, sub_zero, add_zero, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one]
    first
    | exact Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hm)
    | simp [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hm)]
    | (ext i j
       simp [Matrix.diagonal_apply, (Fin.castLE_injective hm).eq_iff])
  rw [h, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact Finset.prod_ne_zero_iff.2 fun a _ => hD _

theorem levi_logfn (hD : ∀ k, D k ≠ 0) :
    levi (fun v => Real.log |fn hm D Y v|) 0 (fun _ => 1) =
      levi (fn hm D Y) 0 (fun _ => 1) / fn hm D Y 0 := by
  have hc : ContDiffAt ℝ 2 (fn hm D Y) 0 := (contDiff_fn hm D Y).contDiffAt
  have h0 := fn_zero_ne hm D Y hD
  have h := leviHalfLogAbs (ι := Fin 1) (fn hm D Y) 0 hc h0 (fderiv_fn_zero hm D Y) (fun _ => 1)
  have hL : ContDiffAt ℝ 2 (fun x => (1 / 2 : ℝ) * Real.log |fn hm D Y x|) 0 := by
    have e : (fun x => (1 / 2 : ℝ) * Real.log |fn hm D Y x|) = fun x => (1 / 2 : ℝ) * Real.log (fn hm D Y x) := by
      funext x; rw [Real.log_abs]
    rw [e]
    exact contDiffAt_const.mul (hc.log h0)
  have e : (fun v => Real.log |fn hm D Y v|) =
      fun v => (1 / 2 * Real.log |fn hm D Y v|) + 1 * (1 / 2 * Real.log |fn hm D Y v|) := by
    funext v; ring
  rw [e, levi_add_smul 1 hL hL, h]
  field_simp
  ring

theorem Gz_herm (ζ : ℂ) : (Gz hm D Y ζ)ᴴ = Gz hm D Y ζ := by
  have hD : (Matrix.diagonal fun k => (D k : ℂ))ᴴ = Matrix.diagonal fun k => (D k : ℂ) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext k
    simp
  first
  | simp only [Gz, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
  | (unfold Gz
     rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
       Matrix.conjTranspose_conjTranspose]
     erw [hD]
     simp only [Matrix.mul_assoc])

theorem fn_eq (v : Fin 1 → ℂ) : fn hm D Y v = ‖pd hm Y v‖ ^ 2 * fY hm D Y v := by
  have key : ∀ (p G : ℂ), (star p * (G * p)).re = ‖p‖ ^ 2 * G.re := by
    intro p G
    have h1 : star p * (G * p) = ((Complex.normSq p : ℝ) : ℂ) * G := by
      rw [Complex.star_def, ← Complex.mul_conj]
      ring
    rw [h1, Complex.re_ofReal_mul]
    first
    | rw [Complex.normSq_eq_norm_sq]
    | rw [← Complex.sq_norm]
    | simp [Complex.normSq_eq_norm_sq]
  simp only [fn, fY, Gnz, pd, Matrix.det_mul, Matrix.det_conjTranspose]
  exact key _ _

theorem pd_eval (v : Fin 1 → ℂ) : pd hm Y v = (lin (-(Ym hm Y))).det.eval (v 0) := by
  unfold pd lin
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply, sub_eq_add_neg] <;> ring
  · simp [Matrix.one_apply, h, sub_eq_add_neg] <;> ring

theorem pd_analytic : AnalyticAt ℂ (pd hm Y) 0 := by
  have e : pd hm Y = (fun z => (lin (-(Ym hm Y))).det.eval z) ∘ (fun v : Fin 1 → ℂ => v 0) :=
    funext fun v => pd_eval hm Y v
  rw [e]
  exact ((lin (-(Ym hm Y))).det.differentiable.analyticAt _).comp
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt _)

theorem pd_zero : pd hm Y 0 = 1 := by
  simp [pd]

theorem logpd_analytic : AnalyticAt ℂ (fun v => 2 * Complex.log (pd hm Y v)) 0 := by
  have h0 : pd hm Y 0 ∈ Complex.slitPlane := by
    rw [pd_zero]
    exact Complex.one_mem_slitPlane
  exact analyticAt_const.mul ((pd_analytic hm Y).clog h0)

theorem logpd_eq (v : Fin 1 → ℂ) : Real.log (‖pd hm Y v‖ ^ 2) = (2 * Complex.log (pd hm Y v)).re := by
  have h : (2 * Complex.log (pd hm Y v)).re = 2 * (Complex.log (pd hm Y v)).re := by
    simp [Complex.mul_re]
  rw [h, Complex.log_re, Real.log_pow]
  push_cast
  ring

theorem levi_logpd (w : Fin 1 → ℂ) : levi (fun v => Real.log (‖pd hm Y v‖ ^ 2)) 0 w = 0 := by
  have e : (fun v => Real.log (‖pd hm Y v‖ ^ 2)) = fun v => (2 * Complex.log (pd hm Y v)).re :=
    funext fun v => logpd_eq hm Y v
  rw [e]
  exact levi_re_analytic (logpd_analytic hm Y) w

theorem core_levi (hD : ∀ k, D k ≠ 0) :
    levi (fun v => Real.log |fY hm D Y v|) 0 (fun _ => 1) =
      ∑ a : Fin m, (D (Fin.castLE hm a))⁻¹ * Sa hm D Y a := by
  have hP : (∏ a : Fin m, D (Fin.castLE hm a)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hD _
  have hfY0 : fY hm D Y 0 ≠ 0 := by rw [fY_zero]; exact hP
  have h0 := fn_zero_ne hm D Y hD
  have hcont : ContinuousAt (fY hm D Y) 0 := (contDiff_fY hm D Y).continuous.continuousAt
  have hpdc : ContinuousAt (pd hm Y) 0 := (pd_analytic hm Y).continuousAt
  have hev : (fun v => Real.log |fY hm D Y v|) =ᶠ[𝓝 0]
      fun v => Real.log |fn hm D Y v| + (-1) * Real.log (‖pd hm Y v‖ ^ 2) := by
    filter_upwards [hcont.eventually_ne hfY0, hpdc.eventually_ne (by rw [pd_zero]; exact one_ne_zero)]
      with v h1 h2
    have hp : ‖pd hm Y v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 h2)
    rw [Real.log_abs, Real.log_abs, fn_eq, Real.log_mul hp h1]
    ring
  have hL1 : ContDiffAt ℝ 2 (fun v => Real.log |fn hm D Y v|) 0 := by
    have e : (fun v => Real.log |fn hm D Y v|) = fun v => Real.log (fn hm D Y v) := by
      funext v; rw [Real.log_abs]
    rw [e]
    exact (contDiff_fn hm D Y).contDiffAt.log h0
  have hL2 : ContDiffAt ℝ 2 (fun v => Real.log (‖pd hm Y v‖ ^ 2)) 0 := by
    rw [funext (logpd_eq hm Y)]
    exact Complex.reCLM.contDiff.contDiffAt.comp _
      ((logpd_analytic hm Y).contDiffAt.restrict_scalars ℝ)
  rw [levi_congr hev, levi_add_smul (-1) hL1 hL2, levi_logpd, levi_logfn hm D Y hD, levi_fn hm D Y hD,
    fn_zero, mul_zero, add_zero, mul_div_cancel_left₀ _ hP]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
end
end

