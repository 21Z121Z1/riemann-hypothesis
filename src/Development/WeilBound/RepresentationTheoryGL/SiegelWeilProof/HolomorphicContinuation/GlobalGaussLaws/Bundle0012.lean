import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0010
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0011
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.Bundle0002

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInB
section
noncomputable section

open scoped Matrix ComplexConjugate SchwartzMap
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

section
variable {T : Type} [Fintype T] [DecidableEq T] {m n : ℕ} (τ : T)

abbrev Bsp (τ : T) (m n : ℕ) : Type := {τ' : T // τ' ≠ τ} → Fin m → Fin n → ℂ

def extF (b : Bsp τ m n) : T → Fin m → Fin n → ℂ := fun τ' => if h : τ' = τ then 0 else b ⟨τ', h⟩

def extL : Bsp τ m n →L[ℝ] (T → Fin m → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := extF τ
      map_add' := fun b b' => by
        funext τ' i j
        by_cases h : τ' = τ <;> simp [extF, h]
      map_smul' := fun r b => by
        funext τ' i j
        by_cases h : τ' = τ <;> simp [extF, h] }

def coordL (k : T × Fin m × Fin n) : Bsp τ m n →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.2).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.2.1).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => Fin m → Fin n → ℂ) k.1).comp (extL τ)))

theorem tg_eval {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {σ : Type} (v : σ → E → ℂ)
    (hv : ∀ k, (v k).HasTemperateGrowth) (p : MvPolynomial σ ℂ) :
    (fun x => MvPolynomial.eval (fun k => v k x) p).HasTemperateGrowth := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have := Function.HasTemperateGrowth.const (E := E) a
    convert this using 1
    all_goals first | rfl | (funext x; simp)
  | add p q hp hq =>
    have := hp.add hq
    convert this using 1
    all_goals first | rfl | (funext x; simp)
  | mul_X p k hp =>
    have := hp.mul (hv k)
    convert this using 1
    all_goals first | rfl | (funext x; simp)

def vC (k : T × Fin m × Fin n × Bool) (b : Bsp τ m n) : ℂ :=
  if k.2.2.2 then conj (coordL τ (k.1, k.2.1, k.2.2.1) b) else coordL τ (k.1, k.2.1, k.2.2.1) b

theorem tg_vC (k : T × Fin m × Fin n × Bool) : (vC (m := m) (n := n) τ k).HasTemperateGrowth := by
  by_cases hk : k.2.2.2 = true
  · have e : vC (m := m) (n := n) τ k = ⇑(Complex.conjCLE.toContinuousLinearMap.comp (coordL τ (k.1, k.2.1, k.2.2.1))) := by
      funext b
      simp [vC, hk]
    rw [e]
    exact ContinuousLinearMap.hasTemperateGrowth _
  · have e : vC (m := m) (n := n) τ k = ⇑(coordL τ (k.1, k.2.1, k.2.2.1)) := by
      funext b
      simp [vC, hk]
    rw [e]
    exact ContinuousLinearMap.hasTemperateGrowth _

theorem tg_poly (p : MvPolynomial (T × Fin m × Fin n × Bool) ℂ) :
    (fun b : Bsp τ m n => MvPolynomial.eval (fun k => vC τ k b) p).HasTemperateGrowth :=
  tg_eval _ (tg_vC τ) p

variable (fr : Matrix (Fin m) (Fin m) ℂ)

def eL (hfr : IsUnit fr.det) : (T → Fin m → Fin n → ℂ) ≃ₗ[ℝ] ((Fin m → Fin n → ℂ) × Bsp τ m n) where
  toFun z := (Matrix.of.symm (fr⁻¹ * Matrix.of (z τ)), fun τ' => z τ'.1)
  invFun ab := fun τ' => if h : τ' = τ then Matrix.of.symm (fr * Matrix.of ab.1) else ab.2 ⟨τ', h⟩
  map_add' z w := by
    ext1
    · exact Matrix.mul_add fr⁻¹ (of (z τ)) (of (w τ))
    · rfl
  map_smul' r z := by
    ext1
    · exact Matrix.mul_smul fr⁻¹ r (of (z τ))
    · rfl
  left_inv z := by
    funext τ'
    by_cases h : τ' = τ
    · subst h
      simp [Matrix.mul_nonsing_inv_cancel_left _ _ hfr]
    · simp [h]
  right_inv ab := by
    ext1
    · simp [Matrix.nonsing_inv_mul_cancel_left _ _ hfr]
    · funext τ'
      simp [τ'.2]

end

end PositivityTheory.Rg.Sw.Glob.AwayPf
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcB
section
noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcBH

open DCalcH

variable {m n : ℕ}

theorem norm_vS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) (a : Fin m) (j : Fin n) :
    ‖vS u X s a j‖ ^ 2 = ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2 := by
  simp only [DCalcH.vS, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

def nS (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) : ℝ := ∑ a, ∑ j, ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2

theorem gs_vS (c : ℝ) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    gs c (vS u X s) = Complex.exp (((-(c * nS u X s)) : ℝ) : ℂ) := by
  simp only [gs, nS, norm_vS, Complex.ofReal_neg]

theorem nS_hasDeriv (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (nS u X) (∑ a, ∑ j, 2 * X j * ‖vS u X s a j‖ ^ 2) s := by
  have h : ∀ a j, HasDerivAt (fun s => ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2)
      (2 * X j * ‖vS u X s a j‖ ^ 2) s := by
    intro a j
    rw [norm_vS]
    have h1 : HasDerivAt (fun s : ℝ => s * X j) (X j) s := by
      simpa using (hasDerivAt_id s).mul_const (X j)
    refine (((h1.exp).pow 2).const_mul (‖u a j‖ ^ 2)).congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  have h3 := HasDerivAt.sum (u := Finset.univ) fun a _ => HasDerivAt.sum (u := Finset.univ) fun j _ => h a j
  have e : nS u X = ∑ a, ∑ j, fun s : ℝ => ‖u a j‖ ^ 2 * Real.exp (s * X j) ^ 2 := by
    ext y
    simp [nS, Finset.sum_apply]
  rw [e]
  exact h3

theorem gs_hasDeriv (c : ℝ) (u : Fin m → Fin n → ℂ) (X : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => gs c (vS u X s))
      (gs c (vS u X s) * (-(2 * c : ℂ) * ∑ a, ∑ j, (X j : ℂ) * ((‖vS u X s a j‖ ^ 2 : ℝ) : ℂ))) s := by
  simp_rw [gs_vS]
  have h := ((nS_hasDeriv u X s).const_mul c).neg.ofReal_comp.cexp
  refine h.congr_deriv ?_
  congr 1
  push_cast
  rw [neg_mul]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

def fF (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s : ℝ) : ℂ :=
  ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * fP c P (vS u X s)

theorem fF_hasDeriv (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s : ℝ) :
    HasDerivAt (fF c X P u) (fF c X (dil c X P) u s) s := by
  have he : HasDerivAt (fun s : ℝ => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ))
      ((((m : ℝ) * ∑ j, X j : ℝ) : ℂ) * ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ)) s := by
    have := hasDerivAt_expX ((m : ℝ) * ∑ j, X j) s
    simp only [mul_assoc] at this ⊢
    exact this
  have h := he.mul ((eval_hasDeriv P u X s).mul (gs_hasDeriv c u X s))
  unfold fF fP
  have efun : (fun s : ℝ => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * (evX P (vS u X s) * gs c (vS u X s))) =
      fun s => ((Real.exp (s * (m : ℝ) * ∑ j, X j) : ℝ) : ℂ) * (evX P (vS u X s) * gs c (vS u X s)) := rfl
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [evX_dil]
  push_cast
  ring

theorem fF_iter (c : ℝ) (X : Fin n → ℝ) (u : Fin m → Fin n → ℂ) (r : ℕ) :
    iteratedDeriv r (fF c X 1 u) = fF c X ((dil c X ^ r) 1) u := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    rw [(fF_hasDeriv c X ((dil c X ^ r) 1) u s).deriv, pow_succ', Module.End.mul_apply]

end DCalcBH

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompAway
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open PositivityTheory.Rg.Sw.Glob.DecH

theorem decompAway : DecompAway := by
  intro D n θ τ ι hθ hι g
  obtain ⟨-, hιy⟩ := hι
  have hg : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mat g) * (Jst D n).map (incA D) * mat g =
      (Jst D n).map (incA D) := g.2
  set Y := compAt θ τ (mat g) with hYdef
  have hY : Yᴴ * reidx (JJ n) * Y = reidx (JJ n) := by
    have := congrArg (compAt θ τ) hg
    rwa [DA.compAt_mul, DA.compAt_mul, DA.compAt_conjT θ hθ, DA.compAt_Jst θ hθ] at this
  have hinv : compAt θ τ (mat g⁻¹) * Y = 1 := by
    rw [hYdef, ← DA.compAt_mul, ← DA.mat_mul, inv_mul_cancel, DA.mat_one, DA.compAt_one]
  have hYu : IsUnit Y.det := Matrix.isUnit_det_of_left_inverse hinv
  set M : M2 n := Y.submatrix finSumFinEquiv finSumFinEquiv with hMdef
  have hMY : reidx M = Y := by ext i j; simp [reidx, hMdef]
  have hMG : InG M := by
    have h2 : JJ n = (reidx (JJ n)).submatrix finSumFinEquiv finSumFinEquiv := by ext i j; simp [reidx]
    unfold InG
    rw [h2, hMdef, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hY]
  have hMu : IsUnit M.det := by rw [hMdef, det_submatrix_equiv_self]; exact hYu
  set y := mkGR M hMu hMG with hydef
  have hιY : compAt θ τ (mat (ι y)) = Y := by rw [(hιy y).1, hydef, mR_mkGR, hMY]
  have htriv : compAt θ τ (mat (g * (ι y)⁻¹)) = 1 := by
    have h3 : compAt θ τ (mat (g * (ι y)⁻¹)) * Y = Y := by
      calc compAt θ τ (mat (g * (ι y)⁻¹)) * Y = compAt θ τ (mat (g * (ι y)⁻¹)) * compAt θ τ (mat (ι y)) := by rw [hιY]
        _ = compAt θ τ (mat (g * (ι y)⁻¹ * ι y)) := by rw [DA.mat_mul (g * (ι y)⁻¹) (ι y), DA.compAt_mul]
        _ = Y := by rw [inv_mul_cancel_right]
    calc compAt θ τ (mat (g * (ι y)⁻¹)) = compAt θ τ (mat (g * (ι y)⁻¹)) * Y * Y⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hYu, Matrix.mul_one]
      _ = 1 := by rw [h3, Matrix.mul_nonsing_inv _ hYu]
  refine ⟨g * (ι y)⁻¹, y, htriv, by group, ?_⟩
  generalize g * (ι y)⁻¹ = x at htriv ⊢
  intro y'
  apply DA.mat_inj
  rw [DA.mat_mul, DA.mat_mul]
  apply GlobalTheory.StabAtPlace.mx_ext hθ
  · rw [DA.finMap_mul, DA.finMap_mul, (hιy y').2.2, Matrix.mul_one, Matrix.one_mul]
  · intro τ'
    rw [DA.compAt_mul, DA.compAt_mul]
    by_cases h : τ' = τ
    · subst h
      rw [htriv, Matrix.mul_one, Matrix.one_mul]
    · rw [(hιy y').2.1 τ' h, Matrix.mul_one, Matrix.one_mul]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetNeOfPosDef
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

namespace DSiegH

variable {n : ℕ} {A B C D : Matrix (Fin n) (Fin n) ℂ}

theorem cross_form_linear_fractional_eq_conjTranspose_sub (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (W : Matrix (Fin n) (Fin n) ℂ) : (A * W + B)ᴴ * (C * W + D) - (C * W + D)ᴴ * (A * W + B) = Wᴴ - W := by
  have e : (A * W + B)ᴴ * (C * W + D) - (C * W + D)ᴴ * (A * W + B) =
      Wᴴ * (Aᴴ * C - Cᴴ * A) * W + Wᴴ * (Aᴴ * D - Cᴴ * B) + (Bᴴ * C - Dᴴ * A) * W + (Bᴴ * D - Dᴴ * B) := by
    simp only [conjTranspose_add, conjTranspose_mul]
    noncomm_ring
  rw [e, sub_eq_zero.2 h1, h3, h4, sub_eq_zero.2 h2]
  noncomm_ring

theorem det_ne (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : ∀ v : Fin n → ℂ, v ≠ 0 → star v ⬝ᵥ ((Wᴴ - W) *ᵥ v) ≠ 0) :
    (C * W + D).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hQv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have key := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => star v ⬝ᵥ (M *ᵥ v)) (cross_form_linear_fractional_eq_conjTranspose_sub h1 h2 h3 h4 W)
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hQv, Matrix.mulVec_zero, zero_sub, dotProduct_neg] at key
  have e : star v ⬝ᵥ ((C * W + D)ᴴ *ᵥ ((A * W + B) *ᵥ v)) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hQv, star_zero, zero_dotProduct]
  rw [e, neg_zero] at key
  exact hW v hv (by rw [Matrix.sub_mulVec] at *; simpa [dotProduct_sub] using key.symm)

theorem im_formula (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (W : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit (C * W + D).det) :
    (A * W + B) * (C * W + D)⁻¹ - ((A * W + B) * (C * W + D)⁻¹)ᴴ =
      ((C * W + D)⁻¹)ᴴ * (W - Wᴴ) * (C * W + D)⁻¹ := by
  set P := A * W + B
  set Q := C * W + D
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQ
  have hQh : (Q⁻¹)ᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, hQQ, conjTranspose_one]
  have hc : Pᴴ * Q - Qᴴ * P = Wᴴ - W := cross_form_linear_fractional_eq_conjTranspose_sub h1 h2 h3 h4 W
  have e1 : P * Q⁻¹ = (Q⁻¹)ᴴ * (Qᴴ * P) * Q⁻¹ := by rw [← Matrix.mul_assoc, hQh, Matrix.one_mul]
  have e2 : (P * Q⁻¹)ᴴ = (Q⁻¹)ᴴ * (Pᴴ * Q) * Q⁻¹ := by
    rw [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  rw [e2, e1, ← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 2
  have : Qᴴ * P - Pᴴ * Q = -(Pᴴ * Q - Qᴴ * P) := by abel
  rw [this, hc]
  abel

theorem siegel_of (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1) (h4 : Bᴴ * C - Dᴴ * A = -1)
    (W : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit (C * W + D).det) (a : ℂ)
    (hW : (a • (W - Wᴴ)).PosDef) :
    (a • ((A * W + B) * (C * W + D)⁻¹ - ((A * W + B) * (C * W + D)⁻¹)ᴴ)).PosDef := by
  rw [im_formula h1 h2 h3 h4 W hQ]
  have e : a • (((C * W + D)⁻¹)ᴴ * (W - Wᴴ) * (C * W + D)⁻¹) =
      ((C * W + D)⁻¹)ᴴ * (a • (W - Wᴴ)) * (C * W + D)⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  exact hW.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hQ)))

theorem posDef_diag_re (w : Fin n → ℂ) (hw : ∀ j, 0 < (w j).re) (a : ℂ)
    (s : ℂ) (hs : s = Complex.I ∨ s = -Complex.I) (hsa : a * s * 2 = 1) :
    (a • (s • diagonal w - (s • diagonal w)ᴴ)).PosDef := by
  have e : a • (s • diagonal w - (s • diagonal w)ᴴ) = diagonal fun j => ((w j).re : ℂ) := by
    rw [conjTranspose_smul, diagonal_conjTranspose]
    ext i j
    by_cases hij : i = j
    · subst hij
      have hst : star s = -s := by
        rcases hs with rfl | rfl <;> simp [Complex.conj_I]
      simp only [Matrix.smul_apply, Matrix.sub_apply, diagonal_apply_eq, smul_eq_mul, hst, Pi.star_apply]
      have hw' : (w i : ℂ) + star (w i) = 2 * ((w i).re : ℂ) := by
        rw [Complex.star_def, Complex.add_conj]; push_cast; ring
      calc a * (s * w i - -s * star (w i)) = a * s * ((w i : ℂ) + star (w i)) := by ring
        _ = a * s * (2 * ((w i).re : ℂ)) := by rw [hw']
        _ = ((w i).re : ℂ) := by linear_combination ((w i).re : ℂ) * hsa
    · simp [hij]
  rw [e, Matrix.posDef_diagonal_iff]
  intro j
  exact_mod_cast hw j

theorem det_ne_of_posDef (h1 : Aᴴ * C = Cᴴ * A) (h2 : Bᴴ * D = Dᴴ * B) (h3 : Aᴴ * D - Cᴴ * B = 1)
    (h4 : Bᴴ * C - Dᴴ * A = -1) (W : Matrix (Fin n) (Fin n) ℂ) (a : ℂ) (ha : a ≠ 0) (hX : (a • (W - Wᴴ)).PosDef) :
    (C * W + D).det ≠ 0 := by
  refine det_ne h1 h2 h3 h4 W fun v hv => ?_
  have e : Wᴴ - W = (-a⁻¹) • (a • (W - Wᴴ)) := by
    rw [smul_smul, neg_mul, inv_mul_cancel₀ ha, neg_one_smul, neg_sub]
  rw [e, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact mul_ne_zero (neg_ne_zero.2 (inv_ne_zero ha)) (hX.dotProduct_mulVec_pos hv).ne'

end DSiegH

open DRealH DSiegH in
theorem dSieg : DSieg := by
  intro n y X z hz
  obtain ⟨h1, h2, h3, h4⟩ := blocks_of_inG (g := mR y) y.2
  set A := (mR y).toBlocks₁₁ with hA
  set B := (mR y).toBlocks₁₂ with hB
  set C := (mR y).toBlocks₂₁ with hC
  set D := (mR y).toBlocks₂₂ with hD
  set w : Fin n → ℂ := fun j => Complex.exp (2 * z * X j) with hwdef
  set E : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => Complex.exp (z * X j) with hE
  set F : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => Complex.exp (-(z * X j)) with hF
  have hwre : ∀ j, 0 < (w j).re := by
    intro j
    simp only [hwdef, Complex.exp_re]
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    all_goals
      have hj := hz j
      have him : (2 * z * (X j : ℂ)).im = 2 * (z.im * X j) := by simp [Complex.mul_im]; ring
      rw [him]
      rw [abs_lt] at hj
      linarith [hj.1, hj.2]
  have hM : mR y * aC X z = fromBlocks (A * E) (B * F) (C * E) (D * F) := by
    have e : mR y = fromBlocks A B C D := (fromBlocks_toBlocks _).symm
    rw [e]
    unfold aC
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, zero_add, hE, hF]
  have hFu : IsUnit F.det := by
    rw [hF, det_diagonal]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun j _ => Complex.exp_ne_zero _)
  have hFF : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv _ hFu
  have hWF : ∀ s : ℂ, E * (s • 1) = (s • diagonal w) * F := by
    intro s
    rw [hE, hF, Matrix.smul_mul, diagonal_mul_diagonal, Matrix.mul_smul, Matrix.mul_one]
    congr 1
    congr 1
    funext j
    rw [hwdef, ← Complex.exp_add]
    congr 1; ring
  have hblk : ∀ s : ℂ, ((mR y * aC X z).toBlocks₂₁ * (s • 1) + (mR y * aC X z).toBlocks₂₂) = (C * (s • diagonal w) + D) * F ∧
      ((mR y * aC X z).toBlocks₁₁ * (s • 1) + (mR y * aC X z).toBlocks₁₂) = (A * (s • diagonal w) + B) * F := by
    intro s
    rw [hM]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    constructor
    · rw [Matrix.mul_assoc, hWF, Matrix.add_mul, Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, hWF, Matrix.add_mul, Matrix.mul_assoc]
  have hpt : ∀ s : ℂ, ptZ y X z s = (A * (s • diagonal w) + B) * (C * (s • diagonal w) + D)⁻¹ := by
    intro s
    simp only [ptZ]
    rw [(hblk s).1, (hblk s).2, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_assoc _ F, hFF, Matrix.mul_one]
  have hI2 : -(Complex.I / 2) ≠ 0 := by simp [Complex.I_ne_zero]
  have hI2' : Complex.I / 2 ≠ 0 := by simp [Complex.I_ne_zero]
  have hX1 : ((-(Complex.I / 2)) • ((Complex.I • diagonal w) - (Complex.I • diagonal w)ᴴ)).PosDef :=
    posDef_diag_re w hwre _ Complex.I (Or.inl rfl) (by ring_nf; rw [Complex.I_sq]; ring)
  have hX2 : ((Complex.I / 2) • (((-Complex.I) • diagonal w) - ((-Complex.I) • diagonal w)ᴴ)).PosDef :=
    posDef_diag_re w hwre _ (-Complex.I) (Or.inr rfl) (by ring_nf; rw [Complex.I_sq]; ring)
  have hQ1 := det_ne_of_posDef h1 h2 h3 h4 _ _ hI2 hX1
  have hQ2 := det_ne_of_posDef h1 h2 h3 h4 _ _ hI2' hX2
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold IsSiegel
    rw [hpt]
    exact siegel_of h1 h2 h3 h4 _ (isUnit_iff_ne_zero.2 hQ1) _ hX1
  · unfold IsSiegel
    rw [hpt, conjTranspose_conjTranspose]
    have e : ∀ Z : Matrix (Fin n) (Fin n) ℂ, (-(Complex.I / 2)) • (Zᴴ - Z) = (Complex.I / 2) • (Z - Zᴴ) := by
      intro Z; rw [← neg_sub, smul_neg, neg_smul, neg_neg]
    rw [e]
    exact siegel_of h1 h2 h3 h4 _ (isUnit_iff_ne_zero.2 hQ2) _ hX2
  · rw [(hblk _).1, det_mul]; exact mul_ne_zero hQ1 (isUnit_iff_ne_zero.1 hFu)
  · rw [(hblk _).1, det_mul]; exact mul_ne_zero hQ2 (isUnit_iff_ne_zero.1 hFu)

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSchA
section
noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GCSchH

variable {m n : ℕ}

theorem trace_gramB (Z : Matrix (Fin n) (Fin n) ℂ) (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    (Z * gramB ε b u).trace = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a) ⬝ᵥ (Zᵀ *ᵥ u a) := by
  set S := Finset.univ.filter (fun a => ε a = b)
  have hG : ∀ i j, gramB ε b u j i = ∑ a ∈ S, star (u a j) * u a i := fun i j => GaussH.gramB_apply ε b u j i
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hG, Finset.mul_sum, dotProduct, mulVec,
    Matrix.transpose_apply, Pi.star_apply]
  calc _ = ∑ i, ∑ a ∈ S, ∑ j, Z i j * (star (u a j) * u a i) := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a ∈ S, ∑ i, ∑ j, Z i j * (star (u a j) * u a i) := Finset.sum_comm
    _ = ∑ a ∈ S, ∑ j, ∑ i, Z i j * (star (u a j) * u a i) := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem im_quad (W : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    (star y ⬝ᵥ (W *ᵥ y)).im = (star y ⬝ᵥ (((-(Complex.I / 2)) • (W - Wᴴ)) *ᵥ y)).re := by
  have hs : star (star y ⬝ᵥ (W *ᵥ y)) = star y ⬝ᵥ (Wᴴ *ᵥ y) := by
    rw [Matrix.star_dotProduct, Matrix.star_mulVec, star_star, ← Matrix.dotProduct_mulVec]
  rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.sub_mulVec, dotProduct_sub, ← hs]
  set s := star y ⬝ᵥ (W *ᵥ y)
  simp only [smul_eq_mul, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.div_re, Complex.div_im, Complex.I_re, Complex.I_im]
  norm_num
  ring

theorem coercive_of_pos {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (h : ∀ x, x ≠ 0 → 0 < (Q x x).re) : ∃ κ, 0 < κ ∧ ∀ x, κ * ‖x‖ ^ 2 ≤ (Q x x).re :=
  _root_.UpperTheory.Reformulated.B.P6.r24a.PositivityTheory.Rg.Sw.Glob.GCSchH.coercive_of_pos Q h

end PositivityTheory.Rg.Sw.Glob.GCSchH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVac
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open Vac

theorem lIvac : LIvac := by
  intro m n ε c t p q e hc hpq S C hS h1 hy hcell
  have hα : ((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)) ≠ 0 := by
    apply mul_ne_zero <;> apply zpow_ne_zero <;> apply pow_ne_zero <;> simp
  have key : ∀ g : GR n, (toBlocks₂₁ (mR g)).det ≠ 0 →
      S g = (C * ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) ^ (p + q) /
        (((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)))) * F0 p q e g := by
    intro g hg
    obtain ⟨y, h, b, hy0, hb, hh, rfl⟩ := bigcell g hg
    rw [hy y h hy0, hcell h b hb hh, secN_eval ε c t p q hc hpq b hb, vacuum_section_mul_parabolic p q e y h hy0,
      vacuum_section_big_cell p q e h b hh, mul_zpow, mul_zpow]
    field_simp
  have hall : ∀ g, S g = (C * ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) ^ (p + q) /
        (((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)))) * F0 p q e g := by
    intro g
    exact congrFun (Continuous.ext_on dense_cell hS (continuous_const.mul (continuous_vacuum_section p q e)) key) g
  have hlam := hall 1
  rw [h1, weight_factor_one, mul_one] at hlam
  intro g
  rw [hall g, ← hlam, one_mul]

end PositivityTheory.Rg.Sw.Glob
end
end

