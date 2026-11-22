import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0159
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfNormal
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

noncomputable section

namespace GlobalTheory.Mem.Lift.Normal

variable {ι : Type}

theorem real_lin_smul (l : (ι → ℂ) →ₗ[ℝ] ℂ) (c : ℂ) (z : ι → ℂ) :
    l (c • z) = c.re * l z + c.im * l (I • z) := by
  have hc : c • z = c.re • z + c.im • (I • z) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  rw [hc, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

theorem real_lin_I_I (l : (ι → ℂ) →ₗ[ℝ] ℂ) (z : ι → ℂ) : l (I • I • z) = - l z := by
  rw [smul_smul, I_mul_I, neg_one_smul, map_neg]

def linPart (l : (ι → ℂ) →ₗ[ℝ] ℂ) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun z := l z - I * l (I • z)
  map_add' x y := by simp only [smul_add, map_add]; ring
  map_smul' c z := by
    rw [smul_comm I c z, real_lin_smul l c z, real_lin_smul l c (I • z), real_lin_I_I, RingHom.id_apply, smul_eq_mul]
    conv_rhs => rw [← Complex.re_add_im c]
    linear_combination (c.im * l (I • z)) * I_mul_I

def antiPart (l : (ι → ℂ) →ₗ[ℝ] ℂ) : (ι → ℂ) →ₗ⋆[ℂ] ℂ where
  toFun z := l z + I * l (I • z)
  map_add' x y := by simp only [smul_add, map_add]; ring
  map_smul' c z := by
    rw [smul_comm I c z, real_lin_smul l c z, real_lin_smul l c (I • z), real_lin_I_I, smul_eq_mul]
    have : (starRingEnd ℂ) c = c.re - c.im * I := by
      apply Complex.ext <;> simp
    rw [this]
    linear_combination (c.im * l (I • z)) * I_mul_I

theorem im_add_I_re (h : ℂ) : ((h.im : ℂ) + I * ((I * h).im : ℂ)) = I * (starRingEnd ℂ) h := by
  apply Complex.ext <;> simp

theorem im_sub_I_re (h : ℂ) : ((h.im : ℂ) - I * ((I * h).im : ℂ)) = - I * h := by
  apply Complex.ext <;> simp

variable [Fintype ι] [DecidableEq ι]

def nC (X : Matrix ι ι ℂ) (i : ι × ι × Bool × Bool) : ℂ :=
  X i.1 i.2.1 * (-(1 / (4 * π))) * (if i.2.2.1 then -I else 1) * (if i.2.2.2 then I else 1)

def nP (i : ι × ι × Bool × Bool) : ι → ℂ :=
  if i.2.2.1 then I • Pi.single i.1 1 else Pi.single i.1 1

def nQ (H : Matrix ι ι ℂ) (i : ι × ι × Bool × Bool) : ι → ℂ :=
  if i.2.2.2 then I • H⁻¹ *ᵥ Pi.single i.2.1 1 else H⁻¹ *ᵥ Pi.single i.2.1 1

theorem sum_lin (X : Matrix ι ι ℂ) (A : (ι → ℂ) →ₗ[ℂ] ℂ) (v : ι → ℂ) :
    ∑ k, ∑ j, X k j * (v j * A (Pi.single k 1)) = A (X *ᵥ v) := by
  have hx : X *ᵥ v = ∑ k, (∑ j, X k j * v j) • (Pi.single k (1 : ℂ) : ι → ℂ) := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply]
  rw [hx, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sum_anti {H X : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (hX : Xᴴ * H + H * X = 0)
    (A : (ι → ℂ) →ₗ⋆[ℂ] ℂ) (v : ι → ℂ) :
    ∑ k, ∑ j, X k j * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * A (H⁻¹ *ᵥ Pi.single j 1)) = - A (X *ᵥ v) := by
  have hinv' : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr hd)
  set w := X *ᵥ v with hw

  have hexp : w = ∑ j, (H *ᵥ w) j • (H⁻¹ *ᵥ Pi.single j 1) := by
    have h1 : H *ᵥ w = ∑ j, (H *ᵥ w) j • (Pi.single j (1 : ℂ) : ι → ℂ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    calc w = H⁻¹ *ᵥ (H *ᵥ w) := by rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
      _ = H⁻¹ *ᵥ ∑ j, (H *ᵥ w) j • (Pi.single j (1 : ℂ) : ι → ℂ) := by rw [← h1]
      _ = _ := by
        rw [Matrix.mulVec_sum]
        simp only [Matrix.mulVec_smul]
  have hA : A w = ∑ j, (starRingEnd ℂ) ((H *ᵥ w) j) * A (H⁻¹ *ᵥ Pi.single j 1) := by
    conv_lhs => rw [hexp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smulₛₗ, smul_eq_mul]

  have hcoef : ∀ j, ∑ k, X k j * (star v ⬝ᵥ H *ᵥ Pi.single k 1) = -(starRingEnd ℂ) ((H *ᵥ w) j) := by
    intro j
    have hs : ∀ k, star v ⬝ᵥ H *ᵥ Pi.single k 1 = (star v ᵥ* H) k := by
      intro k
      rw [Matrix.dotProduct_mulVec]
      simp [dotProduct, Pi.single_apply]
    have hXH : (H * X)ᴴ = -(H * X) := by
      rw [Matrix.conjTranspose_mul, hH]
      exact eq_neg_of_add_eq_zero_left hX
    have hstar : (starRingEnd ℂ) ((H *ᵥ w) j) = (star v ᵥ* (H * X)ᴴ) j := by
      rw [hw, Matrix.mulVec_mulVec, ← Matrix.star_mulVec]
      rfl
    simp_rw [hs]
    rw [hstar, hXH, Matrix.vecMul_neg, Pi.neg_apply, neg_neg, ← Matrix.vecMul_vecMul]
    simp [vecMul, dotProduct, mul_comm]
  rw [hA, Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ k, X k j * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * A (H⁻¹ *ᵥ Pi.single j 1))
      = (∑ k, X k j * (star v ⬝ᵥ H *ᵥ Pi.single k 1)) * A (H⁻¹ *ᵥ Pi.single j 1) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by
        rw [hcoef j]
        ring

theorem isQuadOf_normal {H X : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (hX : Xᴴ * H + H * X = 0) :
    IsQuadOf (fun x y => (star y ⬝ᵥ H *ᵥ x).im) (fun v => X *ᵥ v) (nC X) nP (nQ H) := by
  intro l v
  beta_reduce
  have hinv : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H (isUnit_iff_ne_zero.mpr hd)

  have hkj : ∀ k j, (∑ b1 : Bool, ∑ b2 : Bool, nC X (k, j, b1, b2) *
      (((star v ⬝ᵥ H *ᵥ nQ H (k, j, b1, b2)).im : ℂ) * l (nP (k, j, b1, b2)) +
        ((star v ⬝ᵥ H *ᵥ nP (k, j, b1, b2)).im : ℂ) * l (nQ H (k, j, b1, b2)))) =
      X k j * (-(1 / (4 * π))) * (I * (v j * linPart l (Pi.single k 1)) +
        (-I) * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * antiPart l (H⁻¹ *ᵥ Pi.single j 1))) := by
    intro k j
    have ha : ((star v ⬝ᵥ H *ᵥ (H⁻¹ *ᵥ Pi.single j 1)).im : ℂ) +
        I * ((star v ⬝ᵥ H *ᵥ (I • H⁻¹ *ᵥ Pi.single j 1)).im : ℂ) = I * v j := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, im_add_I_re, Matrix.mulVec_mulVec, hinv,
        Matrix.one_mulVec, dotProduct_single, mul_one, Pi.star_apply, starRingEnd_apply, star_star]
    have hp : ((star v ⬝ᵥ H *ᵥ Pi.single k 1).im : ℂ) -
        I * ((star v ⬝ᵥ H *ᵥ (I • Pi.single k 1)).im : ℂ) = -I * (star v ⬝ᵥ H *ᵥ Pi.single k 1) := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, im_sub_I_re]
    simp only [Fintype.sum_bool, nC, nP, nQ, Bool.false_eq_true, ↓reduceIte, linPart, antiPart, LinearMap.coe_mk, AddHom.coe_mk]
    linear_combination (X k j * (-(1 / (4 * π))) * (l (Pi.single k 1) - I * l (I • Pi.single k 1))) * ha +
      (X k j * (-(1 / (4 * π))) * (l (H⁻¹ *ᵥ Pi.single j 1) + I * l (I • H⁻¹ *ᵥ Pi.single j 1))) * hp
  have hsum : ∀ F : ι × ι × Bool × Bool → ℂ, ∑ i, F i = ∑ k, ∑ j, ∑ b1, ∑ b2, F (k, j, b1, b2) :=
    fun F => by simp only [Fintype.sum_prod_type]
  rw [hsum, Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => hkj k j]
  have hsplit : (∑ k, ∑ j, X k j * (-(1 / (4 * π))) * (I * (v j * linPart l (Pi.single k 1)) +
      (-I) * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * antiPart l (H⁻¹ *ᵥ Pi.single j 1)))) =
      (-(1 / (4 * π)) * I : ℂ) * ((∑ k, ∑ j, X k j * (v j * linPart l (Pi.single k 1))) -
        ∑ k, ∑ j, X k j * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * antiPart l (H⁻¹ *ᵥ Pi.single j 1))) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hLA : linPart l (X *ᵥ v) + antiPart l (X *ᵥ v) = 2 * l (X *ᵥ v) := by
    simp only [linPart, antiPart, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfin : ∀ z : ℂ, 2 * (π : ℂ) * I * (-(1 / (4 * (π : ℂ))) * I * (2 * z)) = z := by
    intro z
    rw [show 2 * (π : ℂ) * I * (-(1 / (4 * (π : ℂ))) * I * (2 * z)) = -(I * I) * ((π : ℂ) * (π : ℂ)⁻¹) * z by ring,
      I_mul_I, mul_inv_cancel₀ hπ]
    ring
  rw [hsplit, sum_lin, sum_anti hH hd hX, sub_neg_eq_add, hLA]
  exact hfin _

private theorem sm_add' {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {ρ : (ι → ℂ) → B →L[ℂ] B} {f g : B} (hf : Sm ρ f) (hg : Sm ρ g) : Sm ρ (f + g) := by
  unfold Sm at *
  simp only [map_add]
  exact hf.add hg

private theorem sm_smul' {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {ρ : (ι → ℂ) → B →L[ℂ] B} {f : B} (a : ℂ) (hf : Sm ρ f) : Sm ρ (a • f) := by
  unfold Sm at *
  simp only [map_smul]
  exact hf.const_smul a

theorem quad_normal (H X : Matrix ι ι ℂ) {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (ρ : (ι → ℂ) → B →L[ℂ] B) (f : B) (hs : ∀ v, Sm ρ (dH ρ v f)) :
    quad ρ (nC X) nP (nQ H) f = nOp ρ H X f := by
  have hy : ∀ j : ι, Sm ρ (dH ρ (H⁻¹ *ᵥ Pi.single j 1) f) := fun j => hs _
  have hIy : ∀ j : ι, Sm ρ (dH ρ (I • H⁻¹ *ᵥ Pi.single j 1) f) := fun j => hs _

  have hexp : ∀ (u : ι → ℂ) (j : ι), dH ρ u (dOp ρ H j f) = (-(1 / (4 * π)) : ℂ) •
      (dH ρ u (dH ρ (H⁻¹ *ᵥ Pi.single j 1) f) + I • dH ρ u (dH ρ (I • H⁻¹ *ᵥ Pi.single j 1) f)) := by
    intro u j
    unfold dOp
    rw [dH_smul u _ (sm_add' (hy j) (sm_smul' I (hIy j))),
      dH_add u (hy j) (sm_smul' I (hIy j)), dH_smul u I (hIy j)]
  unfold quad nOp xOp
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [nC, nP, nQ, Bool.false_eq_true, ↓reduceIte, hexp]
  module

def omH (H : Matrix ι ι ℂ) : (ι → ℂ) →L[ℝ] (ι → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((ι → ℂ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun x y : ι → ℂ => (star y ⬝ᵥ H *ᵥ x).im)
        (fun x x' y => by simp [mulVec_add])
        (fun r x y => by simp [mulVec_smul])
        (fun x y y' => by simp)
        (fun r x y => by simp))

theorem normal_quad : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H X : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → Xᴴ * H + H * X = 0 → ∃ (κ : Type) (_ : Fintype κ) (c : κ → ℂ) (p q : κ → ι → ℂ), IsQuadOf (fun x y => (star y ⬝ᵥ H *ᵥ x).im) (fun v => X *ᵥ v) c p q ∧ ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∀ f, Sm ρ f → quad ρ c p q f = nOp ρ H X f := by
  intro ι _ _ H X hH hd hX
  refine ⟨ι × ι × Bool × Bool, inferInstance, nC X, nP, nQ H, isQuadOf_normal hH hd hX, ?_⟩
  intro B _ _ ρ hρ f hf
  exact quad_normal H X ρ f fun v => DCalc.sm_dH (om := omH H) hρ hf v

end GlobalTheory.Mem.Lift.Normal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTransvectionMulVecMemSpanWeightVectorsDomin
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

noncomputable section

namespace GlobalTheory.AlgWtHW.LowerTransv

open Polynomial

def tGL {n : ℕ} (i j : Fin n) (h : i ≠ j) (s : ℂ) : GL (Fin n) ℂ :=
  ⟨transvection i j s, transvection i j (-s),
    by rw [transvection_mul_transvection_same i j h, add_neg_cancel, transvection_zero],
    by rw [transvection_mul_transvection_same i j h, neg_add_cancel, transvection_zero]⟩

theorem inv_val {n : ℕ} {i j : Fin n} (h : i ≠ j) (s : ℂ) (T : GL (Fin n) ℂ)
    (hT : T.val = transvection i j s) : (T⁻¹).val = transvection i j (-s) := by
  have e : T = tGL i j h s := Units.ext hT
  subst e
  rfl

theorem eval_evalRingHom {σ : Type} (g : σ → ℂ[X]) (Q : MvPolynomial σ ℂ) (s : ℂ) :
    (MvPolynomial.aeval g Q).eval s = MvPolynomial.eval (fun v => (g v).eval s) Q := by
  rw [MvPolynomial.aeval_def, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left]
  have : (Polynomial.evalRingHom s).comp (algebraMap ℂ ℂ[X]) = RingHom.id ℂ := by
    ext; simp
  rw [this]
  rfl

theorem expand {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ)
    (hΦ : IsPolyRep Φ) {i j : Fin n} (h : i ≠ j) (w : ι → ℂ) :
    ∃ q : ι → ℂ[X], ∀ (s : ℂ) (T : GL (Fin n) ℂ), T.val = transvection i j s →
      Φ T *ᵥ w = fun a => (q a).eval s := by
  choose Q hQ using hΦ.poly
  let g : (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ[X] :=
    Sum.elim (fun p => (transvection i j (X : ℂ[X])) p.1 p.2)
      (fun p => (transvection i j (-X : ℂ[X])) p.1 p.2)
  refine ⟨fun a => ∑ b, MvPolynomial.aeval g (Q a b) * C (w b), ?_⟩
  intro s T hT
  funext a
  simp only [mulVec, dotProduct, eval_finset_sum, eval_mul, eval_C, eval_evalRingHom]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hQ a b T]
  congr 2
  congr 1
  funext v
  rcases v with ⟨p1, p2⟩ | ⟨p1, p2⟩
  · simp only [g, Sum.elim_inl, hT, transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    split_ifs <;> simp
  · simp only [g, Sum.elim_inr, inv_val h s T hT, transvection, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> simp

end GlobalTheory.AlgWtHW.LowerTransv

namespace GlobalTheory.AlgWtHW.LowerTransv

open Polynomial

theorem diagonal_eq_of_isDiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsDiag) :
    A = diagonal (fun m => A m m) := by
  ext a b
  by_cases hab : a = b
  · subst hab; simp
  · simp [diagonal_apply_ne _ hab, hA hab]

theorem diag_ne_zero {n : ℕ} (D : GL (Fin n) ℂ) (hD : D.val.IsDiag) (m : Fin n) :
    D.val m m ≠ 0 := by
  have hdet : (D.val).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp D.isUnit).ne_zero
  rw [diagonal_eq_of_isDiag _ hD, det_diagonal] at hdet
  exact (Finset.prod_ne_zero_iff.mp hdet) m (Finset.mem_univ _)

theorem diagonal_mul_transvection {n : ℕ} {i j : Fin n} (h : i ≠ j) (d : Fin n → ℂ)
    (hdj : d j ≠ 0) (s : ℂ) :
    diagonal d * transvection i j s = transvection i j (s * (d i / d j)) * diagonal d := by
  ext a b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.add_apply, diagonal_mul, mul_diagonal, Matrix.single_apply]
  by_cases h2 : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h2
    simp only [and_self, if_true, one_apply_ne h]
    field_simp
    ring
  · simp only [h2, if_false, mul_zero, zero_mul, add_zero]
    by_cases hab : a = b
    · subst hab; simp
    · simp [one_apply_ne hab]

theorem conj_val {n : ℕ} {i j : Fin n} (h : i ≠ j) (D : GL (Fin n) ℂ) (hD : D.val.IsDiag)
    (s : ℂ) (T : GL (Fin n) ℂ) (hT : T.val = transvection i j s) :
    (D * T * D⁻¹).val = transvection i j (s * (D.val i i / D.val j j)) := by
  have key : D.val * T.val = transvection i j (s * (D.val i i / D.val j j)) * D.val := by
    have := diagonal_mul_transvection h (fun m => D.val m m) (diag_ne_zero D hD j) s
    rw [← diagonal_eq_of_isDiag _ hD] at this
    rw [hT]
    exact this
  rw [Units.val_mul, Units.val_mul, key, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.mul_one]

end GlobalTheory.AlgWtHW.LowerTransv

namespace GlobalTheory.AlgWtHW.LowerTransv

open Polynomial

def shiftWt {n : ℕ} (ν : Fin n → ℤ) (i j : Fin n) (k : ℕ) : Fin n → ℤ :=
  fun m => ν m + (k : ℤ) * (if m = i then 1 else 0) - (k : ℤ) * (if m = j then 1 else 0)

theorem prod_zpow_shiftWt {n : ℕ} (d : Fin n → ℂ) (hd : ∀ m, d m ≠ 0) (ν : Fin n → ℤ)
    (i j : Fin n) (k : ℕ) :
    ∏ m, d m ^ (shiftWt ν i j k m) = (∏ m, d m ^ ν m) * (d i / d j) ^ k := by
  have e : ∀ m, d m ^ (shiftWt ν i j k m) =
      d m ^ ν m * ((if m = i then d m ^ (k : ℤ) else 1) / (if m = j then d m ^ (k : ℤ) else 1)) := by
    intro m
    simp only [shiftWt]
    rw [zpow_sub₀ (hd m), zpow_add₀ (hd m), mul_div_assoc]
    split_ifs <;> simp
  rw [Finset.prod_congr rfl (fun m _ => e m), Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp [div_pow, zpow_natCast]

theorem domLE_shiftWt {n : ℕ} {ν lam : Fin n → ℤ} (hν : DomLE ν lam) {i j : Fin n} (hji : j < i)
    (k : ℕ) : DomLE (shiftWt ν i j k) lam := by
  obtain ⟨h1, h2⟩ := hν
  constructor
  · rw [← h1]
    simp only [shiftWt, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  · intro K
    have hK := h2 K
    simp only [shiftWt, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
    have hji' : (j : ℕ) < i := hji
    by_cases hi : (i : ℕ) < K
    · have hj : (j : ℕ) < K := lt_trans hji' hi
      simp only [hi, hj, if_true]
      linarith
    · simp only [hi, if_false, mul_zero, add_zero]
      have : (0 : ℤ) ≤ (k : ℤ) * (if (j : ℕ) < K then 1 else 0) := by
        split_ifs <;> simp
      linarith

theorem isWtVec_coeff {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (hΦ : IsPolyRep Φ) {i j : Fin n} (h : i ≠ j)
    (ν : Fin n → ℤ) (w : ι → ℂ) (hw : IsWtVec Φ ν w) (q : ι → ℂ[X])
    (hq : ∀ (s : ℂ) (T : GL (Fin n) ℂ), T.val = transvection i j s →
      Φ T *ᵥ w = fun a => (q a).eval s) (k : ℕ) :
    IsWtVec Φ (shiftWt ν i j k) (fun a => (q a).coeff k) := by
  intro D hD
  have hd : ∀ m, D.val m m ≠ 0 := diag_ne_zero D hD
  set c : ℂ := D.val i i / D.val j j with hc
  set P : ℂ := ∏ m, D.val m m ^ ν m with hP
  have hs : ∀ s : ℂ, Φ D *ᵥ (fun a => (q a).eval s) = P • (fun a => (q a).eval (s * c)) := by
    intro s
    have hT : (tGL i j h s).val = transvection i j s := rfl
    have hc' : Φ D * Φ (tGL i j h s) = Φ (D * tGL i j h s * D⁻¹) * Φ D := by
      rw [← hΦ.mul, ← hΦ.mul, inv_mul_cancel_right]
    rw [← hq s _ hT, ← hq (s * c) _ (conj_val h D hD s _ hT), mulVec_mulVec, hc',
      ← mulVec_mulVec, hw D hD, mulVec_smul]
  have hpoly : ∀ a, ∑ b, C (Φ D a b) * q b = C P * (q a).comp (C c * X) := by
    intro a
    apply Polynomial.funext
    intro s
    have e := congrFun (hs s) a
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
    simp only [eval_finset_sum, eval_mul, eval_C, eval_comp, eval_X]
    rw [e, mul_comm c s]
  funext a
  have e := congrArg (fun p => Polynomial.coeff p k) (hpoly a)
  simp only [finset_sum_coeff, coeff_C_mul, comp_C_mul_X_coeff] at e
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [e, prod_zpow_shiftWt _ hd]
  ring

end GlobalTheory.AlgWtHW.LowerTransv

namespace GlobalTheory.AlgWtHW

open Polynomial LowerTransv

theorem lowerTransvection_mulVec_mem_Sle : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (lam ν : Fin n → ℤ), DomLE ν lam →
    ∀ (w : ι → ℂ), IsWtVec Φ ν w → ∀ (i j : Fin n), j < i → ∀ (s : ℂ) (T : GL (Fin n) ℂ),
    T.val = transvection i j s → Φ T *ᵥ w ∈ Sle Φ lam := by
  intro n ι _ _ Φ hΦ lam ν hν w hw i j hji s T hT
  have h : i ≠ j := hji.ne'
  obtain ⟨q, hq⟩ := expand Φ hΦ h w
  set N : ℕ := (Finset.univ.sup fun a => (q a).natDegree) + 1 with hN
  have hsum : Φ T *ᵥ w = ∑ k ∈ Finset.range N, s ^ k • (fun a => (q a).coeff k) := by
    rw [hq s T hT]
    funext a
    rw [Finset.sum_apply]
    have hlt : (q a).natDegree < N :=
      Nat.lt_succ_of_le (Finset.le_sup (f := fun a => (q a).natDegree) (Finset.mem_univ a))
    rw [eval_eq_sum_range' hlt]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsum]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨shiftWt ν i j k, domLE_shiftWt hν hji k, isWtVec_coeff Φ hΦ h ν w hw q hq k⟩

end GlobalTheory.AlgWtHW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyRepMulVecMemOfCofiniteScalarShift
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem mulVec_mem_of_cofinite_shift : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (S : Submodule ℂ (ι → ℂ)) (v : ι → ℂ)
    (B : GL (Fin n) ℂ) (F : Set ℂ), F.Finite →
    (∀ s ∉ F, ∀ C : GL (Fin n) ℂ, C.val = B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ) → Φ C *ᵥ v ∈ S) →
    Φ B *ᵥ v ∈ S := by
  intro n ι _ _ Φ hΦ S v B F hF hS
  choose Q hQ using hΦ.poly
  let M : ℂ → Matrix (Fin n) (Fin n) ℂ := fun s => B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ)
  let x : ℂ → ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → ℂ :=
    fun s => Sum.elim (fun p => M s p.1 p.2) (fun p => (M s)⁻¹ p.1 p.2)
  let g : ℂ → ι → ℂ := fun s i => ∑ j, MvPolynomial.eval (x s) (Q i j) * v j
  have hMc : Continuous M := by
    fun_prop
  have hdetB : IsUnit (B.val).det := (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  have hM0 : M 0 = B.val := by simp [M]
  have hinvc : ContinuousAt (fun s => (M s)⁻¹) 0 := by
    have h1 : ContinuousAt Inv.inv (M 0) := by
      apply continuousAt_matrix_inv
      rw [hM0]
      exact NormedRing.inverse_continuousAt hdetB.unit
    exact h1.comp hMc.continuousAt
  have hxc : ContinuousAt x 0 := by
    rw [continuousAt_pi]
    rintro (p | p)
    · exact ((continuous_apply p.2).comp ((continuous_apply p.1).comp hMc)).continuousAt
    · exact ((continuous_apply p.2).comp (continuous_apply p.1)).continuousAt.comp hinvc
  have hgc : ContinuousAt g 0 := by
    rw [continuousAt_pi]
    intro i
    apply tendsto_finset_sum
    intro j _
    exact (((MvPolynomial.continuous_eval (Q i j)).continuousAt).comp hxc).mul continuousAt_const

  have hgC : ∀ s, ∀ C : GL (Fin n) ℂ, C.val = M s → g s = Φ C *ᵥ v := by
    intro s C hC
    funext i
    simp only [g, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hQ i j C]
    have hx : x s = Sum.elim (fun p => C.val p.1 p.2) (fun p => (C⁻¹).val p.1 p.2) := by
      funext q
      rcases q with p | p
      · simp [x, hC]
      · simp [x, Matrix.coe_units_inv, hC]
    rw [hx]
  have hg0 : g 0 = Φ B *ᵥ v := hgC 0 B hM0.symm
  have hdetev : ∀ᶠ s in nhds (0:ℂ), IsUnit (M s).det := by
    have hc : ContinuousAt (fun s => (M s).det) 0 := hMc.matrix_det.continuousAt
    have : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
    have hne : (M 0).det ≠ 0 := by rw [hM0]; exact hdetB.ne_zero
    filter_upwards [hc.eventually (this.mem_nhds hne)] with s hs
    exact isUnit_iff_ne_zero.2 hs
  have hFev : ∀ᶠ s in nhdsWithin (0:ℂ) {0}ᶜ, s ∉ F := by
    have hcl : IsClosed (F \ {0}) := (hF.diff).isClosed
    have hmem : (F \ {0})ᶜ ∈ nhds (0:ℂ) := hcl.isOpen_compl.mem_nhds (by simp)
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with s hs1 hs2
    intro hsF
    exact hs1 ⟨hsF, hs2⟩
  have hev : ∀ᶠ s in nhdsWithin (0:ℂ) {0}ᶜ, g s ∈ S := by
    filter_upwards [hFev, nhdsWithin_le_nhds hdetev] with s hs hdet
    rw [hgC s (Matrix.nonsingInvUnit (M s) hdet) rfl]
    exact hS s hs _ rfl
  have ht : Filter.Tendsto g (nhdsWithin (0:ℂ) {0}ᶜ) (nhds (Φ B *ᵥ v)) := by
    rw [← hg0]
    exact hgc.tendsto.mono_left nhdsWithin_le_nhds
  exact (Submodule.closed_of_finiteDimensional S).mem_of_tendsto ht hev

end GlobalTheory.AlgWtHW
end

