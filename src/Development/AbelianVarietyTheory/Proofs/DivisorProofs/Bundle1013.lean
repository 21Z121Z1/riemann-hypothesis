import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0973
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0924
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0131
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0979
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGramSchmidtIndefiniteHermitianFrames
section
noncomputable section

open Matrix GlobalTheory.HolDict ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open scoped ContDiff

namespace GlobalTheory.HolDict.GS

section Smooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}

theorem contDiffOn_det {m : Type} [Fintype m] [DecidableEq m] (f : E → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) : ContDiffOn ℝ ∞ (fun x => (f x).det) s := by
  simp only [Matrix.det_apply']
  refine ContDiffOn.sum fun σ _ => contDiffOn_const.mul ?_
  exact contDiffOn_prod fun i _ => hf _ _

theorem contDiffOn_minv {m : Type} [Fintype m] [DecidableEq m] (f : E → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hd : ∀ x ∈ s, (f x).det ≠ 0) (i j : m) :
    ContDiffOn ℝ ∞ (fun x => (f x)⁻¹ i j) s := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', Matrix.adjugate_apply]
  refine ((contDiffOn_det f hf).inv hd).mul (contDiffOn_det _ fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hf _ _

theorem contDiffOn_mmul {m : Type} [Fintype m] (f g : E → Matrix m m ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) s) (i j : m) :
    ContDiffOn ℝ ∞ (fun x => (f x * g x) i j) s := by
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun k _ => (hf _ _).mul (hg _ _)

theorem contDiffOn_Lm {n : ℕ} (f : E → Matrix (Fin n) (Fin n) ℂ)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hd : ∀ x ∈ s, ∀ k, lminor (f x) k ≠ 0) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun x => Lm (f x) i j) s := by
  simp only [Lm, Matrix.of_apply]
  split_ifs with h1 h2
  · refine ContDiffOn.neg ?_
    simp only [wv, vecMul, dotProduct]
    refine ContDiffOn.sum fun k _ => (hf _ _).mul ?_
    exact contDiffOn_minv (fun x => lb (f x) i) (fun a b => hf _ _) (fun x hx => hd x hx (Fin.castSucc i)) _ _
  · exact contDiffOn_const
  · exact contDiffOn_const

end Smooth

variable {n : ℕ}

theorem Lm_conj_diag (A : Mt n) (hA : Aᴴ = A) (hM : ∀ k, lminor A k ≠ 0) :
    Lm A * A * (Lm A)ᴴ = diagonal fun a => (Lm A * A) a a := by
  have hU : (Lm A * A).BlockTriangular id := fun a c h => Lm_mul_up A hM a c h
  have hL : ((Lm A)ᴴ).BlockTriangular id := fun a c h => by
    rw [conjTranspose_apply, Lm_up A c a h, star_zero]
  have hD := hU.mul hL
  have hH : (Lm A * A * (Lm A)ᴴ)ᴴ = Lm A * A * (Lm A)ᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA, Matrix.mul_assoc]
  ext a c
  rcases lt_trichotomy a c with h | h | h
  · rw [diagonal_apply_ne _ h.ne, ← hH, conjTranspose_apply, hD (show id a < id c from h), star_zero]
  · subst h
    rw [diagonal_apply_eq, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [conjTranspose_apply, Lm_diag, star_one, mul_one]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [hU (show id b < id a from h), zero_mul]
      · rw [hL (show id a < id b from h), mul_zero]
    · simp
  · rw [diagonal_apply_ne _ h.ne', hD (show id c < id a from h)]

theorem lminor_succ (A : Mt n) (hA : Aᴴ = A) (hM : ∀ k, lminor A k ≠ 0) (a : Fin n) :
    lminor A a.succ = lminor A a.castSucc * (Lm A * A) a a := by
  have key : ∀ i : Fin (n + 1), lminor A i = ∏ j : Fin i, (Lm A * A) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
      (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
    intro i
    have hN : ((Lm A)ᵀ).BlockTriangular id := fun a c h => Lm_up A c a h
    have h1 := FrameDegreeData.lminor_conj (A := A) hN i
    have h2 : (Lm A)ᵀᵀ * A * ((Lm A)ᵀ).map (starRingEnd ℂ) = Lm A * A * (Lm A)ᴴ := rfl
    rw [h2, Lm_conj_diag A hA hM] at h1
    simp only [transpose_apply, Lm_diag, Finset.prod_const_one, map_one, one_mul, mul_one] at h1
    rw [← h1, lminor, FrameDegreeData.det_sub_upper _ (blockTriangular_diagonal _)]
    simp only [diagonal_apply_eq]
  rw [key, key]
  exact Fin.prod_univ_castSucc (n := a) _

theorem diag_real (A : Mt n) (hA : Aᴴ = A) (hM : ∀ k, lminor A k ≠ 0) (a : Fin n) :
    (((Lm A * A) a a).re : ℂ) = (Lm A * A) a a := by
  have hH : (Lm A * A * (Lm A)ᴴ)ᴴ = Lm A * A * (Lm A)ᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA, Matrix.mul_assoc]
  rw [Lm_conj_diag A hA hM] at hH
  have := congrFun (congrFun hH a) a
  rw [conjTranspose_apply, diagonal_apply_eq] at this
  exact Complex.conj_eq_iff_re.mp this

theorem minor_ne {q : ℕ} {A : Mt n} (h : ∀ i : Fin (n + 1), 0 < psgn q i * (lminor A i).re) (k : Fin (n + 1)) :
    lminor A k ≠ 0 := fun h0 => by
  have := h k
  rw [h0] at this
  simp at this

theorem sgn_sq (q a : ℕ) : sgn q a * sgn q a = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem diag_pos {q : ℕ} (A : Mt n) (hA : Aᴴ = A) (h : ∀ i : Fin (n + 1), 0 < psgn q i * (lminor A i).re)
    (a : Fin n) : 0 < sgn q a * ((Lm A * A) a a).re := by
  have h1 := h a.succ
  have h2 := h a.castSucc
  rw [lminor_succ A hA (minor_ne h) a, ← diag_real A hA (minor_ne h) a, Complex.re_mul_ofReal] at h1
  simp only [Fin.val_succ, psgn, Finset.prod_range_succ, Fin.val_castSucc] at h1 h2
  have e : (∏ x ∈ Finset.range a, sgn q x) * sgn q a * ((lminor A a.castSucc).re * ((Lm A * A) a a).re) =
      ((∏ x ∈ Finset.range a, sgn q x) * (lminor A a.castSucc).re) * (sgn q a * ((Lm A * A) a a).re) := by ring
  rw [e] at h1
  exact (pos_iff_pos_of_mul_pos h1).mp h2

def fac (q : ℕ) (A : Mt n) : Mt n :=
  diagonal (fun a : Fin n => (((Real.sqrt (sgn q a * ((Lm A * A) a a).re))⁻¹ : ℝ) : ℂ)) * (Lm A * A)

theorem fac_spec {q : ℕ} (A : Mt n) (hA : Aᴴ = A) (h : ∀ i : Fin (n + 1), 0 < psgn q i * (lminor A i).re) :
    UpT (fac q A) ∧ ((fac q A)⁻¹)ᴴ * A * (fac q A)⁻¹ = diagonal fun a : Fin n => ((sgn q a : ℝ) : ℂ) := by
  set d : Fin n → ℝ := fun a => ((Lm A * A) a a).re with hd
  set r : Fin n → ℝ := fun a : Fin n => Real.sqrt (sgn q a * d a) with hr
  have hpos : ∀ a : Fin n, 0 < sgn q a * d a := diag_pos A hA h
  have hr0 : ∀ a, r a ≠ 0 := fun a => (Real.sqrt_pos.mpr (hpos a)).ne'
  have hr2 : ∀ a : Fin n, r a * r a = sgn q a * d a := fun a => Real.mul_self_sqrt (hpos a).le
  have hd0 : ∀ a, d a ≠ 0 := fun a h0 => by have := hpos a; rw [h0] at this; simp at this
  have hD : Lm A * A * (Lm A)ᴴ = diagonal fun a => (d a : ℂ) := by
    rw [Lm_conj_diag A hA (minor_ne h)]
    congr 1
    funext a
    exact (diag_real A hA (minor_ne h) a).symm
  have hone : fac q A * ((Lm A)ᴴ * diagonal fun a => ((r a / d a : ℝ) : ℂ)) = 1 := by
    rw [fac, Matrix.mul_assoc, ← Matrix.mul_assoc (Lm A * A), hD, diagonal_mul_diagonal, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext a
    have h1 := hr0 a
    have h2 := hd0 a
    change (((r a)⁻¹ : ℝ) : ℂ) * _ = _
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    field_simp
  refine ⟨⟨(Matrix.isUnit_det_of_right_inverse hone).ne_zero, fun a c hc => ?_⟩, ?_⟩
  · rw [fac, diagonal_mul, Lm_mul_up A (minor_ne h) a c hc, mul_zero]
  · rw [Matrix.inv_eq_right_inv hone, conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
    have e : ∀ X Y : Mt n, X * Lm A * A * ((Lm A)ᴴ * Y) = X * (Lm A * A * (Lm A)ᴴ) * Y := fun X Y => by
      simp only [Matrix.mul_assoc]
    rw [e, hD, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext a
    have h2 := hd0 a
    have h3 := hr2 a
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp
    linear_combination h3

theorem contDiffOn_fac {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} (q : ℕ) (f : E → Mt n)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hA : ∀ x ∈ s, (f x)ᴴ = f x)
    (h : ∀ x ∈ s, ∀ i : Fin (n + 1), 0 < psgn q i * (lminor (f x) i).re) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun x => fac q (f x) i j) s := by
  have hU := contDiffOn_mmul (fun x => Lm (f x)) f
    (contDiffOn_Lm f hf fun x hx => minor_ne (h x hx)) hf
  simp only [fac, diagonal_mul]
  refine ContDiffOn.mul ?_ (hU i j)
  refine Complex.ofRealCLM.contDiff.comp_contDiffOn
    (f := fun x => (Real.sqrt (sgn q i * ((Lm (f x) * f x) i i).re))⁻¹) ?_
  refine ContDiffOn.inv (ContDiffOn.sqrt (contDiffOn_const.mul
    (Complex.reCLM.contDiff.comp_contDiffOn (hU i i))) fun x hx => (diag_pos _ (hA x hx) (h x hx) i).ne')
    fun x hx => (Real.sqrt_pos.mpr (diag_pos _ (hA x hx) (h x hx) i)).ne'

theorem smooth_gramSchmidt : ∀ (n : ℕ) (Hm : Mt n) (q : ℕ) (x₀ : Mt n), OrthFr Hm q x₀ →
    ∃ β : (Fin n → Fin n → ℂ) → (Fin n → Fin n → ℂ), ContDiffOn ℝ ∞ β {x | Matrix.of x ∈ frDom Hm q} ∧
      ∀ x : Fin n → Fin n → ℂ, Matrix.of x ∈ frDom Hm q → UpT (Matrix.of (β x)) ∧
        Matrix.of x * (Matrix.of (β x))⁻¹ * x₀⁻¹ ∈ Formalism.QuantumDeterminants.UH Hm := by
  intro n Hm q x₀ ⟨_, h0⟩
  have hdet : IsUnit x₀.det := by
    have := congrArg Matrix.det h0
    rw [det_mul, det_diagonal] at this
    refine isUnit_iff_ne_zero.mpr fun hz => ?_
    rw [hz, mul_zero] at this
    refine Finset.prod_ne_zero_iff.mpr (fun a _ => ?_) this.symm
    unfold sgn
    split_ifs <;> simp
  have hHm : ∀ X : Mt n, X = x₀ᴴ * Hm * x₀ → (x₀⁻¹)ᴴ * X * x₀⁻¹ = Hm := by
    rintro X rfl
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_assoc,
      mul_nonsing_inv _ hdet, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hH : Hmᴴ = Hm := by
    rw [← hHm _ h0.symm]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose, Matrix.mul_assoc]
    congr 3
    funext a
    simp
  have hA : ∀ x : Mt n, (-(xᴴ * Hm * x))ᴴ = -(xᴴ * Hm * x) := fun x => by
    simp only [conjTranspose_neg, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc]
  refine ⟨fun x i j => fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)) i j, ?_, fun x hx => ?_⟩
  · refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
    refine contDiffOn_fac q (fun x => -((Matrix.of x)ᴴ * Hm * Matrix.of x)) (fun a b => ?_) (fun x _ => hA _)
      (fun x hx => hx.2) i j
    simp only [Matrix.neg_apply]
    have hx : ∀ a b : Fin n, ContDiff ℝ ∞ fun x : Fin n → Fin n → ℂ => x a b := fun a b => by fun_prop
    refine (contDiffOn_mmul _ _ (contDiffOn_mmul _ (fun _ => Hm) (fun a b => ?_) fun _ _ => contDiffOn_const)
      (fun a b => (hx a b).contDiffOn) a b).neg
    exact (Complex.conjCLE.contDiff.comp (hx b a)).contDiffOn
  · obtain ⟨h1, h2⟩ := fac_spec _ (hA (Matrix.of x)) hx.2
    refine ⟨h1, ?_⟩
    change (Matrix.of x * (fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)))⁻¹ * x₀⁻¹)ᴴ * Hm *
      (Matrix.of x * (fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)))⁻¹ * x₀⁻¹) = Hm
    generalize (fac q (-((Matrix.of x)ᴴ * Hm * Matrix.of x)))⁻¹ = γ at h2 ⊢
    have h3 : γᴴ * ((Matrix.of x)ᴴ * Hm * Matrix.of x) * γ = x₀ᴴ * Hm * x₀ := by
      rw [h0, ← diagonal_neg, ← h2]
      simp
    refine Eq.trans ?_ (hHm _ h3)
    simp only [conjTranspose_mul, Matrix.mul_assoc]

end GlobalTheory.HolDict.GS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingAffineFamilyEqIntegralKernel
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf.SecAffine

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem htInf_inv_eq (g : GL (Fin n) (Cinf E)) : htInf g⁻¹ = htInf g := by
  unfold htInf
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [map_inv, htGL_inv]

end GlobalTheory.JSW.MirCinf.SecAffine

namespace GlobalTheory.JSW.MirCinf

theorem smoothMatInf_affine_eq_integral_secKInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) → (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → (∀ z a, χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) * α a = ∫ x, κ x * (𝐞 (τ x (z, a)) : ℂ) ∂ν) → ∃ R : ℝ, ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → ∀ q z g, χ z * smoothMatInf α W (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹ * q) = ∫ p, secKInf R σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1)) ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) := by
  classical
  intro E _ _ n Z _ _ _ σ₀ L χ α hχ hσ hα hαu X _ ν _ κ τ hκ hτ hmom hk
  obtain ⟨R1, hR1⟩ : ∃ R1 : ℝ, ∀ z ∈ tsupport χ, htInf (toGLInf (Matrix.of (σ₀ + L z))) ≤ R1 := by
    have hc : ContinuousOn (fun z => htInf (toGLInf (Matrix.of (σ₀ + L z)))) (tsupport χ) :=
      SmoothGrowth.continuous_htInf.comp_continuousOn (SmoothGrowth.continuousOn_toGLInf.comp
        (by fun_prop : Continuous fun z => σ₀ + L z).continuousOn fun z hz => hσ z hz)
    obtain ⟨C, hC⟩ := hχ.isCompact.exists_bound_of_continuousOn hc
    exact ⟨C, fun z hz => (Real.le_norm_self _).trans (hC z hz)⟩
  obtain ⟨R2, hR2⟩ : ∃ R2 : ℝ, ∀ a ∈ tsupport α, htInf (toGLInf (Matrix.of a)) ≤ R2 := by
    have hc : ContinuousOn (fun a : Fin n → Fin n → Cinf E => htInf (toGLInf (Matrix.of a))) (tsupport α) :=
      SmoothGrowth.continuous_htInf.comp_continuousOn (SmoothGrowth.continuousOn_toGLInf.mono hαu)
    obtain ⟨C, hC⟩ := hα.isCompact.exists_bound_of_continuousOn hc
    exact ⟨C, fun a ha => (Real.le_norm_self _).trans (hC a ha)⟩
  refine ⟨R1 * R2, ?_⟩
  intro W hW q z g
  have hfam := GlobalTheory.T.schwartz_integral_bound_smooth E n Z X ν κ τ hκ hτ hmom (R1 * R2) σ₀ L
  have hrap : IsRapidFInf ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) (secKInf (R1 * R2) σ₀ κ τ q)
      (fun p => toGLInf (Matrix.of p.1)) (secEtaInf L τ q) := by
    obtain ⟨h1, h2, h3⟩ := hfam
    obtain ⟨m1, m2⟩ := h2 Unit (fun _ => q) (fun _ _ => measurable_const)
    refine ⟨m1.comp ((measurable_const (a := ()) : Measurable fun _ : (Fin n → Fin n → Cinf E) × X => ()).prodMk measurable_id), h1,
      fun z => (m2 z).comp ((measurable_const (a := ()) : Measurable fun _ : (Fin n → Fin n → Cinf E) × X => ()).prodMk measurable_id), fun N => ?_⟩
    obtain ⟨C, M, hC⟩ := h3 N
    exact (hC q).1
  have hint : Integrable (fun p : (Fin n → Fin n → Cinf E) × X => secKInf (R1 * R2) σ₀ κ τ q p *
      (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1))) ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) :=
    hrap.integrable hW z g
  have hinner : ∀ h : Fin n → Fin n → Cinf E, ∫ x, secKInf (R1 * R2) σ₀ κ τ q (h, x) * (𝐞 (secEtaInf L τ q (h, x) z) : ℂ) *
      W (g * toGLInf (Matrix.of (h, x).1)) ∂ν =
      (if IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q then
        ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) else 0) *
      (χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) *
        α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) *
      W (g * toGLInf (Matrix.of h)) := by
    intro h
    rw [hk z]
    by_cases hc : IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q
    · have hsum : ((0 : Z), sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of h) σ₀) +
          (z, sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of h) (L z)) =
          (z, fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) := by
        rw [Prod.mk_add_mk, zero_add]
        congr 1
        funext i j
        simp only [Pi.add_apply, sandCLMInf_apply]
        rw [← Matrix.add_apply, ← Matrix.add_mul, ← Matrix.mul_add]
        rfl
      have e : ∀ x, secKInf (R1 * R2) σ₀ κ τ q (h, x) * (𝐞 (secEtaInf L τ q (h, x) z) : ℂ) *
          W (g * toGLInf (Matrix.of (h, x).1)) =
          (((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) *
            W (g * toGLInf (Matrix.of h))) *
          (κ x * (𝐞 (τ x (z, fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) *
            Matrix.of (σ₀ + L z) * Matrix.of h) i j)) : ℂ)) := by
        intro x
        simp only [secKInf, secEtaInf, if_pos hc]
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.comp_apply, ← hsum, map_add, AddChar.map_add_eq_mul, Circle.coe_mul]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul, if_pos hc]
      ring
    · simp [secKInf, if_neg hc]
  have hR : ∫ p, secKInf (R1 * R2) σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1))
      ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) = ∫ h : Fin n → Fin n → Cinf E,
      (if IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q then
        ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) else 0) *
      (χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) *
        α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) *
      W (g * toGLInf (Matrix.of h)) := by
    rw [integral_prod _ hint]
    exact integral_congr_ae (Filter.Eventually.of_forall hinner)
  rw [hR]
  by_cases hz : χ z = 0
  · simp [hz]
  have hzK : z ∈ tsupport χ := subset_tsupport _ hz
  have hu := hσ z hzK
  set σ' := toGLInf (Matrix.of (σ₀ + L z)) with hσ'
  have hσv : (σ' : Matrix (Fin n) (Fin n) (Cinf E)) = Matrix.of (σ₀ + L z) := val_toGLInf hu
  rw [smoothMatInf, GlobalTheory.T.integral_archimedeanMatrices_leftMul_jacobian E n (q⁻¹ * σ'), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only
  have hAh : Matrix.of (fun i j => (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) =
      ((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h := rfl
  have ha : (fun i j => (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) =
      (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) := by
    rw [Units.val_mul, hσv]
  rw [hAh, ha]
  by_cases hαz : α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) = 0
  · rw [hαz]; ring
  have hmem := subset_tsupport _ hαz
  have hAu : IsUnit (Matrix.of (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) := hαu hmem
  rw [← ha] at hAu hmem
  rw [hAh] at hAu
  have hh : IsUnit (Matrix.of h) := (Units.isUnit_units_mul _ _).1 hAu
  have ht : toGLInf (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = (q⁻¹ * σ') * toGLInf (Matrix.of h) :=
    Units.ext (by rw [val_toGLInf hAu, Units.val_mul (q⁻¹ * σ'), val_toGLInf hh])
  have hb1 := hR1 z hzK
  have hb2 : htInf (toGLInf (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h)) ≤ R2 := hR2 _ hmem
  rw [ht] at hb2
  have hb1' : htInf σ' ≤ R1 := hb1
  have hbound : htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q := by
    have e1 : toGLInf (Matrix.of h) = (q⁻¹ * σ')⁻¹ * (q⁻¹ * σ' * toGLInf (Matrix.of h)) := by group
    have p1 := htInf_pos' σ'
    have p2 := htInf_pos' (q⁻¹ * σ' * toGLInf (Matrix.of h))
    have p3 := htInf_pos' q
    calc htInf (toGLInf (Matrix.of h)) = htInf ((q⁻¹ * σ')⁻¹ * (q⁻¹ * σ' * toGLInf (Matrix.of h))) := by rw [← e1]
      _ ≤ htInf ((q⁻¹ * σ')⁻¹) * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) := htInf_mul_le _ _
      _ = htInf (q⁻¹ * σ') * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) := by rw [SecAffine.htInf_inv_eq]
      _ ≤ (htInf q⁻¹ * htInf σ') * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) :=
          mul_le_mul_of_nonneg_right (htInf_mul_le _ _) p2.le
      _ = htInf q * (htInf σ' * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h))) := by rw [SecAffine.htInf_inv_eq]; ring
      _ ≤ htInf q * (R1 * R2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hb1' hb2 p2.le (p1.le.trans hb1')) p3.le
      _ = R1 * R2 * htInf q := by ring
  rw [if_pos ⟨hh, hbound⟩]
  have hG : ((g * σ'⁻¹ * q : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) *
      (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = (g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h := by
    rw [← Matrix.mul_assoc, ← Units.val_mul]
    congr 2
    group
  have hgt : toGLInf ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = g * toGLInf (Matrix.of h) :=
    Units.ext (by rw [val_toGLInf (g.isUnit.mul hh), Units.val_mul, val_toGLInf hh])
  rw [hG, onMatInf_of_isUnit W (g.isUnit.mul hh), hgt, Units.val_mul, jacInf_mul, hσv]
  push_cast
  ring

end GlobalTheory.JSW.MirCinf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabIffLoc
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsomTransport

section Ring

variable {A : Type} [CommRing A] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def conjGL (φ : Matrix m n A) (ψ : Matrix n m A) (h1 : φ * ψ = 1) (h2 : ψ * φ = 1) (g : GL n A) : GL m A where
  val := φ * g.1 * ψ
  inv := φ * (g⁻¹).1 * ψ
  val_inv := by
    rw [Matrix.mul_assoc (φ * g.1), ← Matrix.mul_assoc ψ, ← Matrix.mul_assoc ψ, h2, Matrix.one_mul,
      ← Matrix.mul_assoc, Matrix.mul_assoc φ, Units.mul_inv, Matrix.mul_one, h1]
  inv_val := by
    rw [Matrix.mul_assoc (φ * (g⁻¹).1), ← Matrix.mul_assoc ψ, ← Matrix.mul_assoc ψ, h2, Matrix.one_mul,
      ← Matrix.mul_assoc, Matrix.mul_assoc φ, Units.inv_mul, Matrix.mul_one, h1]

omit [DecidableEq n] in
theorem conj_unitary (σ : A →+* A) (φ : Matrix m n A) (ψ : Matrix n m A) (h1 : φ * ψ = 1)
    (J : Matrix n n A) (J' : Matrix m m A) (hJ : Formalism.UG.cT σ φ * J' * φ = J) (g : Matrix n n A)
    (hg : Formalism.UG.cT σ g * J * g = J) :
    Formalism.UG.cT σ (φ * g * ψ) * J' * (φ * g * ψ) = J' := by
  have e1 : Formalism.UG.cT σ (φ * g * ψ) * J' * (φ * g * ψ) =
      Formalism.UG.cT σ ψ * (Formalism.UG.cT σ g * (Formalism.UG.cT σ φ * J' * φ) * g) * ψ := by
    simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
  have e2 : Formalism.UG.cT σ (φ * ψ) * J' * (φ * ψ) =
      Formalism.UG.cT σ ψ * (Formalism.UG.cT σ φ * J' * φ) * ψ := by
    simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
  rw [e1, hJ, hg, ← hJ, ← e2, h1, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

end Ring

theorem stab_iff_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F))
    (g : HA (AF F) hc.sig V.gram) (hg : ∀ w, w ≠ v → locMat hc V w g = 1) :
    Stab hc V g ↔ ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔
      (locMat hc V v g).1.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
  have hev : ∀ w (y : Fin V.rank → Af F ⊗[F] E),
      (fun i => evF E w ((finMat hc.sig V.gram g).mulVec y i)) =
        (locMat hc V w g).1.mulVec fun i => evF E w (y i) := fun w y => by
    funext i
    rw [locMat_val]
    exact RingHom.map_mulVec (evF E w) _ y i
  constructor
  · intro hs x
    have hx : ∀ w, w ≠ v → (fun i => evF E w (sgT E v (x i))) = 0 := fun w hw =>
      funext fun i => evF_sgT_ne hw _
    have hxv : (fun i => evF E v (sgT E v (x i))) = x := funext fun i => evF_sgT_self v _
    have := hs fun i => sgT E v (x i)
    rw [mem_lamHat_iff, mem_lamHat_iff] at this
    simp only [hev] at this
    constructor
    · intro h0
      have h1 := this.1 (fun w => by
        by_cases hw : w = v
        · subst hw; rw [hxv]; exact h0
        · rw [hx w hw]; exact zero_mem _) v
      rwa [hxv] at h1
    · intro h0
      have h1 := this.2 (fun w => by
        by_cases hw : w = v
        · subst hw; rw [hxv]; exact h0
        · rw [hx w hw, Matrix.mulVec_zero]; exact zero_mem _) v
      rwa [hxv] at h1
  · intro hs y
    rw [mem_lamHat_iff, mem_lamHat_iff]
    refine forall_congr' fun w => ?_
    rw [hev]
    by_cases hw : w = v
    · subst hw; exact hs _
    · rw [hg w hw, Units.val_one, Matrix.one_mulVec]

theorem transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V V' : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (f : AF F ⊗[F] E) (φ : Matrix (Fin V'.rank) (Fin V.rank) (Fv F v ⊗[F] E)) (ψ : Matrix (Fin V.rank) (Fin V'.rank) (Fv F v ⊗[F] E)), IsIdemOf E v f → φ * ψ = 1 → ψ * φ = 1 → (∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔ φ.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V' v) → (Formalism.UG.cT (sigR (Fv F v) hc.sig) φ * JR (Fv F v) V'.gram : Matrix (Fin V.rank) (Fin V'.rank) (Fv F v ⊗[F] E)) * φ = JR (Fv F v) V.gram → ∀ g, Supp hc V f g → ∃ g', Supp hc V' f g' ∧ (locMat hc V' v g').1 = φ * (locMat hc V v g).1 * ψ ∧ (Stab hc V' g' ↔ Stab hc V g) := by
  intro F E _ _ _ _ _ _ hc V V' v f φ ψ hf h1 h2 hL hJ g hg
  have hu : conjGL φ ψ h1 h2 (locMat hc V v g) ∈ HR (Fv F v) hc.sig V'.gram :=
    conj_unitary _ φ ψ h1 _ _ hJ _ (locMat_mem hc V v g)
  obtain ⟨g', hg', e⟩ := (GlobalTheory.SuppLocal.supp_local F E hc V' v f hf).2.2 _ hu
  have e' : (locMat hc V' v g').1 = φ * (locMat hc V v g).1 * ψ := by rw [e]; rfl
  refine ⟨g', hg', e', ?_⟩
  rw [stab_iff_loc hc V' v g' ((GlobalTheory.SuppLocal.supp_iff hc V' hf g').1 hg').2,
    stab_iff_loc hc V v g ((GlobalTheory.SuppLocal.supp_iff hc V hf g).1 hg).2, e']
  constructor
  · intro hs x
    have := hs (φ.mulVec x)
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mulVec_mulVec] at this
    rw [hL, hL ((locMat hc V v g).1.mulVec x)]
    exact this
  · intro hs y
    have := hs (ψ.mulVec y)
    rw [hL, hL ((locMat hc V v g).1.mulVec _), Matrix.mulVec_mulVec, h1, Matrix.one_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    exact this

end GlobalTheory.IsomTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricDenominatorOfZetaDenominatorsStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_denominator_of_zeta_denominators : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → LatIntRam → LatIntUnr → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator := by
  first | exact @GlobalTheory.ToricDenomRow.toricDenominator | exact GlobalTheory.ToricDenomRow.toricDenominator | (intros; apply GlobalTheory.ToricDenomRow.toricDenominator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumCoordinateIsAlgebraicStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricSum_coordinate_isAlgebraic : ∀ (hA : LatAlg) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΛ : IsLatOf ι 1 Λ₀) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (T : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T), IsAlgebraic ℚ (coordIn E d s κ Ω₀ T) := by
  first | exact @GlobalTheory.ToricCoordAlg.isAlgebraic_coordIn | exact GlobalTheory.ToricCoordAlg.isAlgebraic_coordIn | (intros; apply GlobalTheory.ToricCoordAlg.isAlgebraic_coordIn <;> assumption)
end

