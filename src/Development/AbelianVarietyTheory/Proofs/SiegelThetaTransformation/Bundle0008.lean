import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0005
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CanonicalThetaExponentSymplecticInvariant
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

theorem isUnit_det_im_of_mem_siegel {ι : Type} [Fintype ι] [DecidableEq ι] {τ : Matrix ι ι ℂ}
    (hτ : τ ∈ Siegel ι) : IsUnit (τ.map fun z => (z.im : ℂ)).det := by
  have h : (τ.map fun z => (z.im : ℂ)) = Complex.ofRealHom.mapMatrix (τ.map Complex.im) := by
    ext i j; simp
  rw [h, ← RingHom.map_det]
  exact (hτ.2.det_pos.ne'.isUnit).map _

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_add' {α β : Type} (M N : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm (M + N) = _root_.GlobalTheory.SW.qm M + _root_.GlobalTheory.SW.qm N := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_neg' {α β : Type} (M : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm (-M) = -_root_.GlobalTheory.SW.qm M := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_mul_siegel_theta_transformation {α β γ : Type} [Fintype β] (M : Matrix α β ℚ) (N : Matrix β γ ℚ) :
    _root_.GlobalTheory.SW.qm (M * N) = _root_.GlobalTheory.SW.qm M * _root_.GlobalTheory.SW.qm N := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm, Matrix.mul_apply]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_transpose' {α β : Type} (M : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm Mᵀ = (_root_.GlobalTheory.SW.qm M)ᵀ := rfl

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_zero' {α β : Type} : _root_.GlobalTheory.SW.qm (0 : Matrix α β ℚ) = 0 := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_one' : _root_.GlobalTheory.SW.qm (1 : Matrix ι ι ℚ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [_root_.GlobalTheory.SW.qm, one_apply, h]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma sub_conjTranspose_of_isSymm (τ : Matrix ι ι ℂ) (hτ : τ.IsSymm) :
    τ - τᴴ = (2 * I) • τ.map fun z => (z.im : ℂ) := by
  ext i j
  have h := hτ.apply i j
  simp only [Matrix.sub_apply, conjTranspose_apply, Matrix.smul_apply, map_apply, smul_eq_mul, h]
  rw [show star (τ i j) = conj (τ i j) from rfl, Complex.sub_conj]
  push_cast
  ring

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_conjTranspose_eq_transpose {α β : Type} (M : Matrix α β ℚ) :
    (_root_.GlobalTheory.SW.qm M)ᴴ = (_root_.GlobalTheory.SW.qm M)ᵀ := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm, conjTranspose_apply]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma re_star_dotProduct_ofReal_mulVec (Y : Matrix ι ι ℝ) (v : ι → ℂ) :
    (star v ⬝ᵥ (Y.map (fun t => (t : ℂ)) *ᵥ v)).re =
      (fun i => (v i).re) ⬝ᵥ (Y *ᵥ fun i => (v i).re) + (fun i => (v i).im) ⬝ᵥ (Y *ᵥ fun i => (v i).im) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re, Complex.mul_im]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma dotProduct_transpose_mulVec_self (N : Matrix ι ι ℂ) (ζ : ι → ℂ) :
    ζ ⬝ᵥ (Nᵀ *ᵥ ζ) = ζ ⬝ᵥ (N *ᵥ ζ) := by
  rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]

open Matrix Complex in
open scoped ComplexConjugate Real in

theorem _root_.GlobalTheory.SW.canon_exponent_invariant : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ _root_.GlobalTheory.SW.Siegel ι, ∀ ζ : ι → ℂ, (ζ ᵥ* (_root_.GlobalTheory.SW.spDen σ τ)⁻¹) ⬝ᵥ ((_root_.GlobalTheory.SW.spAct σ τ).map fun z => (z.im : ℂ))⁻¹ *ᵥ (ζ ᵥ* (_root_.GlobalTheory.SW.spDen σ τ)⁻¹) + 2 * I * (ζ ⬝ᵥ ((_root_.GlobalTheory.SW.spDen σ τ)⁻¹ * _root_.GlobalTheory.SW.qm σ.toBlocks₂₁) *ᵥ ζ) = ζ ⬝ᵥ (τ.map fun z => (z.im : ℂ))⁻¹ *ᵥ ζ := by
  intro ι _ _ σ hσ τ hτ ζ
  obtain ⟨hsym, hpos⟩ := hτ
  have h2 := SymplecticGroup.mem_iff'.mp hσ
  rw [← fromBlocks_toBlocks σ] at h2
  simp [Matrix.J, fromBlocks_transpose, fromBlocks_multiply] at h2
  obtain ⟨r1, r2, r3, r4⟩ := h2
  replace r1 := congrArg _root_.GlobalTheory.SW.qm r1
  replace r2 := congrArg _root_.GlobalTheory.SW.qm r2
  replace r3 := congrArg _root_.GlobalTheory.SW.qm r3
  replace r4 := congrArg _root_.GlobalTheory.SW.qm r4
  simp only [qm_add', qm_neg', qm_mul_siegel_theta_transformation, qm_transpose',
    qm_zero', qm_one'] at r1 r2 r3 r4
  set A := _root_.GlobalTheory.SW.qm σ.toBlocks₁₁ with hA
  set B := _root_.GlobalTheory.SW.qm σ.toBlocks₁₂ with hB
  set C := _root_.GlobalTheory.SW.qm σ.toBlocks₂₁ with hC
  set D := _root_.GlobalTheory.SW.qm σ.toBlocks₂₂ with hD
  set J := _root_.GlobalTheory.SW.spDen σ τ with hJdef
  have hJ : J = C * τ + D := rfl
  set M := A * τ + B with hM
  have hact : _root_.GlobalTheory.SW.spAct σ τ = M * J⁻¹ := rfl
  set Y := τ.map fun z => (z.im : ℂ) with hYdef
  have hY : τ - τᴴ = (2 * I) • Y := sub_conjTranspose_of_isSymm τ hsym
  have hτt : τᵀ = τ := hsym
  have hCh : Cᴴ = Cᵀ := qm_conjTranspose_eq_transpose _
  have hDh : Dᴴ = Dᵀ := qm_conjTranspose_eq_transpose _
  have hAh : Aᴴ = Aᵀ := qm_conjTranspose_eq_transpose _
  have hBh : Bᴴ = Bᵀ := qm_conjTranspose_eq_transpose _
  have hI1 : Jᴴ * M - Mᴴ * J = τ - τᴴ := by
    rw [hJ, hM, conjTranspose_add, conjTranspose_add, conjTranspose_mul, conjTranspose_mul, hCh, hDh, hAh, hBh]
    have hE : (τᴴ * Cᵀ + Dᵀ) * (A * τ + B) - (τᴴ * Aᵀ + Bᵀ) * (C * τ + D) =
        τᴴ * (Cᵀ * A + -(Aᵀ * C)) * τ + τᴴ * (Cᵀ * B + -(Aᵀ * D)) + (Dᵀ * A + -(Bᵀ * C)) * τ +
          (Dᵀ * B + -(Bᵀ * D)) := by noncomm_ring
    rw [hE, r1, r2, r3, r4]
    noncomm_ring
  have hI2 : Mᵀ * J = Jᵀ * M := by
    rw [hJ, hM, transpose_add, transpose_add, transpose_mul, transpose_mul, hτt]
    have hE : (τ * Aᵀ + Bᵀ) * (C * τ + D) - (τ * Cᵀ + Dᵀ) * (A * τ + B) =
        -(τ * (Cᵀ * A + -(Aᵀ * C)) * τ) - τ * (Cᵀ * B + -(Aᵀ * D)) - (Dᵀ * A + -(Bᵀ * C)) * τ -
          (Dᵀ * B + -(Bᵀ * D)) := by noncomm_ring
    rw [r1, r2, r3, r4] at hE
    rw [← sub_eq_zero, hE]
    noncomm_ring
  have hYr : Y = (τ.map Complex.im).map (fun t => (t : ℂ)) := rfl
  have hdetY : Y.det ≠ 0 := by
    have : Y.det = ((τ.map Complex.im).det : ℂ) := by
      rw [hYr]
      exact (RingHom.map_det Complex.ofRealHom _).symm
    rw [this, Complex.ofReal_ne_zero]
    exact hpos.det_pos.ne'
  have h2I : (2 * I : ℂ) ≠ 0 := by simp
  have hdetJ : J.det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have h0 : star v ⬝ᵥ ((Jᴴ * M - Mᴴ * J) *ᵥ v) = 0 := by
      rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec, hJv, mulVec_zero,
        dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hJv, star_zero, zero_dotProduct, sub_zero]
    rw [hI1, hY, smul_mulVec, dotProduct_smul, smul_eq_mul, mul_eq_zero] at h0
    have h1 := congrArg Complex.re (h0.resolve_left h2I)
    rw [hYr, re_star_dotProduct_ofReal_mulVec, Complex.zero_re] at h1
    have hna := hpos.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).re)
    have hnb := hpos.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).im)
    simp only [star_trivial] at hna hnb
    have ha : (fun i => (v i).re) = 0 := by
      by_contra h
      have := hpos.dotProduct_mulVec_pos h
      simp only [star_trivial] at this
      linarith
    have hb : (fun i => (v i).im) = 0 := by
      by_contra h
      have := hpos.dotProduct_mulVec_pos h
      simp only [star_trivial] at this
      linarith
    apply hv
    funext i
    apply Complex.ext
    · simpa using congrFun ha i
    · simpa using congrFun hb i
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hdetJ
  have hYu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hdetY
  have hJJ : J * J⁻¹ = 1 := mul_nonsing_inv J hJu
  have hJJ' : J⁻¹ * J = 1 := nonsing_inv_mul J hJu
  have hYY : Y⁻¹ * Y = 1 := nonsing_inv_mul Y hYu
  have hτ'sym : (M * J⁻¹).IsSymm := by
    have hJtu : IsUnit Jᵀ.det := by rwa [det_transpose]
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_nonsing_inv]
    calc (Jᵀ)⁻¹ * Mᵀ = (Jᵀ)⁻¹ * (Mᵀ * J) * J⁻¹ := by simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = M * J⁻¹ := by rw [hI2, ← Matrix.mul_assoc (Jᵀ)⁻¹, nonsing_inv_mul _ hJtu, Matrix.one_mul]
  set Y' := (_root_.GlobalTheory.SW.spAct σ τ).map fun z => (z.im : ℂ) with hY'def
  have hY' : (2 * I) • Y' = M * J⁻¹ - (M * J⁻¹)ᴴ := by
    rw [hY'def, hact]
    exact (sub_conjTranspose_of_isSymm _ hτ'sym).symm
  have hkey : Jᴴ * Y' * J = Y := by
    apply smul_right_injective _ h2I
    calc (2 * I) • (Jᴴ * Y' * J) = Jᴴ * ((2 * I) • Y') * J := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = Jᴴ * (M * J⁻¹ - (M * J⁻¹)ᴴ) * J := by rw [hY']
      _ = Jᴴ * M - Mᴴ * J := by
        rw [conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul]
        congr 1
        · simp only [Matrix.mul_assoc, hJJ', Matrix.mul_one]
        · rw [← Matrix.mul_assoc Jᴴ, ← conjTranspose_mul, hJJ', conjTranspose_one, Matrix.one_mul]
      _ = (2 * I) • Y := by rw [hI1, hY]
  have hY'inv : Y'⁻¹ = J * Y⁻¹ * Jᴴ := by
    apply Matrix.inv_eq_left_inv
    calc J * Y⁻¹ * Jᴴ * Y' = J * Y⁻¹ * (Jᴴ * Y' * J) * J⁻¹ := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = 1 := by rw [hkey, Matrix.mul_assoc J, hYY, Matrix.mul_one, hJJ]
  have hJh : Jᴴ = Jᵀ - (2 * I) • (Y * Cᵀ) := by
    have hτh : τᴴ = τ - (2 * I) • Y := by rw [← hY]; abel
    rw [hJ, conjTranspose_add, conjTranspose_mul, transpose_add, transpose_mul, hCh, hDh, hτt, hτh,
      Matrix.sub_mul, Matrix.smul_mul]
    abel
  have hJt : Jᵀ * (J⁻¹)ᵀ = 1 := by rw [← transpose_mul, hJJ', transpose_one]
  have hmat : J⁻¹ * (J * Y⁻¹ * Jᴴ) * (J⁻¹)ᵀ = Y⁻¹ - (2 * I) • (J⁻¹ * C)ᵀ := by
    rw [hJh, transpose_mul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hJJ',
      Matrix.one_mul]
    rw [Matrix.mul_assoc Y⁻¹ Jᵀ, hJt, Matrix.mul_one, hYY, Matrix.one_mul]
  rw [hY'inv, ← dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, mulVec_mulVec, hmat, sub_mulVec,
    dotProduct_sub, smul_mulVec, dotProduct_smul, dotProduct_transpose_mulVec_self, smul_eq_mul]
  ring

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ComplexPhaseCalculusRootOfUnityStatement
section
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_phase_calculus_rootOfUnity : (∀ a b : ℂ, Ph a → Ph b → Ph (a * b)) ∧ (∀ a : ℂ, Ph a → Ph (conj a) ∧ Ph a⁻¹) ∧ (∀ t : ℝ, Ph (t : ℂ)) ∧ (∀ a : ℂ, IsMu a → Ph a ∧ ‖a‖ = 1) ∧ (∀ a : ℂ, Ph a → ‖a‖ = 1 → IsMu a) ∧ (∀ a b : ℂ, IsMu a → IsMu b → IsMu (a * b) ∧ IsMu a⁻¹ ∧ IsMu (conj a)) ∧ (∀ (a : ℂ) (k : ℕ), 0 < k → (IsMu (a ^ k) → IsMu a) ∧ (Ph (a ^ k) → Ph a)) ∧ (∀ q : ℚ, IsMu (cexp (π * I * (q : ℂ)))) ∧ ∀ a b : ℂ, b ≠ 0 → Ph b → Ph (a * b) → Ph a := by
  first | exact @GlobalTheory.Phase.Calc.calculus | exact GlobalTheory.Phase.Calc.calculus | (intros; apply GlobalTheory.Phase.Calc.calculus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledRowTestFunctionPropertiesStatement
section
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledRowTestFunction_properties : ∀ (n g : ℕ) (φ : Matrix (Fin n) (Fin g) ℚ → ℂ), (PV φ → PV (dup φ)) ∧ (φ ≠ 0 → dup φ ≠ 0) ∧ (IsSB φ → IsSB (dup φ)) ∧ (∀ u : ℂ, dup (u • φ) = u ^ 2 • dup φ) ∧ ∀ τ ∈ Siegel (Fin g), blk n τ ∈ Siegel (Fin n × Fin g) ∧ (IsSB φ → ∀ ζ : Fin 2 → Fin n × Fin g → ℂ, thS (dup φ) (blk n τ) ζ = thS φ τ (fun k i => ζ 0 (k, i)) * thS φ τ (fun k i => ζ 1 (k, i))) ∧ ((blk n τ).map fun z => (z.im : ℂ))⁻¹ = blk n ((τ.map fun z => (z.im : ℂ))⁻¹) := by
  first | exact @GlobalTheory.Phase.Doubling.doubling | exact GlobalTheory.Phase.Doubling.doubling | (intros; apply GlobalTheory.Phase.Doubling.doubling <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfSiegelThetaSeriesRationalEqStatement
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_siegelThetaSeriesRational_eq : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (φ ψ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB ψ → ∀ τ ∈ Siegel ι, (∀ ζ, thS φ τ ζ = thS ψ τ ζ) → φ = ψ := by
  first | exact @GlobalTheory.SW.eq_of_thS_eq | exact GlobalTheory.SW.eq_of_thS_eq | (intros; apply GlobalTheory.SW.eq_of_thS_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsCosetQuadraticPhaseTestFunctionConjCharacterMu
section
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.ShapeOps

theorem mu_mul {a b : ℂ} (ha : IsMu a) (hb : IsMu b) : IsMu (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [mul_pow, pow_mul, ha, mul_comm m n, pow_mul, hb]; simp

theorem mu_inv {a : ℂ} (ha : IsMu a) : IsMu a⁻¹ := by
  obtain ⟨m, hm, ha⟩ := ha
  exact ⟨m, hm, by rw [inv_pow, ha, inv_one]⟩

theorem mu_conj {a : ℂ} (ha : IsMu a) : IsMu (conj a) := by
  obtain ⟨m, hm, ha⟩ := ha
  exact ⟨m, hm, by rw [← map_pow, ha, map_one]⟩

theorem mu_ne {a : ℂ} (ha : IsMu a) : a ≠ 0 := by
  obtain ⟨m, hm, ha⟩ := ha
  rintro rfl
  rw [zero_pow hm.ne'] at ha
  exact zero_ne_one ha

theorem ph_mul {a b : ℂ} (ha : Ph a) (hb : Ph b) : Ph (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [norm_mul, Complex.ofReal_mul, mul_pow, mul_pow, pow_mul a, ha, ← pow_mul, mul_comm m n, pow_mul b, hb,
    ← pow_mul]

theorem ph_conj {a : ℂ} (ha : Ph a) : Ph (conj a) := by
  obtain ⟨m, hm, ha⟩ := ha
  refine ⟨m, hm, ?_⟩
  rw [← map_pow, ha, map_pow, Complex.conj_ofReal, Complex.norm_conj]

section Quad

variable {M : Type} [AddCommGroup M]

theorem quad_mul {S : AddSubgroup M} {f g : M → ℂ} (hf : Quad S f) (hg : Quad S g) :
    Quad S (fun x => f x * g x) := by
  refine ⟨fun x hx => mu_mul (hf.1 x hx) (hg.1 x hx), fun x hx y hy z hz => ?_⟩
  have h1 := hf.2 x hx y hy z hz
  have h2 := hg.2 x hx y hy z hz
  calc _ = (f (x + y + z) * f x * f y * f z) * (g (x + y + z) * g x * g y * g z) := by ring
    _ = _ := by rw [h1, h2]; ring

theorem quad_conj {S : AddSubgroup M} {f : M → ℂ} (hf : Quad S f) : Quad S (fun x => conj (f x)) := by
  refine ⟨fun x hx => mu_conj (hf.1 x hx), fun x hx y hy z hz => ?_⟩
  have h1 := congrArg conj (hf.2 x hx y hy z hz)
  simpa only [map_mul] using h1

theorem quad_mono {S S' : AddSubgroup M} {f : M → ℂ} (h : S' ≤ S) (hf : Quad S f) : Quad S' f :=
  ⟨fun x hx => hf.1 x (h hx), fun x hx y hy z hz => hf.2 x (h hx) y (h hy) z (h hz)⟩

theorem quad_affine {S : AddSubgroup M} {h : M → ℂ} (h1 : ∀ x ∈ S, IsMu (h x))
    (h2 : ∀ x ∈ S, ∀ y ∈ S, h (x + y) * h 0 = h x * h y) : Quad S h := by
  refine ⟨h1, fun x hx y hy z hz => ?_⟩
  have h0 : h 0 ≠ 0 := mu_ne (h1 0 S.zero_mem)
  have e1 : h (x + y) = h x * h y / h 0 := by rw [eq_div_iff h0]; exact h2 x hx y hy
  have e2 : h (y + z) = h y * h z / h 0 := by rw [eq_div_iff h0]; exact h2 y hy z hz
  have e3 : h (x + z) = h x * h z / h 0 := by rw [eq_div_iff h0]; exact h2 x hx z hz
  have e4 : h (x + y + z) = h (x + y) * h z / h 0 := by
    rw [eq_div_iff h0]; exact h2 _ (S.add_mem hx hy) z hz
  rw [e4, e1, e2, e3]
  field_simp

theorem quad_shift {S : AddSubgroup M} {f : M → ℂ} (hf : Quad S f) {d : M} (hd : d ∈ S) :
    Quad S (fun x => f (x + d)) := by
  have hq : Quad S (fun x => f (x + d) * (f x)⁻¹) := by
    refine quad_affine (fun x hx => mu_mul (hf.1 _ (S.add_mem hx hd)) (mu_inv (hf.1 x hx)))
      fun x hx y hy => ?_
    have h := hf.2 x hx y hy d hd
    have n0 := mu_ne (hf.1 0 S.zero_mem)
    have nx := mu_ne (hf.1 x hx)
    have ny := mu_ne (hf.1 y hy)
    have nxy := mu_ne (hf.1 _ (S.add_mem hx hy))
    simp only [zero_add]
    field_simp
    linear_combination h
  have hm := quad_mul hf hq
  have key : ∀ x ∈ S, f (x + d) = f x * (f (x + d) * (f x)⁻¹) := fun x hx => by
    have nx := mu_ne (hf.1 x hx)
    field_simp
  refine ⟨fun x hx => hf.1 _ (S.add_mem hx hd), fun x hx y hy z hz => ?_⟩
  have := hm.2 x hx y hy z hz
  simp only at this ⊢
  rw [← key _ hx, ← key _ hy, ← key _ hz, ← key _ S.zero_mem, ← key _ (S.add_mem hx hy),
    ← key _ (S.add_mem hy hz), ← key _ (S.add_mem hx hz),
    ← key _ (S.add_mem (S.add_mem hx hy) hz)] at this
  exact this

end Quad

variable {κ ι : Type} [Fintype κ] [Fintype ι]

theorem chr_add (y x x' : Matrix κ ι ℚ) : chr y (x + x') = chr y x * chr y x' := by
  unfold chr
  rw [← Complex.exp_add, ← mul_add, ← Rat.cast_add, ← Finset.sum_add_distrib]
  congr 3
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← add_dotProduct]; rfl

theorem mu_exp (q : ℚ) : IsMu (cexp (2 * Real.pi * I * (q : ℂ))) := by
  refine ⟨q.den, q.den_pos, ?_⟩
  rw [← Complex.exp_nat_mul]
  have h : ((q.den : ℚ) * q) = q.num := Rat.den_mul_eq_num q
  have h' : ((q.den : ℂ) * q) = q.num := by exact_mod_cast congrArg (fun t : ℚ => (t : ℂ)) h
  rw [show (q.den : ℂ) * (2 * Real.pi * I * (q : ℂ)) = ((q.den : ℂ) * q) * (2 * Real.pi * I) by ring, h']
  exact Complex.exp_int_mul_two_pi_mul_I _

theorem intM_nsmul (N : ℕ) {z : Matrix κ ι ℚ} (hz : IntM z) : IntM ((N : ℚ) • z) := fun k i => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact (isIntegral_algebraMap (R := ℤ) (x := (N : ℤ)) |>.mul (hz k i) : IsIntegral ℤ (_ * _))

theorem exists_den (y : Matrix κ ι ℚ) : ∃ N : ℕ, 0 < N ∧ IntM ((N : ℚ) • y) := by
  classical
  refine ⟨∏ p : κ × ι, (y p.1 p.2).den, Finset.prod_pos fun p _ => Rat.den_pos _, fun k i => ?_⟩
  obtain ⟨c, hc⟩ : (y k i).den ∣ ∏ p : κ × ι, (y p.1 p.2).den :=
    Finset.dvd_prod_of_mem (fun p : κ × ι => (y p.1 p.2).den) (Finset.mem_univ (k, i))
  rw [hc, Matrix.smul_apply, smul_eq_mul]
  have : (((y k i).den * c : ℕ) : ℚ) * y k i = algebraMap ℤ ℚ (c * (y k i).num) := by
    have h := Rat.den_mul_eq_num (y k i)
    simp only [eq_intCast]
    push_cast
    rw [← h]; ring
  rw [this]
  exact isIntegral_algebraMap

theorem chr_eq_one {y z : Matrix κ ι ℚ} {N : ℕ} (hy : IntM ((N : ℚ) • y)) (hz : IntM z) :
    chr y ((N : ℚ) • z) = 1 := by
  have h : IsIntegral ℤ (∑ k, ((N : ℚ) • z) k ⬝ᵥ y k) := by
    refine IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun i _ => ?_
    have := (hz k i).mul (hy k i)
    rw [Matrix.smul_apply, smul_eq_mul] at this
    rw [Matrix.smul_apply, smul_eq_mul]
    convert this using 1; ring
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  unfold chr
  rw [← hn, mul_comm]
  simp only [eq_intCast, Rat.cast_intCast]
  exact Complex.exp_int_mul_two_pi_mul_I _

theorem isSB_mul_chr {φ : Matrix κ ι ℚ → ℂ} (h : IsSB φ) (y : Matrix κ ι ℚ) :
    IsSB (fun x => φ x * chr y x) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  obtain ⟨N, hN, hy⟩ := exists_den y
  refine ⟨N * R, Nat.mul_pos hN hR, fun x hx => ?_, fun x z hz => ?_⟩
  · have := intM_nsmul N (h1 x (left_ne_zero_of_mul hx))
    rwa [smul_smul, ← Nat.cast_mul] at this
  · have e1 : ((N * R : ℕ) : ℚ) • z = (R : ℚ) • ((N : ℚ) • z) := by
      rw [smul_smul, Nat.cast_mul, mul_comm]
    have e2 : ((N * R : ℕ) : ℚ) • z = (N : ℚ) • ((R : ℚ) • z) := by
      rw [smul_smul, Nat.cast_mul]
    have a1 : φ (x + ((N * R : ℕ) : ℚ) • z) = φ x := by rw [e1]; exact h2 x _ (intM_nsmul N hz)
    have a2 : chr y (x + ((N * R : ℕ) : ℚ) • z) = chr y x := by
      rw [chr_add, e2, chr_eq_one hy (intM_nsmul R hz), mul_one]
    simp only [a1, a2]

theorem shape_conj {φ : Matrix κ ι ℚ → ℂ} (h : Shape φ) : Shape (fun x => conj (φ x)) := by
  obtain ⟨hs, c, a, S, f, hc, hf, hφ⟩ := h
  refine ⟨(isSB_algebra_haar_linear ℚ κ ι φ φ hs hs).2.2.2.1, conj c, a, S, _, ph_conj hc, quad_conj hf,
    fun x => ?_⟩
  simp only [hφ x]
  split_ifs <;> simp

theorem shape_chr {φ : Matrix κ ι ℚ → ℂ} (h : Shape φ) (y : Matrix κ ι ℚ) :
    Shape (fun x => φ x * chr y x) := by
  obtain ⟨hs, c, a, S, f, hc, hf, hφ⟩ := h
  have hq : Quad S (fun x => chr y (x + a)) := by
    refine quad_affine (fun x _ => mu_exp _) fun x _ x' _ => ?_
    simp only [← chr_add]
    congr 1; abel
  refine ⟨isSB_mul_chr hs y, c, a, S, _, hc, quad_mul hf hq, fun x => ?_⟩
  simp only [hφ x, sub_add_cancel]
  split_ifs <;> simp [mul_assoc]

theorem shape_mul {φ ψ : Matrix κ ι ℚ → ℂ} (h : Shape φ) (h' : Shape ψ) :
    Shape (fun x => φ x * ψ x) := by
  obtain ⟨hs, c, a, S, f, hc, hf, hφ⟩ := h
  obtain ⟨hs', c', a', S', f', hc', hf', hψ⟩ := h'
  refine ⟨(isSB_algebra_haar_linear ℚ κ ι φ ψ hs hs').2.2.1, ?_⟩
  by_cases hb : ∃ b, b - a ∈ S ∧ b - a' ∈ S'
  · obtain ⟨b, hb, hb'⟩ := hb
    refine ⟨c * c', b, S ⊓ S', _, ph_mul hc hc',
      quad_mul (quad_mono inf_le_left (quad_shift hf hb)) (quad_mono inf_le_right (quad_shift hf' hb')),
      fun x => ?_⟩
    have i1 : x - a ∈ S ↔ x - b ∈ S := by
      rw [show x - a = x - b + (b - a) by abel]; exact S.add_mem_cancel_right hb
    have i2 : x - a' ∈ S' ↔ x - b ∈ S' := by
      rw [show x - a' = x - b + (b - a') by abel]; exact S'.add_mem_cancel_right hb'
    simp only [hφ x, hψ x, sub_add_sub_cancel]
    by_cases p : x - b ∈ S
    · by_cases p' : x - b ∈ S'
      · rw [if_pos (i1.2 p), if_pos (i2.2 p'), if_pos (AddSubgroup.mem_inf.2 ⟨p, p'⟩)]; ring
      · rw [if_neg (mt i2.1 p'), mul_zero, if_neg (fun q => p' (AddSubgroup.mem_inf.1 q).2)]
    · rw [if_neg (mt i1.1 p), zero_mul, if_neg (fun q => p (AddSubgroup.mem_inf.1 q).1)]
  · refine ⟨0, 0, ⊥, fun _ => 1, ph_zero, ⟨fun _ _ => isMu_one, fun _ _ _ _ _ _ => rfl⟩, fun x => ?_⟩
    have : φ x * ψ x = 0 := by
      rw [hφ x, hψ x]
      by_cases p : x - a ∈ S
      · have p' : x - a' ∉ S' := fun p' => hb ⟨x, p, p'⟩
        simp [p']
      · simp [p]
    simp [this]

end GlobalTheory.Phase.ShapeOps

theorem GlobalTheory.Phase.shape_conj_chr_mul : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Shape (fun x => conj (φ x)) ∧ (∀ y, Shape (fun x => φ x * chr y x)) ∧ ∀ ψ, Shape ψ → Shape (fun x => φ x * ψ x) :=
  fun _ _ _ _ _ _ h => ⟨ShapeOps.shape_conj h, ShapeOps.shape_chr h, fun _ h' => ShapeOps.shape_mul h h'⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsZeroOrPosMulRootOfUnityFiniteGaussSumStatement
section
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isZeroOrPosMulRootOfUnity_finite_gaussSum : ∀ (M : Type) [AddCommGroup M] [Fintype M] (f : M → ℂ), Quad ⊤ f → Ph (∑ x, f x) := by
  first | exact @GlobalTheory.Phase.GaussSum.ph_sum | exact GlobalTheory.Phase.GaussSum.ph_sum | (intros; apply GlobalTheory.Phase.GaussSum.ph_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinearStatement
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (φ ψ : Matrix κ ι K → ℂ), IsSB φ → IsSB ψ → IsSB (φ + ψ) ∧ (∀ c : ℂ, IsSB (c • φ)) ∧ IsSB (φ * ψ) ∧ IsSB (fun x : Matrix κ ι K => conj (φ x)) ∧ haar (φ + ψ) = haar φ + haar ψ ∧ (∀ c : ℂ, haar (c • φ) = c * haar φ) ∧ haar (fun x : Matrix κ ι K => conj (φ x)) = conj (haar φ) ∧ ∀ b : Matrix κ ι K, IsSB (fun x : Matrix κ ι K => φ (x - b)) ∧ haar (fun x : Matrix κ ι K => φ (x - b)) = haar φ := by
  first | exact @GlobalTheory.SW.isSB_algebra_haar_linear | exact GlobalTheory.SW.isSB_algebra_haar_linear | (intros; apply GlobalTheory.SW.isSB_algebra_haar_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInnerProductSelfNonnegBoundsStatement
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatInnerProduct_self_nonneg_bounds : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (R : ℕ) (φ : Matrix κ ι K → ℂ), 0 < R → HasLevel R φ → (ip φ φ).im = 0 ∧ 0 ≤ (ip φ φ).re ∧ (∀ x, ‖φ x‖ ^ 2 ≤ (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) * (ip φ φ).re) ∧ (∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → (ip φ φ).re ≤ (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) * B ^ 2) ∧ (∃ B : ℝ, ∀ x, ‖φ x‖ ≤ B) ∧ ∀ ψ, IsSB ψ → ‖ip φ ψ‖ ^ 2 ≤ (ip φ φ).re * (ip ψ ψ).re := by
  first | exact @GlobalTheory.SW.ip_self_nonneg_and_bounds | exact GlobalTheory.SW.ip_self_nonneg_and_bounds | (intros; apply GlobalTheory.SW.ip_self_nonneg_and_bounds <;> assumption)
end

