import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0768
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionCommQuasiReflection
section
open Matrix Formalism.IndefR.Datum
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory.CartanRefl

theorem exists_sign {k : ℕ} {G : Matrix (Fin k) (Fin k) ℂ} (hG : G.IsHermitian) (hd : G.det ≠ 0) :
    ∃ s, IsCartanInv G s ∧ ∀ u, u * G = G * u → u * s = s * u := by
  classical
  let U : Matrix (Fin k) (Fin k) ℂ := hG.eigenvectorUnitary.1
  have h1 : U * star U = 1 := hG.eigenvectorUnitary.2.2
  have h2 : star U * U = 1 := hG.eigenvectorUnitary.2.1
  have hs : G = U * diagonal (fun i => (hG.eigenvalues i : ℂ)) * star U := by
    have := hG.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hne : ∀ i, hG.eigenvalues i ≠ 0 := fun i hi => by
    rw [hG.det_eq_prod_eigenvalues] at hd
    exact hd (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]))
  have mul : ∀ a b : Fin k → ℂ, (U * diagonal a * star U) * (U * diagonal b * star U) =
      U * diagonal (fun i => a i * b i) * star U := fun a b => by
    calc _ = U * (diagonal a * (star U * U) * diagonal b) * star U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one, diagonal_mul_diagonal]
  let e : Fin k → ℝ := fun i => if 0 < hG.eigenvalues i then 1 else -1
  have he : ∀ i, (e i : ℂ) * e i = 1 := fun i => by
    simp only [e]; split_ifs <;> simp
  have hh : (U * diagonal (fun i => (e i : ℂ)) * star U)ᴴ = U * diagonal (fun i => (e i : ℂ)) * star U := by
    simp [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc,
      Pi.star_def]
  refine ⟨U * diagonal (fun i => (e i : ℂ)) * star U, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [mul]
    simp only [he, diagonal_one, Matrix.mul_one, h1]
  · rw [hh]
    conv_lhs => rw [hs]
    conv_rhs => rw [hs]
    rw [mul, mul]
    congr 3
    funext i
    rw [mul_right_comm, he, one_mul]
  · conv => arg 1; arg 1; rw [hs]
    rw [mul]
    have hp : (diagonal fun i => (hG.eigenvalues i : ℂ) * e i).PosDef := by
      rw [Matrix.posDef_diagonal_iff]
      intro i
      rw [← Complex.ofReal_mul, Complex.zero_lt_real]
      simp only [e]
      split_ifs with h
      · simpa using h
      · have := lt_of_le_of_ne (not_lt.1 h) (hne i)
        linarith
    have hu : IsUnit (star U) := ⟨⟨star U, U, h2, h1⟩, rfl⟩
    have := hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose] at this
  · intro u hu
    obtain ⟨v, rfl⟩ : ∃ v, u = U * v * star U := ⟨star U * u * U, by
      calc u = (U * star U) * u * (U * star U) := by rw [h1, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]⟩
    have cm : ∀ a b : Matrix (Fin k) (Fin k) ℂ, (U * a * star U) * (U * b * star U) = U * (a * b) * star U := fun a b => by
      calc _ = U * (a * (star U * U) * b) * star U := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h2, Matrix.mul_one]
    have inj : ∀ a b : Matrix (Fin k) (Fin k) ℂ, U * a * star U = U * b * star U → a = b := fun a b h => by
      have key : ∀ a : Matrix (Fin k) (Fin k) ℂ, star U * (U * a * star U) * U = a := fun a => by
        calc _ = (star U * U) * a * (star U * U) := by simp only [Matrix.mul_assoc]
          _ = a := by rw [h2, Matrix.one_mul, Matrix.mul_one]
      rw [← key a, h, key]
    have hv : v * diagonal (fun i => (hG.eigenvalues i : ℂ)) = diagonal (fun i => (hG.eigenvalues i : ℂ)) * v := by
      apply inj
      rw [← cm, ← cm, ← hs, hu]
    rw [cm, cm]
    congr 2
    ext i j
    have hij := congrFun (congrFun hv i) j
    rw [mul_diagonal, diagonal_mul] at hij ⊢
    by_cases h0 : v i j = 0
    · simp [h0]
    · have : hG.eigenvalues j = hG.eigenvalues i := by
        rw [mul_comm] at hij
        exact_mod_cast mul_right_cancel₀ h0 hij
      simp only [e, this, mul_comm]

theorem exists_comm {k : ℕ} {G r : Matrix (Fin k) (Fin k) ℂ} (hG : Gᴴ = G) (hd : G.det ≠ 0)
    (hr : r * r = 1) (hrG : rᴴ * G * r = G) : ∃ s, IsCartanInv G s ∧ s * r = r * s := by
  classical
  have hH : (1 + rᴴ * r).PosDef := PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self r)
  obtain ⟨C, hC, hCH⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hH.isStrictlyPositive
  obtain ⟨⟨C, B, hCB, hBC⟩, rfl⟩ := hC
  simp only [star_eq_conjTranspose] at hCH
  have hCB' : Bᴴ * Cᴴ = 1 := by rw [← conjTranspose_mul, hCB, conjTranspose_one]
  have hBC' : Cᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBC, conjTranspose_one]
  have hr' : rᴴ * rᴴ = 1 := by rw [← conjTranspose_mul, hr, conjTranspose_one]
  have e1 : ∀ X : Matrix (Fin k) (Fin k) ℂ, C * (B * X) = X := fun X => by rw [← Matrix.mul_assoc, hCB, Matrix.one_mul]
  have e2 : ∀ X : Matrix (Fin k) (Fin k) ℂ, B * (C * X) = X := fun X => by rw [← Matrix.mul_assoc, hBC, Matrix.one_mul]
  have e3 : ∀ X : Matrix (Fin k) (Fin k) ℂ, Bᴴ * (Cᴴ * X) = X := fun X => by rw [← Matrix.mul_assoc, hCB', Matrix.one_mul]
  have e4 : ∀ X : Matrix (Fin k) (Fin k) ℂ, Cᴴ * (Bᴴ * X) = X := fun X => by rw [← Matrix.mul_assoc, hBC', Matrix.one_mul]
  have e5 : ∀ X : Matrix (Fin k) (Fin k) ℂ, r * (r * X) = X := fun X => by rw [← Matrix.mul_assoc, hr, Matrix.one_mul]
  have e6 : ∀ X : Matrix (Fin k) (Fin k) ℂ, rᴴ * (G * (r * X)) = G * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hrG]
  have hinv : rᴴ * (Cᴴ * C) * r = Cᴴ * C := by
    rw [← hCH, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, hr', Matrix.one_mul, hr, add_comm]
  have huu : (C * r * B) * (C * r * B) = 1 := by
    simp only [Matrix.mul_assoc, e2, e5, hCB]
  have hsu : (C * r * B)ᴴ * (C * r * B) = 1 := by
    calc _ = Bᴴ * (rᴴ * (Cᴴ * C) * r) * B := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hinv]; simp only [Matrix.mul_assoc, e3, hCB]
  have hu : (C * r * B)ᴴ = C * r * B := by
    calc _ = (C * r * B)ᴴ * ((C * r * B) * (C * r * B)) := by rw [huu, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hsu, Matrix.one_mul]
  have hG' : (Bᴴ * G * B).IsHermitian := isHermitian_conjTranspose_mul_mul B hG
  have hd' : (Bᴴ * G * B).det ≠ 0 := by
    intro h
    apply hd
    have : G = Cᴴ * (Bᴴ * G * B) * C := by simp only [Matrix.mul_assoc, e4, hBC, Matrix.mul_one]
    rw [this, det_mul, det_mul, h, mul_zero, zero_mul]
  have hc : (C * r * B) * (Bᴴ * G * B) = (Bᴴ * G * B) * (C * r * B) := by
    have : (C * r * B)ᴴ * (Bᴴ * G * B) * (C * r * B) = Bᴴ * G * B := by
      simp only [conjTranspose_mul, Matrix.mul_assoc, e4, e2, e6]
    rw [hu] at this
    conv_lhs => rw [← this]
    rw [← Matrix.mul_assoc (C * r * B), ← Matrix.mul_assoc (C * r * B), huu, Matrix.one_mul]
  obtain ⟨s, ⟨hs1, hs2, hs3⟩, hs4⟩ := exists_sign hG' hd'
  have hs5 := hs4 _ hc
  refine ⟨B * s * C, ⟨?_, ?_, ?_⟩, ?_⟩
  · calc _ = B * (s * s) * C := by simp only [Matrix.mul_assoc, e1]
      _ = 1 := by rw [hs1, Matrix.mul_one, hBC]
  · calc _ = Cᴴ * (sᴴ * (Bᴴ * G * B) * s) * C := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hs2]; simp only [Matrix.mul_assoc, e4, hBC, Matrix.mul_one]
  · have hu : IsUnit C := ⟨⟨C, B, hCB, hBC⟩, rfl⟩
    have := hs3.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
    simpa only [Matrix.mul_assoc, e4] using this
  · calc _ = B * (s * (C * r * B)) * C := by simp only [Matrix.mul_assoc, hBC, Matrix.mul_one]
      _ = _ := by rw [← hs5]; simp only [Matrix.mul_assoc, e2]

theorem exists_cartan_comm_quasiReflection : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), Gᴴ = G → G.det ≠ 0 → ∀ x : Fin n → ℂ, star x ⬝ᵥ G *ᵥ x ≠ 0 → ∃ s, IsCartanInv G s ∧ ∀ c : ℂ, s * (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) = (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) * s := by
  intro n G hG hd x hx
  set q := star x ⬝ᵥ G *ᵥ x with hq
  have hM : Matrix.vecMulVec x (star x ᵥ* G) = Matrix.vecMulVec x (star x) * G := by
    rw [vecMulVec_mul]
  have hN : (Matrix.vecMulVec x (star x))ᴴ = Matrix.vecMulVec x (star x) := by
    rw [conjTranspose_vecMulVec, star_star]
  have hMM : Matrix.vecMulVec x (star x ᵥ* G) * Matrix.vecMulVec x (star x ᵥ* G) = q • Matrix.vecMulVec x (star x ᵥ* G) := by
    rw [vecMulVec_mul_vecMulVec, hq, dotProduct_mulVec, vecMulVec_smul]
  have hMG : (Matrix.vecMulVec x (star x ᵥ* G))ᴴ * G = G * Matrix.vecMulVec x (star x ᵥ* G) := by
    rw [hM, conjTranspose_mul, hN, hG, Matrix.mul_assoc]
  have hqs : star q = q := by
    rw [hq, ← star_dotProduct_star, star_star, star_mulVec, hG, dotProduct_mulVec]
  generalize Matrix.vecMulVec x (star x ᵥ* G) = M at hMM hMG ⊢
  have hr : (1 + (-2 / q) • M) * (1 + (-2 / q) • M) = 1 := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hMM,
      smul_smul, add_assoc, ← add_smul, smul_add]
    have : -2 / q + (-2 / q + -2 / q * (-2 / q * q)) = 0 := by field_simp; ring
    rw [this, zero_smul, add_zero]
  have hrG : (1 + (-2 / q) • M)ᴴ * G = G * (1 + (-2 / q) • M) := by
    have : star (-2 / q) = -2 / q := by rw [star_div₀, hqs]; simp
    rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, this, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hMG]
  obtain ⟨s, hs, hc⟩ := exists_comm hG hd hr (by rw [hrG, Matrix.mul_assoc, hr, Matrix.mul_one])
  refine ⟨s, hs, fun c => ?_⟩
  have hsM : s * M = M * s := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      add_right_inj] at hc
    exact smul_right_injective _ (div_ne_zero (by norm_num) hx) hc
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hsM]

end GlobalTheory.CartanRefl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSetUnitaryHermitianReal
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.AnisoCpt

open Metric Matrix

section Gen

variable {K : Type} [NontriviallyNormedField K] [ProperSpace K] {n m : ℕ}

theorem exists_mul_sq_le (Q : (Fin n → K) → (Fin m → K)) (hc : Continuous Q)
    (hs : ∀ (c : K) y, Q (c • y) = (c * c) • Q y) (h0 : ∀ y, Q y = 0 → y = 0) :
    ∃ a > 0, ∀ y, a * ‖y‖ ^ 2 ≤ ‖Q y‖ := by
  have hns : ∀ (c : K) y, ‖Q (c • y)‖ = ‖c‖ * ‖c‖ * ‖Q y‖ := fun c y => by
    rw [hs, norm_smul, norm_mul]
  obtain ⟨c, hc1⟩ := NormedField.exists_one_lt_norm K
  have hc0 : 0 < ‖c‖ := lt_trans one_pos hc1
  let S : Set (Fin n → K) := {y | 1 / ‖c‖ ≤ ‖y‖ ∧ ‖y‖ ≤ 1}
  have hSc : IsCompact S := (isCompact_closedBall (0 : Fin n → K) 1).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
    (fun y hy => mem_closedBall_zero_iff.2 hy.2)
  have hcont : Continuous fun y => ‖Q y‖ := hc.norm
  by_cases hS : S.Nonempty
  · obtain ⟨y₀, hy₀S, hmin⟩ := hSc.exists_isMinOn hS hcont.continuousOn
    have hy₀ : y₀ ≠ 0 := by
      intro h
      have := hy₀S.1
      rw [h, norm_zero] at this
      exact absurd this (not_le.2 (by positivity))
    refine ⟨‖Q y₀‖, norm_pos_iff.2 (fun h => hy₀ (h0 _ h)), fun y => ?_⟩
    by_cases hy : y = 0
    · rw [hy, norm_zero]
      simp
    obtain ⟨d, hd0, hdlt, hdge, -⟩ := rescale_to_shell hc1 one_pos hy
    have hdS : d • y ∈ S := ⟨hdge, hdlt.le⟩
    have h1 : ‖Q y₀‖ ≤ ‖d‖ * ‖d‖ * ‖Q y‖ := by
      rw [← hns]
      exact hmin hdS
    have h2 : ‖d‖ * ‖y‖ < 1 := by
      rw [← norm_smul]
      exact hdlt
    have hn := norm_nonneg y
    have hd := norm_nonneg d
    have hf := norm_nonneg (Q y)
    have h3 : (‖d‖ * ‖y‖) ^ 2 ≤ 1 := by nlinarith [mul_nonneg hd hn]
    calc ‖Q y₀‖ * ‖y‖ ^ 2 ≤ ‖d‖ * ‖d‖ * ‖Q y‖ * ‖y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = ‖Q y‖ * (‖d‖ * ‖y‖) ^ 2 := by ring
      _ ≤ ‖Q y‖ * 1 := mul_le_mul_of_nonneg_left h3 hf
      _ = ‖Q y‖ := mul_one _
  · refine ⟨1, one_pos, fun y => ?_⟩
    by_cases hy : y = 0
    · rw [hy, norm_zero]
      simp
    obtain ⟨d, -, hdlt, hdge, -⟩ := rescale_to_shell hc1 one_pos hy
    exact absurd ⟨d • y, hdge, hdlt.le⟩ hS

theorem exists_le_mul_sq (Q : (Fin n → K) → (Fin m → K)) (hc : Continuous Q)
    (hs : ∀ (c : K) y, Q (c • y) = (c * c) • Q y) :
    ∃ B ≥ 0, ∀ y, ‖Q y‖ ≤ B * ‖y‖ ^ 2 := by
  have hns : ∀ (c : K) y, ‖Q (c • y)‖ = ‖c‖ * ‖c‖ * ‖Q y‖ := fun c y => by
    rw [hs, norm_smul, norm_mul]
  have hQ0 : Q 0 = 0 := by simpa using hs 0 0
  obtain ⟨c, hc1⟩ := NormedField.exists_one_lt_norm K
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : Fin n → K) 1).exists_bound_of_continuousOn
    hc.continuousOn
  have hM₀0 : 0 ≤ M₀ := le_trans (norm_nonneg _) (hM₀ 0 (mem_closedBall_self zero_le_one))
  refine ⟨M₀ * ‖c‖ ^ 2, by positivity, fun y => ?_⟩
  by_cases hy : y = 0
  · rw [hy, hQ0, norm_zero]
    positivity
  obtain ⟨d, hd0, hdlt, -, hdinv⟩ := rescale_to_shell hc1 one_pos hy
  have h1 := hM₀ (d • y) (mem_closedBall_zero_iff.2 hdlt.le)
  rw [hns] at h1
  have ht : ‖d‖⁻¹ ≤ ‖c‖ * ‖y‖ := by simpa using hdinv
  have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd0
  have hf : ‖Q y‖ = ‖d‖⁻¹ ^ 2 * (‖d‖ * ‖d‖ * ‖Q y‖) := by
    field_simp
  calc ‖Q y‖ = ‖d‖⁻¹ ^ 2 * (‖d‖ * ‖d‖ * ‖Q y‖) := hf
    _ ≤ ‖d‖⁻¹ ^ 2 * M₀ := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ ≤ (‖c‖ * ‖y‖) ^ 2 * M₀ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_nonneg.2 hdpos.le) ht 2) hM₀0
    _ = M₀ * ‖c‖ ^ 2 * ‖y‖ ^ 2 := by ring

end Gen

theorem hform_eq {A : Type} [CommRing A] {n : Type} [Fintype n] (c : A →+* A) (J : Matrix n n A)
    (x y : n → A) : Formalism.UG.hform c J x y = (fun i => c (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] (c : A →+* A)
    (J g : Matrix n n A) (x : n → A) :
    Formalism.UG.hform c J (g *ᵥ x) (g *ᵥ x) = Formalism.UG.hform c (Formalism.UG.cT c g * J * g) x x := by
  have h1 : (fun i => c ((g *ᵥ x) i)) = (g.map c) *ᵥ (fun i => c (x i)) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  rw [hform_eq, hform_eq, h1, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, Matrix.dotProduct_mulVec]
  rfl

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] (K : Type) [Field K] [Algebra F K]

theorem sigR_smul (σ : E →ₐ[F] E) (c : K) (z : K ⊗[F] E) : sigR K σ (c • z) = c • sigR K σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

def sigL (σ : E →ₐ[F] E) : K ⊗[F] E →ₗ[K] K ⊗[F] E where
  toFun := sigR K σ
  map_add' := map_add _
  map_smul' := sigR_smul K σ

theorem hR_smul (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : K)
    (x : Fin M → K ⊗[F] E) : hR K σ J (c • x) (c • x) = (c * c) • hR K σ J x x := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, sigR_smul, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum, smul_smul]

end Tens

end GlobalTheory.AnisoCpt

namespace GlobalTheory.AnisoCpt

open Metric Matrix

theorem exists_isCompact_entries_of_anisotropic :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (K : Type) [NontriviallyNormedField K] [ProperSpace K] [Algebra F K] (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ u : Fin M → K ⊗[F] E, hR K σ J u u = 0 → u = 0) →
    ∃ C : Set (K ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (K ⊗[F] E),
      Formalism.UG.cT (sigR K σ) g * JR K J * g = JR K J → ∀ i j, g i j ∈ C := by
  intro F E _ _ _ _ _ σ hcm K _ _ _ M J _ haniso
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (K ⊗[F] E) := IsModuleTopology.isTopologicalRing K _
  let bV := Module.finBasis K (Fin M → K ⊗[F] E)
  let bE := Module.finBasis K (K ⊗[F] E)
  let φ := bV.equivFun
  let ψ := bE.equivFun
  have hφs : Continuous φ.symm := IsModuleTopology.continuous_of_linearMap φ.symm.toLinearMap
  have hψ : Continuous ψ := IsModuleTopology.continuous_of_linearMap ψ.toLinearMap
  have hs : Continuous (sigR K σ) := IsModuleTopology.continuous_of_linearMap (sigL K σ)
  have hhc : Continuous fun x : Fin M → K ⊗[F] E => hR K σ J x x := by
    show Continuous fun x => Formalism.UG.hform (sigR K σ) (JR K J) x x
    unfold Formalism.UG.hform
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      ((hs.comp (continuous_apply i)).mul continuous_const).mul (continuous_apply j)
  let Q : (Fin (Module.finrank K (Fin M → K ⊗[F] E)) → K) → (Fin (Module.finrank K (K ⊗[F] E)) → K) :=
    fun y => ψ (hR K σ J (φ.symm y) (φ.symm y))
  have hQc : Continuous Q := hψ.comp (hhc.comp hφs)
  have hQs : ∀ (c : K) y, Q (c • y) = (c * c) • Q y := by
    intro c y
    simp only [Q, map_smul, hR_smul]
  have hQ0 : ∀ y, Q y = 0 → y = 0 := by
    intro y hy
    have h1 : hR K σ J (φ.symm y) (φ.symm y) = 0 := by
      exact ψ.injective (hy.trans (map_zero ψ).symm)
    have h2 := haniso _ h1
    simpa using congrArg φ h2
  obtain ⟨a, ha, hlow⟩ := exists_mul_sq_le Q hQc hQs hQ0
  obtain ⟨B, hB, hup⟩ := exists_le_mul_sq Q hQc hQs
  have hunit : ∀ g : Matrix (Fin M) (Fin M) (K ⊗[F] E),
      Formalism.UG.cT (sigR K σ) g * JR K J * g = JR K J → ∀ x, hR K σ J (g *ᵥ x) (g *ᵥ x) = hR K σ J x x := by
    intro g hg x
    show Formalism.UG.hform _ _ _ _ = Formalism.UG.hform _ _ _ _
    rw [hform_mulVec, hg]
  let e : Fin M → Fin (Module.finrank K (Fin M → K ⊗[F] E)) → K := fun j => φ (Pi.single j 1)
  let D := ∑ j, ‖e j‖ ^ 2
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun j _ => sq_nonneg _
  let r := B / a * D + 1
  refine ⟨⋃ i : Fin M, (fun y => φ.symm y i) '' closedBall 0 r,
    isCompact_iUnion fun i => (isCompact_closedBall _ _).image ((continuous_apply i).comp hφs), ?_⟩
  intro g hg i j
  refine Set.mem_iUnion.2 ⟨i, φ (g *ᵥ Pi.single j 1), ?_, ?_⟩
  · rw [mem_closedBall_zero_iff]
    set t := ‖φ (g *ᵥ Pi.single j 1)‖
    have ht : 0 ≤ t := norm_nonneg _
    have h1 := hlow (φ (g *ᵥ Pi.single j 1))
    have hQeq : Q (φ (g *ᵥ Pi.single j 1)) = Q (e j) := by
      simp only [Q, e, LinearEquiv.symm_apply_apply, hunit g hg]
    rw [hQeq] at h1
    have h2 := hup (e j)
    have hej : ‖e j‖ ^ 2 ≤ D :=
      Finset.single_le_sum (f := fun j => ‖e j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ j)
    have h3 : t ^ 2 ≤ B / a * D := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      nlinarith
    have h4 : 0 ≤ B / a * D := mul_nonneg (div_nonneg hB ha.le) hD0
    nlinarith [sq_nonneg (t - 1)]
  · simp only [LinearEquiv.symm_apply_apply]
    rw [Matrix.mulVec_single_one]
    rfl

end GlobalTheory.AnisoCpt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusMatrixQuasiLogarithmBasis
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

section Div

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type} {d : ℕ}

theorem in_mono {N N' : Ideal B} (h : N ≤ N') {f : MvPowerSeries σ Q} (hf : In N f) : In N' f :=
  fun α => by
    obtain ⟨b, hb, e⟩ := hf α
    exact ⟨b, h hb, e⟩

theorem in_span_smul (p : B) {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) :
    In (Ideal.span {p}) (algebraMap B Q p • f) := fun α => by
  obtain ⟨b, -, e⟩ := hf α
  refine ⟨b * p, Ideal.mem_span_singleton'.2 ⟨b, rfl⟩, ?_⟩
  rw [coeff_smul, e, ← map_mul, mul_comm]

theorem div_coeff (p : B) {c : Q} (hc : c * algebraMap B Q p = 1) {q : Q}
    (h : ∃ b ∈ Ideal.span {p}, q = algebraMap B Q b) : ∃ b ∈ (⊤ : Ideal B), c * q = algebraMap B Q b := by
  obtain ⟨b, hb, e⟩ := h
  obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.1 hb
  refine ⟨b', Submodule.mem_top, ?_⟩
  rw [e, map_mul, ← mul_assoc, mul_comm c, mul_assoc, hc, mul_one]

theorem ql_div (p : B) {c : Q} (hc : c * algebraMap B Q p = 1)
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {f : MvPowerSeries (Fin d) Q} (hf : QL μ (Ideal.span {p}) f) : QL μ ⊤ (c • f) := by
  obtain ⟨h0, h1, h2⟩ := hf
  have hμ' : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp [up, hμ i]
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, h0,
      mul_zero]
  · have := div_coeff p hc (h1 i)
    simpa [lin, coeff_smul] using this
  · rw [formalCoboundary_smul hμ']
    intro α
    have := div_coeff p hc (h2 α)
    simpa [coeff_smul] using this

theorem comb_mul {ι : Type} [Fintype ι] (p : B) (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (fun l => b l * p) e = algebraMap B Q p • comb b e := by
  simp only [comb, Finset.smul_sum, map_mul, mul_comm, mul_smul]

end Div

end GlobalTheory.QLog

namespace GlobalTheory.QLog

theorem exists_frob_matrix : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∃ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, ∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) ∧ ∀ i', i = Sum.inl i' → In (Ideal.span {(p : F.B)}) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hm k e hB hA
  have key := fun f hf => GlobalTheory.T.quasi_log_lift_pdiv_group_frame p C v O hv ε hε F G d c μ' hL hm f hf
  obtain ⟨u, hu⟩ := F.frame.unit_p
  set pinv : F.Q := ((u⁻¹ : F.Qˣ) : F.Q) with hpinv
  have hpB : (p : F.Q) = algebraMap F.B F.Q (p : F.B) := (map_natCast _ _).symm
  have hc : pinv * algebraMap F.B F.Q (p : F.B) = 1 := by
    rw [← hpB, ← hu, hpinv, Units.inv_mul]
  have hc' : algebraMap F.B F.Q (p : F.B) * pinv = 1 := by rw [mul_comm, hc]
  have h1 : ∀ i', ∃ b : Fin d ⊕ Fin k → F.B,
      In (⊤ : Ideal F.B) (pinv • frob p F.s (e (Sum.inl i')) - comb b e) := fun i' =>
    (hB.2 _ (ql_div (p : F.B) hc hL.const
      ((key _ (hB.1 _)).2 (hA i').1))).exists
  have h2 : ∀ j, ∃ b : Fin d ⊕ Fin k → F.B,
      In (⊤ : Ideal F.B) (frob p F.s (e (Sum.inr j)) - comb b e) := fun j =>
    (hB.2 _ (key _ (hB.1 _)).1).exists
  choose b1 hb1 using h1
  choose b2 hb2 using h2
  refine ⟨Matrix.of fun l i => Sum.elim (fun i' => b1 i' l) (fun j => b2 j l) i, ?_⟩
  intro i
  rcases i with i' | j
  · have hcol : (fun l => ((Matrix.of fun l i => Sum.elim (fun i' => b1 i' l) (fun j => b2 j l) i) *
        blk d k (p : F.B) 1) l (Sum.inl i')) = fun l => b1 i' l * p := by
      funext l
      simp [blk, Matrix.mul_diagonal]
    rw [hcol, comb_mul]
    have heq : frob p F.s (e (Sum.inl i')) - algebraMap F.B F.Q (p : F.B) • comb (b1 i') e =
        algebraMap F.B F.Q (p : F.B) • (pinv • frob p F.s (e (Sum.inl i')) - comb (b1 i') e) := by
      rw [smul_sub, smul_smul, hc', one_smul]
    rw [heq]
    have hp := in_span_smul (p : F.B) (hb1 i')
    exact ⟨in_mono le_top hp, fun _ _ => hp⟩
  · have hcol : (fun l => ((Matrix.of fun l i => Sum.elim (fun i' => b1 i' l) (fun j => b2 j l) i) *
        blk d k (p : F.B) 1) l (Sum.inr j)) = fun l => b2 j l := by
      funext l
      simp [blk, Matrix.mul_diagonal]
    rw [hcol]
    exact ⟨hb2 j, fun _ h => absurd h (by simp)⟩

end GlobalTheory.QLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelOneThetaNeZeroOnIdealHalfLatticeStatement
section
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open GlobalTheory.SW hiding Level
open scoped ComplexConjugate Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelOne_theta_ne_zero_on_ideal_half_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ (w : E) (L : Lt E r), SelfD X L → ∀ x ∈ X.dom, ∀ (𝔪 : Ideal (𝓞 E)) (M : ℕ), 2 ≤ M → 𝔪 * conjI 𝔪 = Ideal.span {(M : 𝓞 E)} → ∀ ϑ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w x L ϑ → ϑ ≠ 0 → ∃ u ∈ 𝔪 • L, ϑ (pv X idx x ((M : E)⁻¹ • u)) ≠ 0 := by
  first | exact @GlobalTheory.Dict.ThetaHalf.exists_ne_zero_on_half | exact GlobalTheory.Dict.ThetaHalf.exists_ne_zero_on_half | (intros; apply GlobalTheory.Dict.ThetaHalf.exists_ne_zero_on_half <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupSchemeOfIsOpenStableStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openSubgroupScheme_of_isOpen_stable : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (Z : Set G.left), IsOpen Z → (∀ s : S, (η[G]).left s ∈ Z) → (∀ w : (G ⊗ G).left, (fst G G).left w ∈ Z → (snd G G).left w ∈ Z → (μ[G]).left w ∈ Z) → (∀ y ∈ Z, (ι[G]).left y ∈ Z) → ∃ (G₀ : Over S) (_ : GrpObj G₀) (j : G₀ ⟶ G), IsMonHom j ∧ IsOpenImmersion j.left ∧ Set.range j.left = Z := by
  first | exact @GlobalTheory.OpenSubgroup.exists_open_subgroup | exact GlobalTheory.OpenSubgroup.exists_open_subgroup | (intros; apply GlobalTheory.OpenSubgroup.exists_open_subgroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianEtaleStalkOverPointStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strictlyHenselianEtaleStalk_over_point : ∀ (S : Scheme.{0}) (U : Over S), Etale U.hom → ∀ u : U.left, ∃ (O : Type) (_ : CommRing O) (s : Spec (CommRingCat.of O) ⟶ S) (g : Over.mk s ⟶ U), IsStalk O s ∧ ∃ v, g.left v = u := by
  first | (exact @GlobalTheory.EtC.exists_isStalk_over_point) | (exact GlobalTheory.EtC.exists_isStalk_over_point) | (intros; apply GlobalTheory.EtC.exists_isStalk_over_point  <;> assumption)
end

