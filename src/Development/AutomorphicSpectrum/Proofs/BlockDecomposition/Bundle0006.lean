import Mathlib

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnTprodCubicFactor
section
namespace GlobalTheory.CompanionTheory.EulerThree

noncomputable def cubicFactor (p : ℕ) (a b c s : ℂ) : ℂ :=
  (1 - a * (p : ℂ) ^ (-s))⁻¹ * (1 - b * (p : ℂ) ^ (-s))⁻¹ * (1 - c * (p : ℂ) ^ (-s))⁻¹

theorem norm_param_mul {p : ℕ} (hp : 2 ≤ p) {a : ℂ} (ha : ‖a‖ = 1) (s : ℂ) :
    ‖a * (p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  rw [norm_mul, ha, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

theorem rpow_neg_le_half {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 1 ≤ σ) :
    (p : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : (p : ℝ) ^ (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.rpow_neg_one, one_div]
    exact inv_anti₀ (by norm_num) hp'
  exact h1.trans h2

theorem one_sub_ne_zero_of_le {x : ℂ} (hx : ‖x‖ ≤ 1 / 2) : 1 - x ≠ 0 := by
  intro h
  have : x = 1 := (sub_eq_zero.1 h).symm
  rw [this, norm_one] at hx
  norm_num at hx

theorem norm_inv_one_sub_sub_one_le {x : ℂ} (hx : ‖x‖ ≤ 1 / 2) :
    ‖(1 - x)⁻¹ - 1‖ ≤ 2 * ‖x‖ := by
  have hne := one_sub_ne_zero_of_le hx
  have hlow : 1 / 2 ≤ ‖1 - x‖ := by
    have := norm_sub_norm_le (1 : ℂ) x
    rw [norm_one] at this
    linarith
  have e : (1 - x)⁻¹ - 1 = x * (1 - x)⁻¹ := by
    field_simp
    ring
  rw [e, norm_mul, norm_inv]
  have hinv : ‖1 - x‖⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  nlinarith [norm_nonneg x]

theorem norm_three_sub_one_le {y₁ y₂ y₃ : ℂ} {t : ℝ} (ht : t ≤ 1 / 2)
    (h₁ : ‖y₁‖ ≤ 2 * t) (h₂ : ‖y₂‖ ≤ 2 * t) (h₃ : ‖y₃‖ ≤ 2 * t) :
    ‖(1 + y₁) * (1 + y₂) * (1 + y₃) - 1‖ ≤ 14 * t := by
  have ht0 : 0 ≤ t := by nlinarith [norm_nonneg y₁]
  have e : (1 + y₁) * (1 + y₂) * (1 + y₃) - 1 =
      y₁ + y₂ + y₃ + y₁ * y₂ + y₁ * y₃ + y₂ * y₃ + y₁ * y₂ * y₃ := by ring
  have m₁₂ : ‖y₁ * y₂‖ ≤ 2 * t := by
    rw [norm_mul]
    nlinarith [norm_nonneg y₁, norm_nonneg y₂]
  have m₁₃ : ‖y₁ * y₃‖ ≤ 2 * t := by
    rw [norm_mul]
    nlinarith [norm_nonneg y₁, norm_nonneg y₃]
  have m₂₃ : ‖y₂ * y₃‖ ≤ 2 * t := by
    rw [norm_mul]
    nlinarith [norm_nonneg y₂, norm_nonneg y₃]
  have m₁₂₃ : ‖y₁ * y₂ * y₃‖ ≤ 2 * t := by
    rw [norm_mul]
    have : ‖y₃‖ ≤ 1 := by linarith
    nlinarith [norm_nonneg (y₁ * y₂), norm_nonneg y₃]
  rw [e]
  calc _ ≤ ‖y₁‖ + ‖y₂‖ + ‖y₃‖ + ‖y₁ * y₂‖ + ‖y₁ * y₃‖ + ‖y₂ * y₃‖ + ‖y₁ * y₂ * y₃‖ := by
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        exact norm_add_le _ _
    _ ≤ 14 * t := by linarith

theorem norm_cubicFactor_sub_one_le {p : ℕ} (hp : 2 ≤ p) {a b c s : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hs : 1 ≤ s.re) :
    ‖cubicFactor p a b c s - 1‖ ≤ 14 * (p : ℝ) ^ (-s.re) := by
  have ht := rpow_neg_le_half hp hs
  have key : ∀ {u : ℂ}, ‖u‖ = 1 →
      ‖(1 - u * (p : ℂ) ^ (-s))⁻¹ - 1‖ ≤ 2 * (p : ℝ) ^ (-s.re) := fun hu => by
    have hn := norm_param_mul hp hu s
    have := norm_inv_one_sub_sub_one_le (x := _) (hn.le.trans ht)
    rwa [hn] at this
  have := norm_three_sub_one_le ht (key ha) (key hb) (key hc)
  simpa [cubicFactor] using this

theorem differentiableAt_cubicFactor {p : ℕ} (hp : 2 ≤ p) {a b c s : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hs : 1 ≤ s.re) :
    DifferentiableAt ℂ (fun z => cubicFactor p a b c z) s := by
  have hp0 : (p : ℂ) ≠ 0 := by
    have : p ≠ 0 := by omega
    exact_mod_cast this
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl hp0)
  have key : ∀ {u : ℂ}, ‖u‖ = 1 →
      DifferentiableAt ℂ (fun z : ℂ => (1 - u * (p : ℂ) ^ (-z))⁻¹) s := fun hu => by
    refine ((differentiableAt_const _).sub ((differentiableAt_const _).mul hpow)).inv ?_
    exact one_sub_ne_zero_of_le ((norm_param_mul hp hu s).le.trans (rpow_neg_le_half hp hs))
  exact ((key ha).mul (key hb)).mul (key hc)

variable {ι : Type*} {p : ι → ℕ} {a b c : ι → ℂ}

theorem summable_rpow_neg (hinj : Function.Injective p) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun i => (p i : ℝ) ^ (-σ) :=
  (Real.summable_nat_rpow.2 (by linarith)).comp_injective hinj

theorem multipliable_cubicFactor (hinj : Function.Injective p) (hp : ∀ i, 2 ≤ p i)
    (ha : ∀ i, ‖a i‖ = 1) (hb : ∀ i, ‖b i‖ = 1) (hc : ∀ i, ‖c i‖ = 1) {s : ℂ} (hs : 1 < s.re) :
    Multipliable fun i => cubicFactor (p i) (a i) (b i) (c i) s := by
  have hsum : Summable fun i => cubicFactor (p i) (a i) (b i) (c i) s - 1 :=
    Summable.of_norm_bounded ((summable_rpow_neg hinj hs).mul_left 14)
      fun i => norm_cubicFactor_sub_one_le (hp i) (ha i) (hb i) (hc i) hs.le
  simpa using multipliable_one_add_of_summable hsum.norm

theorem differentiableOn_tprod_cubicFactor (hinj : Function.Injective p) (hp : ∀ i, 2 ≤ p i)
    (ha : ∀ i, ‖a i‖ = 1) (hb : ∀ i, ‖b i‖ = 1) (hc : ∀ i, ‖c i‖ = 1) :
    DifferentiableOn ℂ (fun s => ∏' i, cubicFactor (p i) (a i) (b i) (c i) s)
      {s : ℂ | 1 < s.re} := by
  intro s hs
  have hs : 1 < s.re := hs
  obtain ⟨σ₀, h1, h2⟩ : ∃ σ₀ : ℝ, 1 < σ₀ ∧ σ₀ < s.re := exists_between hs
  let K : Set ℂ := {z | σ₀ < z.re}
  have hK : IsOpen K := isOpen_lt continuous_const Complex.continuous_re
  have hKd : ∀ i, DifferentiableOn ℂ (fun z => cubicFactor (p i) (a i) (b i) (c i) z) K :=
    fun i z hz => (differentiableAt_cubicFactor (hp i) (ha i) (hb i) (hc i)
      (by have : σ₀ < z.re := hz
          linarith)).differentiableWithinAt
  have hprod := ((summable_rpow_neg hinj h1).mul_left 14).hasProdLocallyUniformlyOn_one_add
    (f := fun i z => cubicFactor (p i) (a i) (b i) (c i) z - 1) hK
    (.of_forall fun i z hz => by
      have hz' : σ₀ < z.re := hz
      refine (norm_cubicFactor_sub_one_le (hp i) (ha i) (hb i) (hc i)
        (by linarith)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have : (2 : ℝ) ≤ p i := by exact_mod_cast hp i
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
    (fun i => ((hKd i).sub (differentiableOn_const _)).continuousOn)
  have hd : DifferentiableOn ℂ
      (fun z => ∏' i, (1 + (cubicFactor (p i) (a i) (b i) (c i) z - 1))) K :=
    hprod.differentiableOn (.of_forall fun _ => by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun i _ => hKd i)) hK
  have h3 := hd.differentiableAt (hK.mem_nhds h2)
  simp only [add_sub_cancel] at h3
  exact h3.differentiableWithinAt

end GlobalTheory.CompanionTheory.EulerThree
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqDiagonalOfUpperTriangularOfUnitary
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.RealPlace

theorem eq_diagonal_of_upperTriangular_of_unitary {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ)
    (hB : B.BlockTriangular id) (hBB : Bᴴ * B = 1) : B = diagonal (fun i => B i i) := by
  have hinv : B⁻¹ = Bᴴ := Matrix.inv_eq_left_inv hBB
  haveI : Invertible B := Matrix.invertibleOfIsUnitDet B (Matrix.isUnit_det_of_left_inverse hBB)
  have hT : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hB
  rw [hinv] at hT
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : Bᴴ j i = 0 := hT h
    rw [Matrix.conjTranspose_apply, star_eq_zero] at h1
    rw [h1, Matrix.diagonal_apply_ne _ (ne_of_lt h)]
  · simp
  · rw [hB h, Matrix.diagonal_apply_ne _ (ne_of_gt h)]

theorem flag_isometry_diagonal_on_frame (n r : ℕ) (J P p : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin r) ℂ) (hJ : IsUnit J.det) (hXY : Xᴴ * J * Y = 1)
    (_hP : P.PosDef) (_hPJ : P * J⁻¹ * P = J) (hPX : P * X = J * Y)
    (hpJ : pᴴ * J * p = J) (hpP : pᴴ * P * p = P)
    (B : Matrix (Fin r) (Fin r) ℂ) (hB : B.BlockTriangular id) (hpX : p * X = X * B) :
    ∃ d : Fin r → ℂ, p * X = X * diagonal d ∧ p * Y = Y * diagonal d := by
  have hXPX : Xᴴ * P * X = 1 := by
    rw [Matrix.mul_assoc, hPX, ← Matrix.mul_assoc]
    exact hXY
  have hBB : Bᴴ * B = 1 := by
    calc Bᴴ * B = Bᴴ * (Xᴴ * P * X) * B := by rw [hXPX, Matrix.mul_one]
      _ = (X * B)ᴴ * P * (X * B) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (p * X)ᴴ * P * (p * X) := by rw [hpX]
      _ = Xᴴ * (pᴴ * P * p) * X := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hpP]
          exact hXPX
  have hBd := eq_diagonal_of_upperTriangular_of_unitary B hB hBB
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin r) (Fin r) ℂ, D = diagonal (fun i => B i i) := ⟨_, rfl⟩
  have hBD : B = D := hBd.trans hD.symm
  have hpXD : p * X = X * D := by
    rw [hpX, hBD]
  have hr : pᴴ * (J * p * J⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hpJ, Matrix.mul_nonsing_inv J hJ]
  have hr' : (J * p * J⁻¹) * pᴴ = 1 := mul_eq_one_comm.mp hr
  have key : J * (p * Y) = J * (Y * D) := by
    calc J * (p * Y) = (J * p * J⁻¹) * pᴴ * (J * (p * Y)) := by rw [hr', Matrix.one_mul]
      _ = (J * p * J⁻¹) * (pᴴ * J * p) * Y := by simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * (J * Y) := by
          rw [hpJ]
          simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * (pᴴ * P * p * X) := by rw [hpP, hPX]
      _ = (J * p * J⁻¹) * pᴴ * (P * (p * X)) := by simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * pᴴ * (P * X * D) := by
          rw [hpXD]
          simp only [Matrix.mul_assoc]
      _ = (J * p * J⁻¹) * pᴴ * (J * (Y * D)) := by
          rw [hPX]
          simp only [Matrix.mul_assoc]
      _ = J * (Y * D) := by rw [hr', Matrix.one_mul]
  have hpYD : p * Y = Y * D := by
    calc p * Y = J⁻¹ * (J * (p * Y)) := by
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul J hJ, Matrix.one_mul]
      _ = J⁻¹ * (J * (Y * D)) := by rw [key]
      _ = Y * D := by
          simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul J hJ, Matrix.one_mul]
  exact ⟨fun i => B i i, hD ▸ hpXD, hD ▸ hpYD⟩

end GlobalTheory.CompanionTheory.RealPlace
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqOfNearOfCharpolyEq
section
open MeasureTheory Set Filter Matrix
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.WeylNear

theorem exists_diag (n : ℕ) (s : Matrix (Fin n) (Fin n) ℂ) (hs : s.charpoly.Separable) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ), Function.Injective l ∧
      P * Q = 1 ∧ Q * P = 1 ∧ Q * s * P = diagonal l := by
  have hnd : s.charpoly.roots.Nodup := Polynomial.nodup_roots hs
  have hcard : s.charpoly.roots.card = n := by
    have h1 := (IsAlgClosed.splits s.charpoly).natDegree_eq_card_roots
    rw [Matrix.charpoly_natDegree_eq_dim] at h1
    simpa using h1.symm
  have hc2 : s.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  let e := Finset.equivFinOfCardEq hc2
  let l : Fin n → ℂ := fun i => (e.symm i : ℂ)
  have hl : Function.Injective l := fun i j h =>
    e.symm.injective (Subtype.ext h)
  have hroot : ∀ i, s.charpoly.IsRoot (l i) := fun i => by
    have := (e.symm i).2
    rw [Multiset.mem_toFinset] at this
    exact Polynomial.isRoot_of_mem_roots this
  have hev : ∀ i, ∃ v : Fin n → ℂ, v ≠ 0 ∧ s *ᵥ v = l i • v := by
    intro i
    have h0 : Module.End.HasEigenvalue (Matrix.toLin' s : Module.End ℂ (Fin n → ℂ)) (l i) := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
      exact hroot i
    obtain ⟨v, hv⟩ := h0.exists_hasEigenvector
    refine ⟨v, hv.2, ?_⟩
    have := hv.apply_eq_smul
    simpa using this
  choose v hv0 hv using hev
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' s : Module.End ℂ (Fin n → ℂ)) l hl v
      (fun i => ⟨by
        rw [Module.End.mem_eigenspace_iff]; simpa using hv i, hv0 i⟩)
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => v j i
  have hcol : P.col = v := by
    ext j i; rfl
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp (by rw [hcol]; exact hli)
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hsP : s * P = P * diagonal l := by
    ext i j
    have := congrFun (hv j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, P, Matrix.of_apply]
    rw [this, mul_comm]
  refine ⟨P, P⁻¹, l, hl, Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet, ?_⟩
  rw [Matrix.mul_assoc, hsP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

end GlobalTheory.CompanionTheory.WeylNear
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdaptedMajorant
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.WittMajorant

variable {n : ℕ}

private theorem conj_mul (U V D E : Matrix (Fin n) (Fin n) ℂ) (h : V * U = 1) :
    (U * D * V) * (U * E * V) = U * (D * E) * V := by
  calc (U * D * V) * (U * E * V) = U * D * (V * U) * E * V := by
        simp only [Matrix.mul_assoc]
    _ = U * (D * E) * V := by
        rw [h]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem exists_abs_sign {R : Matrix (Fin n) (Fin n) ℂ} (hR : R.IsHermitian) :
    ∃ A S : Matrix (Fin n) (Fin n) ℂ,
      A.PosSemidef ∧ A = S * R ∧ A = R * S ∧ S * S * R = R := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hR.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : Uᴴ * U = 1 := by
    have := Unitary.star_mul_self_of_mem hR.eigenvectorUnitary.2
    simpa [star_eq_conjTranspose] using this
  have hspec : R = U * diagonal (fun i => ((hR.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have := hR.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def] using this
  set d : Fin n → ℂ := fun i => ((hR.eigenvalues i : ℝ) : ℂ) with hd
  set a : Fin n → ℂ := fun i => ((|hR.eigenvalues i| : ℝ) : ℂ) with ha
  set s : Fin n → ℂ := fun i => (((SignType.sign (hR.eigenvalues i) : SignType) : ℝ) : ℂ) with hs
  have hsd : ∀ i, s i * d i = a i := by
    intro i
    simp only [hs, hd, ha]
    rw [← Complex.ofReal_mul, sign_mul_self]
  have hds : ∀ i, d i * s i = a i := fun i => by rw [mul_comm, hsd]
  have hssd : ∀ i, s i * s i * d i = d i := by
    intro i
    simp only [hs, hd]
    rcases lt_trichotomy (hR.eigenvalues i) 0 with h | h | h
    · simp [sign_neg h]
    · simp [h]
    · simp [sign_pos h]
  refine ⟨U * diagonal a * Uᴴ, U * diagonal s * Uᴴ, ?_, ?_, ?_, ?_⟩
  · have h0 : (diagonal a).PosSemidef := by
      rw [posSemidef_diagonal_iff]
      intro i
      simp only [ha]
      exact_mod_cast abs_nonneg _
    have := h0.conjTranspose_mul_mul_same Uᴴ
    simpa using this
  · conv_rhs => rw [hspec]
    rw [conj_mul _ _ _ _ hUU, diagonal_mul_diagonal]
    simp only [hsd]
  · conv_rhs => rw [hspec]
    rw [conj_mul _ _ _ _ hUU, diagonal_mul_diagonal]
    simp only [hds]
  · conv_lhs => rw [hspec]
    rw [conj_mul _ _ _ _ hUU, conj_mul _ _ _ _ hUU, diagonal_mul_diagonal, diagonal_mul_diagonal]
    simp only [hssd]
    exact hspec.symm

theorem exists_adapted_majorant (n r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin r) ℂ) (hJ : J.IsHermitian) (hdet : IsUnit J.det)
    (hXX : Xᴴ * J * X = 0) (hYY : Yᴴ * J * Y = 0) (hXY : Xᴴ * J * Y = 1) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.PosDef ∧ P * J⁻¹ * P = J ∧ P * X = J * Y := by
  have hJi : J⁻¹ * J = 1 := nonsing_inv_mul J hdet
  have hJi' : J * J⁻¹ = 1 := mul_nonsing_inv J hdet
  have hYX : Yᴴ * J * X = 1 := by
    have := congrArg conjTranspose hXY
    simpa [conjTranspose_mul, hJ.eq, Matrix.mul_assoc] using this
  have xx : Xᴴ * (J * X) = 0 := by rw [← Matrix.mul_assoc]; exact hXX
  have yy : Yᴴ * (J * Y) = 0 := by rw [← Matrix.mul_assoc]; exact hYY
  have xy : Xᴴ * (J * Y) = 1 := by rw [← Matrix.mul_assoc]; exact hXY
  have yx : Yᴴ * (J * X) = 1 := by rw [← Matrix.mul_assoc]; exact hYX
  set R : Matrix (Fin n) (Fin n) ℂ := J⁻¹ - X * Yᴴ - Y * Xᴴ with hRdef
  have hRh : R.IsHermitian := by
    have hi : (J⁻¹)ᴴ = J⁻¹ := (IsHermitian.inv hJ).eq
    unfold IsHermitian
    rw [hRdef, conjTranspose_sub, conjTranspose_sub, hi, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, conjTranspose_conjTranspose]
    abel
  have hRX : R * (J * X) = 0 := by
    rw [hRdef, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, yx, xx,
      ← Matrix.mul_assoc J⁻¹, hJi]
    simp
  have hRY : R * (J * Y) = 0 := by
    rw [hRdef, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, yy, xy,
      ← Matrix.mul_assoc J⁻¹, hJi]
    simp
  have hRJR : R * (J * R) = R := by
    have e : J * R = 1 - (J * X) * Yᴴ - (J * Y) * Xᴴ := by
      rw [hRdef, Matrix.mul_sub, Matrix.mul_sub, hJi', Matrix.mul_assoc, Matrix.mul_assoc]
    have e1 : R * (J * X * Yᴴ) = (R * (J * X)) * Yᴴ := (Matrix.mul_assoc _ _ _).symm
    have e2 : R * (J * Y * Xᴴ) = (R * (J * Y)) * Xᴴ := (Matrix.mul_assoc _ _ _).symm
    rw [e, Matrix.mul_sub, Matrix.mul_sub, e1, e2, hRX, hRY]
    simp
  obtain ⟨A, S, hA, hAS, hAR, hSSR⟩ := exists_abs_sign hRh
  have hAh : Aᴴ = A := hA.isHermitian.eq
  have hAX : A * (J * X) = 0 := by
    rw [hAS, Matrix.mul_assoc, hRX, Matrix.mul_zero]
  have hAY : A * (J * Y) = 0 := by
    rw [hAS, Matrix.mul_assoc, hRY, Matrix.mul_zero]
  have hXA : Xᴴ * (J * A) = 0 := by
    have := congrArg conjTranspose hAX
    simpa [conjTranspose_mul, hJ.eq, hAh, Matrix.mul_assoc] using this
  have hYA : Yᴴ * (J * A) = 0 := by
    have := congrArg conjTranspose hAY
    simpa [conjTranspose_mul, hJ.eq, hAh, Matrix.mul_assoc] using this
  have hAJA : A * (J * A) = R := by
    calc A * (J * A) = (S * R) * (J * (R * S)) := by rw [← hAS, ← hAR]
      _ = S * (R * (J * R)) * S := by simp only [Matrix.mul_assoc]
      _ = S * (R * S) := by rw [hRJR, Matrix.mul_assoc]
      _ = S * (S * R) := by rw [← hAR, hAS]
      _ = R := by rw [← Matrix.mul_assoc, hSSR]
  set T : Matrix (Fin n) (Fin n) ℂ := X * Xᴴ + Y * Yᴴ + A with hTdef
  have hTX : T * (J * X) = Y := by
    rw [hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, xx, yx, hAX]
    simp
  have hTY : T * (J * Y) = X := by
    rw [hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, xy, yy, hAY]
    simp
  have hTA : T * (J * A) = R := by
    rw [hTdef, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, hXA, hYA,
      hAJA]
    simp
  have hTJT : T * (J * T) = J⁻¹ := by
    have e : J * T = (J * X) * Xᴴ + (J * Y) * Yᴴ + J * A := by
      rw [hTdef, Matrix.mul_add, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc]
    have e1 : T * (J * X * Xᴴ) = (T * (J * X)) * Xᴴ := (Matrix.mul_assoc _ _ _).symm
    have e2 : T * (J * Y * Yᴴ) = (T * (J * Y)) * Yᴴ := (Matrix.mul_assoc _ _ _).symm
    rw [e, Matrix.mul_add, Matrix.mul_add, e1, e2, hTX, hTY, hTA, hRdef]
    abel
  have hTpsd : T.PosSemidef :=
    ((posSemidef_self_mul_conjTranspose X).add (posSemidef_self_mul_conjTranspose Y)).add hA
  have hTunit : IsUnit T := by
    have h1 : T * (J * T * J) = 1 := by
      calc T * (J * T * J) = (T * (J * T)) * J := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hTJT, hJi]
    exact (Matrix.isUnit_iff_isUnit_det T).2 (Matrix.isUnit_det_of_right_inverse h1)
  have hTpd : T.PosDef := hTpsd.posDef_iff_isUnit.2 hTunit
  have hJinj : Function.Injective J.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det J).2 hdet)
  refine ⟨J * T * J, ?_, ?_, ?_⟩
  · have := hTpd.conjTranspose_mul_mul_same hJinj
    rwa [hJ.eq] at this
  · calc J * T * J * J⁻¹ * (J * T * J) = J * (T * (J * T)) * J := by
          have h2 : J * T * J * J⁻¹ = J * T := by
            rw [Matrix.mul_assoc (J * T), hJi', Matrix.mul_one]
          rw [h2]
          simp only [Matrix.mul_assoc]
      _ = J := by rw [hTJT, hJi', Matrix.one_mul]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, hTX]

end GlobalTheory.CompanionTheory.WittMajorant
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBumpWithNonzeroIntegral
section
open MeasureTheory
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.MeasureBump

theorem exists_integral_ne_zero_of_carried_by_isOpen
    (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) (U : Set X)
    (hU : IsOpen U) (hc : m Uᶜ = 0) (hm : m ≠ 0)
    (hint : ∀ χ : X → ℝ, Continuous χ → HasCompactSupport χ → tsupport χ ⊆ U → Integrable χ m) :
    ∃ χ : X → ℝ, Continuous χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ ∫ x, χ x ∂m ≠ 0 := by
  have hmU : m U ≠ 0 := by
    intro h0
    apply hm
    rw [← Measure.measure_univ_eq_zero]
    have huniv : (Set.univ : Set X) = U ∪ Uᶜ := (Set.union_compl_self U).symm
    rw [huniv]
    exact measure_union_null h0 hc
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  have hσ : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance
  obtain ⟨K, hK, hKU⟩ := hσ
  have hex : ∃ n, m (K n) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hmU
    rw [← hKU]
    exact measure_iUnion_null hcon
  obtain ⟨n, hn⟩ := hex
  have hsub : K n ⊆ U := hKU ▸ Set.subset_iUnion K n
  obtain ⟨f, hf1, hfc, hfU, hf01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen (hK n) hU hsub
  refine ⟨f, f.continuous, hfc, hfU, ?_⟩
  have hI : Integrable (f : X → ℝ) m := hint f f.continuous hfc hfU
  have hnn : 0 ≤ᵐ[m] (f : X → ℝ) := Filter.Eventually.of_forall fun x => (hf01 x).1
  have hpos : 0 < ∫ x, f x ∂m := by
    rw [integral_pos_iff_support_of_nonneg_ae hnn hI]
    refine lt_of_lt_of_le (pos_iff_ne_zero.2 hn) (measure_mono ?_)
    intro x hx
    simp [Function.mem_support, hf1 hx]
  exact hpos.ne'

end GlobalTheory.CompanionTheory.MeasureBump
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDualAll
section
namespace GlobalTheory.CompanionTheory.DualFin

theorem finite_dual_all : ∀ (R M : Type) [CommRing R] [Finite R] [AddCommGroup M] [Module R M] [Finite M], Finite (Module.Dual R M) :=
  fun R M _ _ _ _ _ =>
    Finite.of_injective (fun f : Module.Dual R M => (f : M → R)) DFunLike.coe_injective

end GlobalTheory.CompanionTheory.DualFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFractionRingInteger
section
namespace GlobalTheory.CompanionTheory.LocalFieldValuationRing

theorem isFractionRing_integer (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : IsFractionRing (ValuativeRel.valuation k).integer k :=
  (Valuation.integer.integers (ValuativeRel.valuation k)).isFractionRing

end GlobalTheory.CompanionTheory.LocalFieldValuationRing
end

