import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GlFreeAlgebraToSpecialLinearEmbInjectiveHom
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.EmbHom

variable {R A β κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β]
  [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A)

theorem res_one' : res b (1 : Matrix κ κ A) = 1 := by
  ext ⟨i, x⟩ ⟨j, y⟩
  by_cases h : i = j
  · subst h
    simp [res, Matrix.one_apply]
  · simp [res, Matrix.one_apply, h]

omit [DecidableEq κ] in
theorem res_mul' (g h : Matrix κ κ A) : res b (g * h) = res b g * res b h := by
  ext ⟨i, x⟩ ⟨j, y⟩
  simp only [res, Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul, Matrix.sum_apply,
    Fintype.sum_prod_type]

omit [Fintype κ] [DecidableEq κ] in
theorem res_inj' (g h : Matrix κ κ A) (e : res b g = res b h) : g = h := by
  ext i j
  apply Algebra.leftMulMatrix_injective b
  ext x y
  exact congrFun (congrFun e (i, x)) (j, y)

theorem emb_one' : emb b (1 : GL κ A) = 1 := by
  unfold emb
  rw [inv_one, Units.val_one, res_one', Matrix.det_one, ← Matrix.fromBlocks_one]
  congr 1

theorem emb_mul' (g h : GL κ A) : emb b (g * h) = emb b g * emb b h := by
  unfold emb
  rw [Matrix.fromBlocks_multiply, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, res_mul', res_mul',
    Matrix.det_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  ext i j
  simp [Matrix.mul_apply, mul_comm]

theorem emb_det' (g : GL κ A) : (emb b g).det = 1 := by
  unfold emb
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique (n := Unit), Matrix.of_apply, ← Matrix.det_mul, ← res_mul',
    Units.mul_inv, res_one', Matrix.det_one]

theorem emb_adjugate' (g : GL κ A) : (emb b g).adjugate = emb b g⁻¹ := by
  have h1 : emb b g * emb b g⁻¹ = 1 := by rw [← emb_mul', mul_inv_cancel, emb_one']
  calc (emb b g).adjugate = (emb b g).adjugate * (emb b g * emb b g⁻¹) := by rw [h1, Matrix.mul_one]
    _ = emb b g⁻¹ := by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, emb_det', one_smul, Matrix.one_mul]

theorem emb_injective' : Function.Injective (fun g : GL κ A => emb b g) := by
  intro g h e
  apply Units.ext
  apply res_inj' b
  exact (Matrix.fromBlocks_inj.mp e).1

theorem emb_hom : ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), emb b (1 : GL κ A) = 1 ∧ (∀ g h : GL κ A, emb b (g * h) = emb b g * emb b h) ∧ (∀ g : GL κ A, (emb b g).det = 1 ∧ (emb b g).adjugate = emb b g⁻¹) ∧ Function.Injective (fun g : GL κ A => emb b g) := by
  intro R A β κ _ _ _ _ _ _ _ b
  exact ⟨emb_one' b, emb_mul' b, fun g => ⟨emb_det' b g, emb_adjugate' b g⟩, emb_injective' b⟩

end GlobalTheory.ClassFin.EmbHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GramLeadingMinorLowerBoundIntegral
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem gramLB_shift {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (t : ℝ) :
    ∃ U : Matrix n n ℝ, U * Uᴴ = 1 ∧
      A + t • (1 : Matrix n n ℝ) = U * diagonal (fun i => hA.eigenvalues i + t) * Uᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix n n ℝ), Unitary.coe_mul_star_self _, ?_⟩
  have hU : (hA.eigenvectorUnitary : Matrix n n ℝ) * star (hA.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    Unitary.coe_mul_star_self _
  have hD : diagonal (fun i => hA.eigenvalues i + t) =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) + t • (1 : Matrix n n ℝ) := by
    ext i j
    by_cases h : i = j <;> simp [diagonal, h]
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, ← star_eq_conjTranspose, hU]

theorem gramLB_one_le_det {n : Type} [Fintype n] [DecidableEq n] {R : Matrix n n ℝ}
    (hR : R.PosSemidef) : 1 ≤ (R + 1).det := by
  obtain ⟨U, hU, hEq⟩ := gramLB_shift hR.1 1
  rw [one_smul] at hEq
  have hdet : U.det * Uᴴ.det = 1 := by rw [← det_mul, hU, det_one]
  rw [hEq, det_mul, det_mul, det_diagonal]
  have e : U.det * (∏ i, (hR.1.eigenvalues i + 1)) * Uᴴ.det = ∏ i, (hR.1.eigenvalues i + 1) := by
    linear_combination (∏ i, (hR.1.eigenvalues i + 1)) * hdet
  rw [e]
  calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
    _ ≤ ∏ i, (hR.1.eigenvalues i + 1) :=
      Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => by linarith [hR.eigenvalues_nonneg i]

theorem gramLB_exists_shift {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.PosDef) : ∃ k : ℝ, 0 < k ∧ k ≤ 1 ∧ (A - k • (1 : Matrix n n ℝ)).PosSemidef := by
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ hA.1.eigenvalues i := by
    rcases isEmpty_or_nonempty n with hn | hn
    · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
    · obtain ⟨i0, hi0⟩ := Finite.exists_min hA.1.eigenvalues
      exact ⟨_, hA.eigenvalues_pos i0, hi0⟩
  refine ⟨min 1 m, lt_min one_pos hm0, min_le_left _ _, ?_⟩
  obtain ⟨U, -, hEq⟩ := gramLB_shift hA.1 (-(min 1 m))
  rw [sub_eq_add_neg, ← neg_smul, hEq]
  exact (posSemidef_diagonal_iff.2 fun i => by linarith [hm i, min_le_right 1 m]).mul_mul_conjTranspose_same U

open scoped MatrixOrder in
theorem gramLB_det_mono {n : Type} [Fintype n] [DecidableEq n] {P Q : Matrix n n ℝ}
    (hP : P.PosDef) (hQ : Q.PosSemidef) : P.det ≤ (P + Q).det := by
  obtain ⟨U, hU, hEq⟩ := gramLB_shift hP.1 0
  simp only [zero_smul, add_zero] at hEq
  have hd : ∀ i, 0 < hP.1.eigenvalues i := hP.eigenvalues_pos
  have hUU : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  let s : n → ℝ := fun i => (Real.sqrt (hP.1.eigenvalues i))⁻¹
  let B : Matrix n n ℝ := U * diagonal s
  have hBt : Bᴴ = diagonal s * Uᴴ := by
    simp [B]
  have hBPB : Bᴴ * P * B = 1 := by
    rw [hBt, hEq]
    simp only [B, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul, ← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul,
      diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hs : Real.sqrt (hP.1.eigenvalues i) * Real.sqrt (hP.1.eigenvalues i) = hP.1.eigenvalues i :=
      Real.mul_self_sqrt (hd i).le
    have hs0 : Real.sqrt (hP.1.eigenvalues i) ≠ 0 := (Real.sqrt_pos.2 (hd i)).ne'
    simp only [s]
    field_simp
    try nlinarith [hs, Real.sq_sqrt (hd i).le]
  have hsum : Bᴴ * (P + Q) * B = 1 + Bᴴ * Q * B := by
    rw [Matrix.mul_add, Matrix.add_mul, hBPB]
  have h1 : Bᴴ.det * B.det * P.det = 1 := by
    have e := congrArg det hBPB
    rw [det_mul, det_mul, det_one] at e
    linear_combination e
  have h2 : Bᴴ.det * B.det * (P + Q).det = (1 + Bᴴ * Q * B).det := by
    rw [← hsum, det_mul (Bᴴ * (P + Q)) B, det_mul Bᴴ (P + Q)]
    ring
  have h3 : 1 ≤ (1 + Bᴴ * Q * B).det := by
    rw [add_comm]
    exact gramLB_one_le_det (hQ.conjTranspose_mul_mul_same B)
  have hc : 0 < Bᴴ.det * B.det := by
    have := hP.det_pos
    by_contra hneg
    nlinarith [not_lt.mp hneg]
  exact le_of_mul_le_mul_left (by linarith) hc

theorem gramLB_posDef {n : Type} [Fintype n] [DecidableEq n] {g : Matrix n n ℝ}
    (hg : g.det ≠ 0) : (gᵀ * g).PosDef := by
  rw [← conjTranspose_eq_transpose_of_trivial]
  exact PosDef.conjTranspose_mul_self g
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det g).2 (Ne.isUnit hg)))

theorem gram_leading_minor_lower_bound :
    ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ γ : Matrix (Fin N) (Fin N) ℤ, γ.det ≠ 0 → ∀ (j : ℕ) (h : j ≤ N), c ≤ (((g * γ.map (Int.cast : ℤ → ℝ))ᵀ * (g * γ.map (Int.cast : ℤ → ℝ))).submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  intro N g hg
  obtain ⟨k, hk0, hk1, hkQ⟩ := gramLB_exists_shift (gramLB_posDef hg)
  refine ⟨k ^ N, pow_pos hk0 N, fun γ hγ j hj => ?_⟩
  set Γ : Matrix (Fin N) (Fin N) ℝ := γ.map (Int.cast : ℤ → ℝ) with hΓ
  set E : Fin j → Fin N := Fin.castLE hj with hE
  let C : Matrix (Fin N) (Fin j) ℝ := Γ.submatrix id E
  let Cz : Matrix (Fin N) (Fin j) ℤ := γ.submatrix id E
  have hGram : ((g * Γ)ᵀ * (g * Γ)).submatrix E E = Cᵀ * (gᵀ * g) * C := by
    have e1 : (g * Γ)ᵀ * (g * Γ) = Γᵀ * (gᵀ * g) * Γ := by
      rw [transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, Matrix.submatrix_mul _ _ E id E Function.bijective_id,
      Matrix.submatrix_mul _ _ E id id Function.bijective_id, submatrix_id_id, transpose_submatrix]
  have hsplit : Cᵀ * (gᵀ * g) * C = k • (Cᵀ * C) + Cᵀ * (gᵀ * g - k • 1) * C := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    abel
  have hΓdet : Γ.det ≠ 0 := by
    have e := (Int.castRingHom ℝ).map_det γ
    rw [show Γ = (Int.castRingHom ℝ).mapMatrix γ from rfl, ← e]
    simpa using hγ
  have hCinj : Function.Injective C.mulVec := by
    have hC : C = Γ * (1 : Matrix (Fin N) (Fin N) ℝ).submatrix id E := by
      rw [← Matrix.submatrix_id_id Γ, ← Matrix.submatrix_mul _ _ id id E Function.bijective_id,
        Matrix.mul_one]
    have hI : Function.Injective ((1 : Matrix (Fin N) (Fin N) ℝ).submatrix id E).mulVec := by
      intro x y hxy
      funext a
      have hEinj : Function.Injective E := Fin.castLE_injective hj
      have e := congrFun hxy (E a)
      simpa [mulVec, dotProduct, Matrix.one_apply, hEinj.eq_iff] using e
    rw [hC]
    intro x y hxy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hxy
    exact hI (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det Γ).2 (Ne.isUnit hΓdet)) hxy)
  have hCC : (Cᵀ * C).PosDef := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact PosDef.conjTranspose_mul_self C hCinj
  have hQ' : (Cᵀ * (gᵀ * g - k • 1) * C).PosSemidef := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hkQ.conjTranspose_mul_mul_same C
  have hCz : Cᵀ * C = (Int.castRingHom ℝ).mapMatrix (Czᵀ * Cz) := by
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
    rfl
  have hdet1 : 1 ≤ (Cᵀ * C).det := by
    have hpos := hCC.det_pos
    rw [hCz, ← RingHom.map_det, eq_intCast] at hpos
    rw [hCz, ← RingHom.map_det, eq_intCast]
    have hz : 0 < (Czᵀ * Cz).det := by exact_mod_cast hpos
    have hz1 : (1 : ℤ) ≤ (Czᵀ * Cz).det := hz
    exact_mod_cast hz1
  calc k ^ N ≤ k ^ j := pow_le_pow_of_le_one hk0.le hk1 hj
    _ ≤ k ^ j * (Cᵀ * C).det := le_mul_of_one_le_right (pow_nonneg hk0.le _) hdet1
    _ = (k • (Cᵀ * C)).det := by rw [det_smul, Fintype.card_fin]
    _ ≤ (k • (Cᵀ * C) + Cᵀ * (gᵀ * g - k • 1) * C).det := gramLB_det_mono (hCC.smul hk0) hQ'
    _ = _ := by rw [← hsplit, ← hGram]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GramMinorSwapAdjacentColumns
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

private theorem exch_sum_split {N : ℕ} (p q : Fin N) (hq : (q : ℕ) = p + 1) (f : Fin N → ℝ)
    (hf : ∀ r, q < r → f r = 0) :
    ∑ r, f r = ∑ r ∈ Finset.univ.filter (· < p), f r + (f p + f q) := by
  have hpq : p ≠ q := fun e => by have := congrArg Fin.val e; omega
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· < p)]
  congr 1
  have hsub : ({p, q} : Finset (Fin N)) ⊆ Finset.univ.filter (fun r => ¬ r < p) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Fin.le_def]
    rcases hx with rfl | rfl <;> omega
  rw [← Finset.sum_subset hsub, Finset.sum_pair hpq]
  intro x hx hx'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Fin.le_def] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'
  apply hf
  rw [Fin.lt_def]
  have h1 : (x : ℕ) ≠ p := fun e => hx'.1 (Fin.ext e)
  have h2 : (x : ℕ) ≠ q := fun e => hx'.2 (Fin.ext e)
  omega

private theorem det_updateRow_last_single_eq_mul_det_submatrix {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (x : ℝ) :
    (X.updateRow (Fin.last m) (Pi.single (Fin.last m) x)).det =
      x * (X.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row _ (Fin.last m), Finset.sum_eq_single (Fin.last m)]
  · have hsub : (X.updateRow (Fin.last m) (Pi.single (Fin.last m) x)).submatrix
        (Fin.last m).succAbove (Fin.last m).succAbove = X.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_last]
      rw [Matrix.updateRow_ne (Fin.castSucc_lt_last i).ne]
    rw [hsub, Matrix.updateRow_self, Pi.single_eq_same, Fin.val_last, Even.neg_one_pow ⟨m, rfl⟩, one_mul]
  · intro j _ hj
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne hj, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem gram_minor_swap_columns : ∀ (N : ℕ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n g g' : Matrix (Fin N) (Fin N) ℝ) (p q : Fin N), kᵀ * k = 1 → (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → (q : ℕ) = p + 1 → g = k * diagonal a * n → g' = g.submatrix id (Equiv.swap p q) → (∀ (j : ℕ) (h : j ≤ N), j ≠ q → ((g'ᵀ * g').submatrix (Fin.castLE h) (Fin.castLE h)).det = ((gᵀ * g).submatrix (Fin.castLE h) (Fin.castLE h)).det) ∧ ∀ h : (q : ℕ) ≤ N, ((g'ᵀ * g').submatrix (Fin.castLE h) (Fin.castLE h)).det = (∏ l ∈ Finset.univ.filter (· < p), a l ^ 2) * (a q ^ 2 + n p q ^ 2 * a p ^ 2) := by
  intro N k a n g g' p q hk hn1 hn0 hq hg hg'

  have hG : gᵀ * g = (diagonal a * n)ᵀ * (diagonal a * n) := by
    rw [hg]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc kᵀ k, hk, Matrix.one_mul]
  have hG' : g'ᵀ * g' = (gᵀ * g).submatrix (Equiv.swap p q) (Equiv.swap p q) := by
    rw [hg']
    ext i j
    simp [Matrix.mul_apply]
  rw [hG', hG]
  set M : Matrix (Fin N) (Fin N) ℝ := diagonal a * n with hM
  have hMe : ∀ i j, M i j = a i * n i j := fun i j => by simp [hM, Matrix.diagonal_mul]
  have hMl : ∀ i j, j < i → M i j = 0 := fun i j h => by rw [hMe, hn0 i j h, mul_zero]
  have hMd : ∀ i, M i i = a i := fun i => by rw [hMe, hn1, mul_one]
  refine ⟨fun j hj hjq => ?_, fun h => ?_⟩
  · by_cases hjp : j ≤ (p : ℕ)
    ·
      congr 1
      have hfix : ∀ z : Fin j, Equiv.swap p q (Fin.castLE hj z) = Fin.castLE hj z := by
        intro z
        have hz := z.isLt
        apply Equiv.swap_apply_of_ne_of_ne
        · intro e
          have := congrArg Fin.val e
          simp only [Fin.coe_castLE] at this
          omega
        · intro e
          have := congrArg Fin.val e
          simp only [Fin.coe_castLE] at this
          omega
      ext x y
      simp only [Matrix.submatrix_apply, hfix]
    ·
      have hpj : (p : ℕ) < j := by omega
      have hqj : (q : ℕ) < j := by omega
      have e1 : Fin.castLE hj ⟨p, hpj⟩ = p := Fin.ext rfl
      have e2 : Fin.castLE hj ⟨q, hqj⟩ = q := Fin.ext rfl
      have hs : ∀ z : Fin j, Equiv.swap p q (Fin.castLE hj z) =
          Fin.castLE hj (Equiv.swap ⟨p, hpj⟩ ⟨q, hqj⟩ z) := by
        intro z
        have := (Fin.castLE_injective hj).swap_apply ⟨p, hpj⟩ ⟨q, hqj⟩ z
        rwa [e1, e2] at this
      have hsub : ((Mᵀ * M).submatrix (Equiv.swap p q) (Equiv.swap p q)).submatrix (Fin.castLE hj)
          (Fin.castLE hj) = ((Mᵀ * M).submatrix (Fin.castLE hj) (Fin.castLE hj)).submatrix
          (Equiv.swap (⟨p, hpj⟩ : Fin j) ⟨q, hqj⟩) (Equiv.swap (⟨p, hpj⟩ : Fin j) ⟨q, hqj⟩) := by
        ext x y
        simp only [Matrix.submatrix_apply, hs]
      rw [hsub, Matrix.det_submatrix_equiv_self]
  · obtain ⟨p, hp⟩ := p
    obtain ⟨q, hqN⟩ := q
    change q = p + 1 at hq
    subst hq
    have h' : p + 1 ≤ N := h
    set P : Fin N := ⟨p, hp⟩ with hP
    set Q : Fin N := ⟨p + 1, hqN⟩ with hQ
    set σ := Equiv.swap P Q with hσ
    set c : Fin (p + 1) → Fin N := Fin.castLE h' with hc
    show (((Mᵀ * M).submatrix σ σ).submatrix c c).det = _
    have hcl : c (Fin.last p) = P := Fin.ext rfl
    have hσc : ∀ s : Fin (p + 1), s ≠ Fin.last p → σ (c s) = c s := by
      intro s hs
      have h1 : (s : ℕ) < p := by
        have := s.isLt
        have : (s : ℕ) ≠ p := fun e => hs (Fin.ext e)
        omega
      apply Equiv.swap_apply_of_ne_of_ne
      · intro e
        have := congrArg Fin.val e
        change (s : ℕ) = p at this
        omega
      · intro e
        have := congrArg Fin.val e
        change (s : ℕ) = p + 1 at this
        omega
    have hσl : σ (c (Fin.last p)) = Q := by
      rw [hcl]
      exact Equiv.swap_apply_left P Q
    have hle : ∀ s, σ (c s) ≤ Q := by
      intro s
      by_cases hs : s = Fin.last p
      · rw [hs, hσl]
      · rw [hσc s hs, Fin.le_def]
        change (s : ℕ) ≤ p + 1
        have := s.isLt
        omega

    set B : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := Matrix.of fun s i => M (c s) (σ (c i)) with hB
    have hBe : ∀ s i, B s i = M (c s) (σ (c i)) := fun s i => rfl
    set emb : Fin p ↪ Fin N :=
      ⟨fun i : Fin p => c i.castSucc, fun x y e => by simpa [Fin.ext_iff, hc] using e⟩ with hemb
    have hembx : ∀ x, emb x = c x.castSucc := fun x => rfl
    have hfilt : Finset.univ.filter (· < P) = (Finset.univ : Finset (Fin p)).map emb := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro hl
        exact ⟨⟨l, hl⟩, Fin.ext rfl⟩
      · rintro ⟨i, _, rfl⟩
        exact i.isLt

    have hX : ((Mᵀ * M).submatrix σ σ).submatrix c c =
        (Bᵀ * B).updateRow (Fin.last p) ((Bᵀ * B) (Fin.last p) + Pi.single (Fin.last p) (a Q ^ 2)) := by
      ext i j
      have hsum : (((Mᵀ * M).submatrix σ σ).submatrix c c) i j =
          (Bᵀ * B) i j + M Q (σ (c i)) * M Q (σ (c j)) := by
        simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, hBe]
        rw [exch_sum_split P Q rfl _ (fun r hr => by rw [hMl r _ (lt_of_le_of_lt (hle i) hr), zero_mul]),
          Fin.sum_univ_castSucc, hfilt, Finset.sum_map, hcl]
        simp only [hembx]
        ring
      rw [hsum]
      by_cases hi : i = Fin.last p
      · subst hi
        rw [Matrix.updateRow_self, Pi.add_apply]
        by_cases hj : j = Fin.last p
        · subst hj
          rw [hσl, hMd, Pi.single_eq_same]
          ring
        · rw [hσl, hσc j hj, hMl Q (c j) (Fin.lt_def.2 j.isLt), mul_zero, Pi.single_eq_of_ne hj]
      · rw [Matrix.updateRow_ne hi, hσc i hi, hMl Q (c i) (Fin.lt_def.2 i.isLt), zero_mul, add_zero]
    have hBT : B.BlockTriangular id := by
      intro s i hi
      have hil : i ≠ Fin.last p := fun e => by
        rw [e] at hi
        exact (not_lt.2 (Fin.le_last s)) hi
      rw [hBe, hσc i hil]
      exact hMl _ _ (Fin.lt_def.2 (Fin.lt_def.1 hi))
    have hdB : B.det = (∏ i : Fin p, a (c i.castSucc)) * (a P * n P Q) := by
      rw [Matrix.det_of_upperTriangular hBT, Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        rw [hBe, hσc _ (Fin.castSucc_lt_last i).ne, hMd]
      · rw [hBe, hσl, hcl, hMe]
    have hminor : (Bᵀ * B).submatrix Fin.castSucc Fin.castSucc =
        (B.submatrix Fin.castSucc Fin.castSucc)ᵀ * B.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
      rw [Fin.sum_univ_castSucc]
      have hz : B (Fin.last p) i.castSucc = 0 := by
        rw [hBe, hσc _ (Fin.castSucc_lt_last i).ne, hcl]
        exact hMl _ _ (Fin.lt_def.2 (Fin.lt_def.1 (Fin.castSucc_lt_last i)))
      rw [hz, zero_mul, add_zero]
    have hBT' : (B.submatrix Fin.castSucc Fin.castSucc).BlockTriangular id := by
      intro s i hi
      exact hBT (Fin.castSucc_lt_castSucc_iff.2 hi)
    have hdB' : (B.submatrix Fin.castSucc Fin.castSucc).det = ∏ i : Fin p, a (c i.castSucc) := by
      rw [Matrix.det_of_upperTriangular hBT']
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Matrix.submatrix_apply, hBe, hσc _ (Fin.castSucc_lt_last i).ne, hMd]
    have hprod : ∏ l ∈ Finset.univ.filter (· < P), a l ^ 2 = (∏ i : Fin p, a (c i.castSucc)) ^ 2 := by
      rw [hfilt, Finset.prod_map, ← Finset.prod_pow]
      simp only [hembx]
    rw [hX, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, det_updateRow_last_single_eq_mul_det_submatrix, hminor,
      Matrix.det_mul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_transpose, hdB, hdB', hprod]
    ring

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HigherUnitsLeSquaresHigherUnits
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

namespace DeepSquares

end DeepSquares

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma exp_neg_two_mul_le_mul_of_lt {e : ℕ} {a b : ℤᵐ⁰}
    (ha : WithZero.exp (-((e : ℤ) + 1)) < a) (hb : WithZero.exp (-((e : ℤ) + 1)) < b) :
    WithZero.exp (-(2 * (e : ℤ))) ≤ a * b := by
  obtain ⟨k, rfl⟩ : ∃ k, WithZero.exp k = a := ⟨_, WithZero.exp_log (ne_bot_of_gt ha)⟩
  obtain ⟨l, rfl⟩ : ∃ l, WithZero.exp l = b := ⟨_, WithZero.exp_log (ne_bot_of_gt hb)⟩
  rw [WithZero.exp_lt_exp] at ha hb
  rw [← WithZero.exp_add, WithZero.exp_le_exp]
  omega

open NumberField IsDedekindDomain in
open scoped WithZero in

theorem _root_.GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (e : ℕ),
    Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) →
    _root_.GlobalTheory.QNorm.hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (2 * e + 1) ≤
      _root_.GlobalTheory.QNorm.sqs
        (_root_.GlobalTheory.QNorm.hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (e + 1)) := by
  intro F _ _ v e h2 x hx
  unfold _root_.GlobalTheory.QNorm.hiUnits at hx
  unfold _root_.GlobalTheory.QNorm.sqs _root_.GlobalTheory.QNorm.hiUnits
  obtain ⟨-, hx1⟩ := hx
  set w : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v
  have h4 : w 4 = WithZero.exp (-(2 * e : ℤ)) := by
    have : (4 : v.adicCompletion F) = 2 * 2 := by norm_num
    rw [this, map_mul, h2, ← WithZero.exp_add]; congr 1; ring
  have hlt : w ((x : v.adicCompletion F) - 1) < w 4 := by
    refine lt_of_le_of_lt hx1 ?_
    rw [h4, WithZero.exp_lt_exp]; push_cast; omega
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v _ hlt
  have hprod : w (r - 1) * w (r + 1) ≤ WithZero.exp (-((2 * e + 1 : ℕ) : ℤ)) := by
    rw [← map_mul, show (r - 1) * (r + 1) = r * r - 1 by ring, ← hr]; exact hx1
  obtain ⟨s, hs, hs1⟩ : ∃ s : v.adicCompletion F, s * s = x ∧
      w (s - 1) ≤ WithZero.exp (-((e + 1 : ℕ) : ℤ)) := by
    by_cases hm : w (r - 1) ≤ WithZero.exp (-((e + 1 : ℕ) : ℤ))
    · exact ⟨r, hr.symm, hm⟩
    by_cases hp : w (r + 1) ≤ WithZero.exp (-((e + 1 : ℕ) : ℤ))
    · refine ⟨-r, by rw [neg_mul_neg, hr], ?_⟩
      rwa [show -r - 1 = -(r + 1) by ring, Valuation.map_neg]
    exfalso
    push_cast at hm hp hprod
    have := (exp_neg_two_mul_le_mul_of_lt (not_le.mp hm) (not_le.mp hp)).trans hprod
    rw [WithZero.exp_le_exp] at this
    omega
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hs
    exact x.ne_zero hs.symm
  have hsv : w s = 1 := by
    have hlt1 : w (s - 1) < 1 :=
      hs1.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    simpa using Valuation.map_one_add_of_lt w hlt1
  refine ⟨Units.mk0 s hs0, ⟨hsv, hs1⟩, ?_⟩
  ext
  simp [pow_two, hs]

end GlobalTheory.QNorm
end

