import Mathlib
import Formalism.PeriodIntegrals.Bundle0011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryConjugation.TransferStep

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryConjugation.ConjTransposeOf
section
noncomputable section

namespace PI.UConjT

theorem conjTranspose_of (h1 : OnbReal) (h2 : TransferStep) (h3 : BlockStep) :
    PI.UMultOne.ConjTranspose := h3 (h2 h1)

end PI.UConjT
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryConjugation.ExistsUnitReal
section
noncomputable section

namespace PI.UConjT

open ComplexConjugate

theorem exists_unit_real {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (w e : E) (hw : w ≠ 0) :
    ∃ c : ℂ, ‖c • w‖ = 1 ∧ (inner ℂ (c • w) e).im = 0 := by
  set z : ℂ := inner ℂ w e with hzdef
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  by_cases hz : z = 0
  · refine ⟨((‖w‖⁻¹ : ℝ) : ℂ), ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      field_simp
    · rw [inner_smul_left, ← hzdef, hz]; simp
  · have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    refine ⟨z * ((‖z‖⁻¹ * ‖w‖⁻¹ : ℝ) : ℂ), ?_, ?_⟩
    · rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      field_simp
    · rw [inner_smul_left, ← hzdef]
      simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, map_mul]
      ring

theorem onbReal : OnbReal := by
  intro m
  induction m with
  | zero =>
    intro E _ _ _ _ T _ e
    exact ⟨fun i => i.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0,
      fun i => i.elim0⟩
  | succ m ih =>
    intro E _ _ _ hm T hT e
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hm
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hw0 : w ≠ 0 := hw.2
    obtain ⟨c, hc1, hcre⟩ := exists_unit_real w e hw0
    set v : E := c • w with hv
    have hv0 : v ≠ 0 := by
      intro h
      rw [h, norm_zero] at hc1
      exact zero_ne_one hc1
    have hTv : T v = μ • v := by
      rw [hv, map_smul, hw.apply_eq_smul, smul_comm c μ w]
    have hvv : inner ℂ v v = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hc1]; simp
    have hμ0 : μ ≠ 0 := by
      intro h0
      have h1 := hT v v
      rw [hTv, h0, zero_smul, inner_zero_left, hvv] at h1
      exact zero_ne_one h1
    set K : Submodule ℂ E := (ℂ ∙ v)ᗮ with hK
    have : Fact (Module.finrank ℂ E = m + 1) := ⟨hm⟩
    have hKdim : Module.finrank ℂ K = m := Submodule.finrank_orthogonal_span_singleton hv0
    have hTK : ∀ x ∈ K, T x ∈ K := by
      intro x hx
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hx ⊢
      have h1 := hT v x
      rw [hTv, inner_smul_left, hx] at h1
      exact (mul_eq_zero.mp h1).resolve_left (by simpa using hμ0)
    let T' : K →ₗ[ℂ] K := T.restrict hTK
    have hT' : ∀ x y : K, inner ℂ (T' x) (T' y) = inner ℂ x y := by
      intro x y
      simp only [Submodule.coe_inner, T', LinearMap.coe_restrict_apply]
      exact hT x y
    set a : ℂ := inner ℂ v e with ha
    have he'K : e - a • v ∈ K := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
        hvv, mul_one, ha, sub_self]
    obtain ⟨b', hb'o, hb'e, hb'r⟩ := ih K hKdim T' hT' ⟨e - a • v, he'K⟩
    have hperp : ∀ i, inner ℂ (b' i : E) v = 0 := fun i =>
      (Submodule.mem_orthogonal_singleton_iff_inner_left).mp (b' i).2
    have hperp' : ∀ i, inner ℂ v (b' i : E) = 0 := fun i =>
      (Submodule.mem_orthogonal_singleton_iff_inner_right).mp (b' i).2
    refine ⟨(Fin.cons v (fun i => (b' i : E)) : Fin (m + 1) → E), ?_, ?_, ?_⟩
    · rw [orthonormal_iff_ite] at hb'o ⊢
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp [hc1]
      · simp only [Fin.cons_zero, Fin.cons_succ, hperp']
        simp [(Fin.succ_ne_zero j).symm]
      · simp only [Fin.cons_zero, Fin.cons_succ, hperp]
        simp [Fin.succ_ne_zero i]
      · simp only [Fin.cons_succ, Fin.succ_inj]
        rw [← Submodule.coe_inner]
        exact hb'o i j
    · intro i
      refine Fin.cases ⟨μ, by simpa using hTv⟩ (fun i => ?_) i
      obtain ⟨d, hd⟩ := hb'e i
      refine ⟨d, ?_⟩
      have h2 := congrArg Subtype.val hd
      simpa [T', LinearMap.coe_restrict_apply] using h2
    · intro i
      refine Fin.cases (by simpa using hcre) (fun i => ?_) i
      simp only [Fin.cons_succ]
      have hi := hb'r i
      rw [Submodule.coe_inner] at hi
      have h3 : inner ℂ (b' i : E) e = inner ℂ (b' i : E) (e - a • v) := by
        rw [inner_sub_right, inner_smul_right, hperp i, mul_zero, sub_zero]
      rw [h3]
      exact hi

end PI.UConjT
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryConjugation.SubmatrixMemUnitaryGroup
section
noncomputable section

namespace PI.UConjT

open Matrix

lemma star_eq_self_of_im_eq_zero {z : ℂ} (h : z.im = 0) : star z = z :=
  Complex.conj_eq_iff_im.mpr h

lemma blk_castSucc_castSucc (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    PI.UMultOne.blk n h (Fin.castSucc a) (Fin.castSucc b) = h a b := by
  simp [PI.UMultOne.blk, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc]

lemma blk_castSucc_last (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) :
    PI.UMultOne.blk n h (Fin.castSucc a) (Fin.last n) = 0 := by
  simp [PI.UMultOne.blk, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc,
    finSumFinEquiv_symm_last]

lemma blk_last_castSucc (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) (b : Fin n) :
    PI.UMultOne.blk n h (Fin.last n) (Fin.castSucc b) = 0 := by
  simp [PI.UMultOne.blk, Matrix.reindex_apply, finSumFinEquiv_symm_apply_castSucc,
    finSumFinEquiv_symm_last]

lemma blk_last_last (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) :
    PI.UMultOne.blk n h (Fin.last n) (Fin.last n) = 1 := by
  simp [PI.UMultOne.blk, Matrix.reindex_apply, finSumFinEquiv_symm_last]

lemma eq_blk_of_last {n : ℕ} (k : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hcol : ∀ i, k (Fin.castSucc i) (Fin.last n) = 0)
    (hrow : ∀ j, k (Fin.last n) (Fin.castSucc j) = 0) (hll : k (Fin.last n) (Fin.last n) = 1) :
    PI.UMultOne.blk n (k.submatrix Fin.castSucc Fin.castSucc) = k := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [blk_last_last, hll]
    | cast b => rw [blk_last_castSucc, hrow]
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [blk_castSucc_last, hcol]
    | cast b => rw [blk_castSucc_castSucc, submatrix_apply]

lemma submatrix_mem_unitaryGroup {n : ℕ} (k : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hk : k ∈ unitaryGroup (Fin (n + 1)) ℂ) (hcol : ∀ i, k (Fin.castSucc i) (Fin.last n) = 0) :
    k.submatrix Fin.castSucc Fin.castSucc ∈ unitaryGroup (Fin n) ℂ := by
  rw [mem_unitaryGroup_iff] at hk ⊢
  ext a b
  have hab := congrFun (congrFun hk (Fin.castSucc a)) (Fin.castSucc b)
  rw [mul_apply, Fin.sum_univ_castSucc] at hab
  simp only [star_eq_conjTranspose, conjTranspose_apply, hcol, zero_mul, add_zero,
    one_apply, Fin.castSucc_inj] at hab
  simpa [mul_apply, conjTranspose_apply, one_apply] using hab

theorem blockStep : BlockStep := by
  intro hS n g hg
  obtain ⟨u, hu, d, hgu, hreal⟩ := hS n g hg
  have hu1 : u * uᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.mp hu
  have hu2 : uᴴ * u = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.mp hu
  have hgeq : g = u * diagonal d * uᴴ := by
    rw [← hgu, Matrix.mul_assoc, hu1, Matrix.mul_one]
  set k : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := (uᴴ)ᵀ * uᴴ with hkdef
  have hkH : kᴴ = u * uᵀ := by
    rw [hkdef, conjTranspose_mul, conjTranspose_conjTranspose]
    congr 1
    ext i j
    simp [conjTranspose_apply]
  have hkk : k * kᴴ = 1 := by
    rw [hkH, hkdef, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, hu2, Matrix.one_mul,
      ← transpose_mul, hu1, transpose_one]
  have hkU : k ∈ unitaryGroup (Fin (n + 1)) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose]; exact hkk
  have hconj : k * g * kᴴ = gᵀ := by
    rw [hkH, hgeq, hkdef, transpose_mul, transpose_mul, diagonal_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc uᴴ u, hu2, Matrix.one_mul, ← Matrix.mul_assoc uᴴ u, hu2,
      Matrix.one_mul]

  have hkent : ∀ i j, k i j = ∑ l, star (u i l) * star (u j l) := by
    intro i j; simp [hkdef, mul_apply, conjTranspose_apply]
  have hu1e : ∀ i j, ∑ l, u i l * star (u j l) = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hu1 i) j
    simpa [mul_apply, conjTranspose_apply, one_apply] using this
  have hcol : ∀ i, k i (Fin.last n) = if i = Fin.last n then 1 else 0 := by
    intro i
    rw [hkent]
    have : ∑ l, star (u i l) * star (u (Fin.last n) l) = star (∑ l, u i l * star (u (Fin.last n) l)) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [star_mul', star_star, star_eq_self_of_im_eq_zero (hreal l)]
    rw [this, hu1e]
    split_ifs <;> simp
  have hrow : ∀ j, k (Fin.last n) j = if Fin.last n = j then 1 else 0 := by
    intro j
    rw [hkent, ← hu1e]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [star_eq_self_of_im_eq_zero (hreal l)]
  have hcol' : ∀ i : Fin n, k (Fin.castSucc i) (Fin.last n) = 0 := by
    intro i; rw [hcol]; simp [Fin.castSucc_ne_last]
  have hrow' : ∀ j : Fin n, k (Fin.last n) (Fin.castSucc j) = 0 := by
    intro j; rw [hrow]; simp [(Fin.castSucc_ne_last j).symm]
  have hll : k (Fin.last n) (Fin.last n) = 1 := by rw [hcol]; simp
  refine ⟨k.submatrix Fin.castSucc Fin.castSucc, submatrix_mem_unitaryGroup k hkU hcol', ?_⟩
  rw [eq_blk_of_last k hcol' hrow' hll]
  exact hconj

end PI.UConjT
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryConjugation.Transfer
section
noncomputable section

namespace PI.UConjT

open Matrix

lemma inner_toEuclideanLin_unitary {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (hg : gᴴ * g = 1)
    (x y : EuclideanSpace ℂ (Fin m)) :
    inner ℂ (Matrix.toEuclideanLin g x) (Matrix.toEuclideanLin g y) = inner ℂ x y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  rw [star_mulVec, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec, hg, one_mulVec,
    dotProduct_comm]

theorem transferStep : TransferStep := by
  intro hO n g hg
  have hg2 : gᴴ * g = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.mp hg
  obtain ⟨b, hbo, hbe, hbr⟩ := hO (n + 1) (EuclideanSpace ℂ (Fin (n + 1)))
    finrank_euclideanSpace_fin (Matrix.toEuclideanLin g) (inner_toEuclideanLin_unitary g hg2)
    (EuclideanSpace.single (Fin.last n) 1)
  choose d hd using hbe
  refine ⟨Matrix.of fun i j => b j i, ?_, d, ?_, ?_⟩
  · rw [mem_unitaryGroup_iff']
    ext i j
    have h1 := orthonormal_iff_ite.mp hbo i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h1
    simp only [star_eq_conjTranspose, mul_apply, conjTranspose_apply, of_apply, one_apply]
    rw [← h1]
    simp [dotProduct, mul_comm]
  · ext i j
    have h1 := congrArg (fun v : EuclideanSpace ℂ (Fin (n + 1)) => v i) (hd j)
    simp only [Matrix.toLpLin_apply, PiLp.smul_apply, smul_eq_mul] at h1
    rw [mul_diagonal, mul_apply]
    simp only [of_apply]
    simpa [mulVec, dotProduct, mul_comm] using h1
  · intro i
    have h1 := hbr i
    rw [EuclideanSpace.inner_single_right] at h1
    simpa using h1

end PI.UConjT
end
end

