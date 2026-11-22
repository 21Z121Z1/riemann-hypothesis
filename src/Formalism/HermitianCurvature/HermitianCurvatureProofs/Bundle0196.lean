import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0189

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymExp
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

lemma expS_summable {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Summable (fun m : ℕ => ((m.factorial : ℂ))⁻¹ • X ^ m) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.expSeries_summable' X

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def mvL {n : ℕ} (y : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ y
      map_add' := fun M N => Matrix.add_mulVec M N y
      map_smul' := fun c M => Matrix.smul_mulVec c M y }

lemma mvL_apply {n : ℕ} (y : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : mvL y M = M *ᵥ y := rfl

lemma exp_mulVec_sq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) (h : X *ᵥ (X *ᵥ y) = 0) :
    NormedSpace.exp X *ᵥ y = y + X *ᵥ y := by
  have hs := expS_summable X
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  show (∑' m : ℕ, ((m.factorial : ℂ))⁻¹ • X ^ m) *ᵥ y = y + X *ᵥ y
  rw [← mvL_apply y, ContinuousLinearMap.map_tsum (mvL y) hs]
  rw [tsum_eq_sum (s := Finset.range 2) ?_]
  · simp [Finset.sum_range_succ, mvL_apply, Matrix.smul_mulVec]
  · intro m hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [mvL_apply, Matrix.smul_mulVec]
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    rw [pow_add, ← Matrix.mulVec_mulVec, pow_two, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero, smul_zero]

lemma exp_smul_mulVec_sq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) (h : X *ᵥ (X *ᵥ y) = 0)
    (c : ℂ) : NormedSpace.exp (c • X) *ᵥ y = y + c • (X *ᵥ y) := by
  have h' : (c • X) *ᵥ ((c • X) *ᵥ y) = 0 := by
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, h, smul_zero, smul_zero]
  rw [exp_mulVec_sq (c • X) y h', Matrix.smul_mulVec]

lemma exp_smul_mulVec_fix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) (h : X *ᵥ y = 0)
    (c : ℂ) : NormedSpace.exp (c • X) *ᵥ y = y := by
  have h2 : X *ᵥ (X *ᵥ y) = 0 := by rw [h, Matrix.mulVec_zero]
  rw [exp_smul_mulVec_sq X y h2 c, h, smul_zero, add_zero]

variable {k r : ℕ}

lemma hpk_star (i j : Fin (2 * r + k + 1)) : star (Hpk k r i j) = Hpk k r i j := by
  unfold Hpk
  split_ifs <;> simp

lemma hpk_symm (i j : Fin (2 * r + k + 1)) : Hpk k r i j = Hpk k r j i := by
  by_cases hij : i = j
  · subst hij
    rfl
  · have hji : ¬ j = i := fun h => hij h.symm
    unfold Hpk
    simp only [hij, hji, and_false, if_false]
    split_ifs <;> first | rfl | (exfalso; omega)

lemma herm_conj (y w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) y w = star (herm (Hpk k r) w y) := by
  simp only [herm, dotProduct, mulVec, star_sum, star_mul', star_star, Pi.star_apply, hpk_star,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hpk_symm j i]
  ring

lemma vmv_mulVec {n : ℕ} (u w y : Fin n → ℂ) : vecMulVec u w *ᵥ y = (w ⬝ᵥ y) • u := by
  ext i
  simp only [vecMulVec, mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma star_hpk_dot (v y : Fin (2 * r + k + 1) → ℂ) : star (Hpk k r *ᵥ v) ⬝ᵥ y = herm (Hpk k r) y v := by
  simp only [herm, dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, hpk_star, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hpk_symm j i]
  ring

theorem xuv_mulVec (u v y : Fin (2 * r + k + 1) → ℂ) :
    Xuv k r u v *ᵥ y = herm (Hpk k r) y v • u - herm (Hpk k r) y u • v := by
  unfold Xuv
  rw [Matrix.sub_mulVec, vmv_mulVec, vmv_mulVec, star_hpk_dot, star_hpk_dot]

theorem xuv_inLie (u v : Fin (2 * r + k + 1) → ℂ) : B.inLie k r (Xuv k r u v) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have e1 : star (Hpk k r *ᵥ u) = star u ᵥ* Hpk k r := by rw [Matrix.star_mulVec, hH]
  have e2 : star (Hpk k r *ᵥ v) = star v ᵥ* Hpk k r := by rw [Matrix.star_mulVec, hH]
  unfold B.inLie Xuv
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_vecMulVec, Matrix.conjTranspose_vecMulVec,
    star_star, star_star, Matrix.sub_mul, Matrix.mul_sub, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, e1, e2]
  abel

lemma mat_eq_mulVec_bvec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : M i j = (M *ᵥ bvec j) i := by
  simp [bvec, Matrix.mulVec_single]

lemma herm_bvec_left (p : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec p) w = ∑ i, star (w i) * Hpk k r i p := by
  simp [herm, bvec, dotProduct, Matrix.mulVec_single]

lemma herm_bvec_bvec (p q : Fin (2 * r + k + 1)) : herm (Hpk k r) (bvec p) (bvec q) = Hpk k r q p := by
  rw [herm_bvec_left]
  simp [bvec, Pi.single_apply]

lemma hpk_col_eI (c : Fin r) (i : Fin (2 * r + k + 1)) :
    Hpk k r i (eI k r c) = if i = esI k r c then 1 else 0 := by
  have hc := c.isLt
  have hi := i.isLt
  unfold Hpk
  simp only [eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma hpk_col_esI (c : Fin r) (i : Fin (2 * r + k + 1)) :
    Hpk k r i (esI k r c) = if i = eI k r c then 1 else 0 := by
  have hc := c.isLt
  have hi := i.isLt
  unfold Hpk
  simp only [eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma herm_eI_left (c : Fin r) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec (eI k r c)) w = star (w (esI k r c)) := by
  rw [herm_bvec_left]
  simp [hpk_col_eI]

lemma herm_esI_left (c : Fin r) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec (esI k r c)) w = star (w (eI k r c)) := by
  rw [herm_bvec_left]
  simp [hpk_col_esI]

lemma hpk_eI_row_block (a : Fin r) (j : Fin (2 * r + k + 1)) (hj : r ≤ j.val) (hj' : j.val ≤ r + k) :
    Hpk k r (eI k r a) j = 0 := by
  have ha := a.isLt
  unfold Hpk
  simp only [eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma hpk_eI_eI (a c : Fin r) : Hpk k r (eI k r a) (eI k r c) = 0 := by
  have ha := a.isLt
  have hc := c.isLt
  unfold Hpk
  simp only [eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma one_mem_UWset (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by
  refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem xuv_lieN (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ b : Fin r, b.val ≤ a.val → v (esI k r b) = 0) :
    Xuv k r (bvec (eI k r a)) v ∈ lieOf (Sset k r z) := by
  intro t
  set X := Xuv k r (bvec (eI k r a)) v with hX
  have hXa : X *ᵥ bvec (eI k r a) = 0 := by
    rw [hX, xuv_mulVec, herm_eI_left, hv a le_rfl, herm_bvec_bvec, hpk_eI_eI]
    simp
  have hXc : ∀ c : Fin r, X *ᵥ bvec (eI k r c) = star (v (esI k r c)) • bvec (eI k r a) := by
    intro c
    rw [hX, xuv_mulVec, herm_eI_left, herm_bvec_bvec, hpk_eI_eI]
    simp
  have hXj : ∀ j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k →
      X *ᵥ bvec j = herm (Hpk k r) (bvec j) v • bvec (eI k r a) := by
    intro j hj hj'
    rw [hX, xuv_mulVec, herm_bvec_bvec, hpk_eI_row_block a j hj hj']
    simp
  refine ⟨1, one_mem_UWset z, NormedSpace.exp ((t : ℂ) • X), ⟨Formalism.FourierDecayAlt.P.B5.exp_mem (xuv_inLie _ _) t, ?_, ?_⟩,
    (Matrix.one_mul _).symm⟩
  · intro c i hci
    have e := exp_smul_mulVec_sq X (bvec (eI k r c)) (by rw [hXc, Matrix.mulVec_smul, hXa, smul_zero]) (t : ℂ)
    rw [show NormedSpace.exp ((t : ℂ) • X) i (eI k r c) = (NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec (eI k r c)) i
      from mat_eq_mulVec_bvec _ _ _, e, hXc]
    have hz : star (v (esI k r c)) * bvec (eI k r a) i = 0 := by
      by_cases hca : c.val ≤ a.val
      · rw [hv c hca]; simp
      · have : i ≠ eI k r a := by
          intro h; rw [h] at hci; simp only [eI] at hci; omega
        simp [bvec, Pi.single_apply, this]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz, mul_zero, add_zero]
    simp [bvec, Pi.single_apply]
  · intro i j hj hj' hi
    have e := exp_smul_mulVec_sq X (bvec j) (by rw [hXj j hj hj', Matrix.mulVec_smul, hXa, smul_zero]) (t : ℂ)
    rw [show NormedSpace.exp ((t : ℂ) • X) i j = (NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec j) i
      from mat_eq_mulVec_bvec _ _ _, e, hXj j hj hj']
    have : i ≠ eI k r a := by
      intro h; rw [h] at hi; simp only [eI] at hi; omega
    simp [bvec, Pi.single_apply, this]

theorem xuv_lieW (z u v : Fin (2 * r + k + 1) → ℂ) (hu : inWb k r u) (hv : inWb k r v)
    (huz : herm (Hpk k r) u z = 0) (hvz : herm (Hpk k r) v z = 0) :
    Xuv k r u v ∈ lieOf (UWset k r z) := by
  intro t
  set X := Xuv k r u v with hX
  have hes : ∀ (w : Fin (2 * r + k + 1) → ℂ), inWb k r w → ∀ c : Fin r, w (esI k r c) = 0 := by
    intro w hw c; exact hw _ (Or.inr (by simp only [esI]; omega))
  have hei : ∀ (w : Fin (2 * r + k + 1) → ℂ), inWb k r w → ∀ c : Fin r, w (eI k r c) = 0 := by
    intro w hw c; exact hw _ (Or.inl (by simp only [eI]; omega))
  refine ⟨Formalism.FourierDecayAlt.P.B5.exp_mem (xuv_inLie _ _) t, fun c => ⟨?_, ?_⟩, ?_⟩
  · refine exp_smul_mulVec_fix X _ ?_ _
    rw [hX, xuv_mulVec, herm_eI_left, herm_eI_left, hes v hv, hes u hu]; simp
  · refine exp_smul_mulVec_fix X _ ?_ _
    rw [hX, xuv_mulVec, herm_esI_left, herm_esI_left, hei v hv, hei u hu]; simp
  · refine exp_smul_mulVec_fix X _ ?_ _
    rw [hX, xuv_mulVec, herm_conj z v, herm_conj z u, hvz, huz]; simp

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermZeroRight
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem hpk_mulVec (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ x) i = if i.val < r ∨ r + k < i.val then x ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -x i else x i := by
  rw [mulVec, dotProduct]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · have : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1 := by
        unfold Hpk
        rcases h with h | h
        · rw [if_pos ⟨h, by simp; omega⟩]
        · rw [if_neg (by simp; omega), if_pos ⟨by simp; omega, by simp; omega⟩]
      rw [this, one_mul]
    · intro j _ hj
      have : Hpk k r i j = 0 := by
        unfold Hpk
        have hj' : j.val ≠ 2 * r + k - i.val := fun e => hj (Fin.ext (by simpa using e))
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [this, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · rw [if_neg h, Finset.sum_eq_single i]
    · unfold Hpk
      rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩]
      split_ifs <;> ring
    · intro j _ hj
      have : Hpk k r i j = 0 := by
        unfold Hpk
        rw [if_neg (by omega), if_neg (by omega), if_neg (fun e => hj e.2.2.symm)]
      rw [this, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'

theorem hpk_symm' : (Hpk k r)ᵀ = Hpk k r := by
  ext i j
  simp only [transpose_apply, Hpk]
  by_cases h1 : j.val < r ∧ j.val + i.val = 2 * r + k
  · rw [if_pos h1]
    by_cases h2 : i.val < r ∧ i.val + j.val = 2 * r + k
    · rw [if_pos h2]
    · rw [if_neg h2, if_pos ⟨h1.1, by omega⟩]
  · rw [if_neg h1]
    by_cases h2 : i.val < r ∧ j.val + i.val = 2 * r + k
    · rw [if_pos h2, if_pos ⟨h2.1, by omega⟩]
    · rw [if_neg h2]
      by_cases h3 : i.val < r ∧ i.val + j.val = 2 * r + k
      · exact absurd ⟨h3.1, by omega⟩ h2
      · by_cases h4 : j.val < r ∧ i.val + j.val = 2 * r + k
        · exact absurd ⟨h4.1, by omega⟩ h1
        · rw [if_neg h3, if_neg h4]
          by_cases h5 : i = j
          · subst h5; rfl
          · rw [if_neg (fun e => h5 e.2.2.symm), if_neg (fun e => h5 e.2.2)]

theorem hpk_conjT : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, ← transpose_apply (Hpk k r) j i, hpk_symm']
  unfold Hpk
  split_ifs <;> simp

theorem herm_eq (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = ∑ i, star (y i) * (Hpk k r *ᵥ x) i := rfl

theorem herm_add_left (x x' y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (x + x') y = herm (Hpk k r) x y + herm (Hpk k r) x' y := by
  simp only [herm, mulVec_add, dotProduct_add]

theorem herm_smul_left (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (c • x) y = c * herm (Hpk k r) x y := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_sub_left (x x' y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (x - x') y = herm (Hpk k r) x y - herm (Hpk k r) x' y := by
  simp only [herm, mulVec_sub, dotProduct_sub]

theorem herm_add_right (x y y' : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (y + y') = herm (Hpk k r) x y + herm (Hpk k r) x y' := by
  simp only [herm, star_add, add_dotProduct]

theorem herm_smul_right (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (c • y) = star c * herm (Hpk k r) x y := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

theorem herm_zero_left (y : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) 0 y = 0 := by
  simp [herm]

theorem herm_zero_right (x : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) x 0 = 0 := by
  simp [herm]

theorem herm_swap (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = star (herm (Hpk k r) y x) := by
  simp only [herm]
  rw [star_dotProduct, star_mulVec, hpk_conjT, dotProduct_mulVec]

theorem herm_skew {ξ : B.Mat k r} (hξ : B.inLie k r ξ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (ξ *ᵥ x) y = -herm (Hpk k r) x (ξ *ᵥ y) := by
  have h : ξᴴ * Hpk k r = -(Hpk k r * ξ) := eq_neg_of_add_eq_zero_left hξ
  simp only [herm]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h, neg_mulVec, dotProduct_neg, neg_neg]

theorem trace_xuv (ξ : B.Mat k r) (u v : Fin (2 * r + k + 1) → ℂ) :
    Matrix.trace (ξ * Xuv k r u v) = herm (Hpk k r) (ξ *ᵥ u) v - herm (Hpk k r) (ξ *ᵥ v) u := by
  have key : ∀ a b : Fin (2 * r + k + 1) → ℂ,
      Matrix.trace (ξ * vecMulVec a (star (Hpk k r *ᵥ b))) = herm (Hpk k r) (ξ *ᵥ a) b := by
    intro a b
    have hb : star (Hpk k r *ᵥ b) = star b ᵥ* Hpk k r := by
      rw [star_mulVec, hpk_conjT]
    rw [hb, herm, dotProduct_mulVec]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [Xuv, Matrix.mul_sub, Matrix.trace_sub, key, key]

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentRankOne
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem asm_contOn_of_ckOn {r : ℕ} {m : ℕ∞} {F : B.Mat k r → E} (hF : B.CkOn m (B.GV k r) F) :
    ContinuousOn F (B.GV k r) := by
  intro g₀ hg₀
  obtain ⟨W0, F', hU, hgU, hF', hag⟩ := hF g₀ hg₀
  have hc : ContinuousAt F' g₀ := (hF'.continuousOn).continuousAt (hU.mem_nhds hgU)
  refine (hc.continuousWithinAt (s := B.GV k r)).congr_of_eventuallyEq ?_ (hag g₀ hgU hg₀)
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g hgU' hgG
  exact hag g hgU' hgG

theorem asm_star_cpt (j ρ : ℕ) (F : B.Mat k (j + ρ) → E) (hFc : B.CkOn ⊤ (B.GV k (j + ρ)) F)
    (R : ℝ) (hR : ∀ g ∈ B.GV k (j + ρ), F g ≠ 0 → B.gN g ≤ R) (χD : ℂ → ℂ) (hχ : U.IsCutC χD) (A₁ : ℝ)
    (hA₁ : 0 ≤ A₁) :
    ∃ B₁, U.Star k j ρ (fun g => χD (U.DjU k j ρ g) • F g) A₁ 0 B₁ ((fun w : ℂ => ‖w‖) '' tsupport χD) := by
  have hχc : Continuous χD := hχ.1.continuous
  have hDc := Formalism.FourierDecayAlt.P.JCTx6.Pos.cont_DjU k j ρ
  obtain ⟨Cχ, hCχ⟩ := hχc.bounded_above_of_compact_support hχ.2.1
  have hKc : IsCompact (B.GV k (j + ρ) ∩ {g : B.Mat k (j + ρ) | B.gN g ≤ R}) :=
    (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k (j + ρ) R).inter_left (Formalism.FourierDecayAlt.P.unitary_group_closed k (j + ρ)).closed
  obtain ⟨CF, hCF⟩ := hKc.exists_bound_of_continuousOn ((asm_contOn_of_ckOn hFc).mono Set.inter_subset_left)
  refine ⟨(max R 0) ^ A₁ * (max Cχ 0 * max CF 0), ⟨?_, ?_, ?_⟩⟩
  · intro g₀ hg₀
    obtain ⟨W0, F', hU, hgU, hF', hag⟩ := hFc g₀ hg₀
    refine ⟨W0, fun g => χD (U.DjU k j ρ g) • F' g, hU, hgU, ?_, fun g hg hgG => by simp only [hag g hg hgG]⟩
    exact contDiffOn_zero.2 ((hχc.comp hDc).continuousOn.smul (hF'.continuousOn))
  · intro g _ hne
    refine ⟨U.DjU k j ρ g, subset_tsupport _ (fun h0 => hne ?_), rfl⟩
    simp only [h0, zero_smul]
  · intro u v hu hv hl g hg
    have hu0 : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hv0 : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu0 hv0
    show B.gN g ^ A₁ * ‖χD (U.DjU k j ρ g) • F g‖ ≤ _
    by_cases h0 : F g = 0
    · rw [h0, smul_zero, norm_zero, mul_zero]
      exact mul_nonneg (Real.rpow_nonneg (le_max_right _ _) _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
    · have hgR := hR g hg h0
      have hg0 : 0 ≤ B.gN g := Real.sqrt_nonneg _
      refine mul_le_mul (Real.rpow_le_rpow hg0 (hgR.trans (le_max_left _ _)) hA₁) ?_ (norm_nonneg _)
        (Real.rpow_nonneg (le_max_right _ _) _)
      rw [norm_smul]
      exact mul_le_mul ((hCχ _).trans (le_max_left _ _)) ((hCF g ⟨hg, hgR⟩).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)

theorem asm_gInt_int (ph ρ : ℕ) (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t : ℂ) (hd : ∀ i, d i ≠ 0) (ht : t ≠ 0)
    (z z' : Fin (2 * (ph + (0 + 1) + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + (0 + 1) + ρ) → E)
    (hFc : B.CkOn ⊤ (B.GV k (ph + (0 + 1) + ρ)) F) (R : ℝ)
    (hR : ∀ g ∈ B.GV k (ph + (0 + 1) + ρ), F g ≠ 0 → B.gN g ≤ R) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ) :
    Integrable (Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' F γ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ) := by
  have hw : (G.wMat (0 + 1)).det ≠ 0 := Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero (0 + 1)
  set c₀ : ℂ := (U.hMat σ d).det * (t ^ (0 + 1) * (G.wMat (0 + 1)).det) with hc₀def
  have hc₀ : c₀ ≠ 0 := mul_ne_zero (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd) (mul_ne_zero (pow_ne_zero _ ht) hw)
  obtain ⟨χD, hχD, hχD1, hχDs⟩ := Formalism.FourierDecayAlt.P.JCTx6.Pos.bump_exists hc₀
  have hR0 : (0 : ℝ) ≤ ((ph + (0 + 1) + ρ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hA₁ : (0 : ℝ) ≤ 8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1) *
      (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) + 1) := by positivity
  obtain ⟨B₁, hStar⟩ := asm_star_cpt (ph + (0 + 1)) ρ F hFc R hR χD hχD _ hA₁
  have hK : IsCompact ((fun w : ℂ => ‖w‖) '' tsupport χD) := hχD.2.1.isCompact.image continuous_norm
  have hK0 : (fun w : ℂ => ‖w‖) '' tsupport χD ⊆ Set.Ioi 0 := by
    rintro _ ⟨w, hw', rfl⟩
    have := norm_pos_iff.mpr hc₀
    exact lt_of_lt_of_le (by positivity) (hχDs w hw').1
  have hthr : 2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) <
      8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1) *
        (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (0 + 1) + ρ) + k + 1 : ℕ) : ℝ) + 1) /
        (8 * (2 * ((ph + (0 + 1) + ρ : ℕ) : ℝ) + 1)) := by
    rw [mul_div_cancel_left₀ _ (by positivity)]
    linarith
  have h1 := Formalism.FourierDecayAlt.P.JCTx6.Int.intG k ph 0 ρ σ d t hd ht _ hK hK0 0 _ hthr z z' E _ B₁ hStar γ hγ
  have e : Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' F γ =
      Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d t z z' (fun g => χD (U.DjU k (ph + (0 + 1)) ρ g) • F g) γ := by
    funext y
    have hdet : G.detM (Matrix.of.symm (t • G.wMat (0 + 1) * G.upper y.2.2)) = t ^ (0 + 1) * (G.wMat (0 + 1)).det :=
      Formalism.FourierDecayAlt.P.JCTx6.Pos.detM_Zv 0 t y.2.2
    have hD : U.DjU k (ph + (0 + 1)) ρ (U.gaXi (p := ph) (s := 0 + 1) k ρ σ d (y.1, y.2.1)
        (Matrix.of.symm (t • G.wMat (0 + 1) * G.upper y.2.2)) γ) = c₀ := by
      rw [Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice, hdet]
    simp only [Formalism.FourierDecayAlt.P.JCTx6.gInt]
    rw [hD, hχD1 c₀ (by rw [dist_self]; positivity), one_smul]
  rw [e]; exact h1

theorem integrable_unipotent_rank_one (ph ρ : ℕ) (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (c : ℂ)
    (z z' : Fin (2 * (ph + 1 + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + 1 + ρ) → E) (γ : B.Mat k ρ)
    (h : Integrable (Formalism.FourierDecayAlt.P.JCTx6.gInt k ph 0 ρ σ d c z z' F γ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ)) :
    Integrable (fun ξ : U.Xi k ph 1 ρ σ => U.psiStar k ρ σ z z' ξ • F (U.gaXi k ρ σ d ξ (fun _ _ => c) γ))
      (U.muXi k ph 1 ρ σ) := by
  have hE : IsEmpty (G.UT (0 + 1)) := ⟨fun q => by have h := q.2; rw [Fin.lt_def] at h; omega⟩
  let v₀ : G.UT (0 + 1) → ℂ := fun q => isEmptyElim q
  have hvol : (volume : Measure (G.UT (0 + 1) → ℂ)) = Measure.dirac v₀ := by
    rw [volume_pi]; exact Measure.pi_of_empty _ _
  have a1 : SigmaFinite (volume : Measure (Fin (0 + 1) → Fin ph → ℂ)) := inferInstance
  have a2 : SigmaFinite (volume : Measure (Fin ph → Fin (0 + 1) → ℂ)) := inferInstance
  have a3 : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  have a4 : SigmaFinite (volume : Measure (G.UT ph → ℂ)) := inferInstance
  have b1 : SigmaFinite (volume : Measure ((Fin (0 + 1) → Fin ph → ℂ) × (Fin ph → Fin (0 + 1) → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have b2 : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT ph → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have b3 : SigmaFinite (volume : Measure (U.XiH ph (0 + 1) σ)) := by
    haveI := b1; haveI := b2
    rw [Measure.volume_eq_prod]; infer_instance
  have b4 : SigmaFinite (U.muXiH ph (0 + 1) σ) := by unfold U.muXiH; exact b3
  have hg : MeasurePreserving (fun b : U.XiH ph (0 + 1) σ => (b, v₀)) volume
      ((volume : Measure (U.XiH ph (0 + 1) σ)).prod (volume : Measure (G.UT (0 + 1) → ℂ))) := by
    rw [hvol]
    exact ⟨measurable_id.prodMk measurable_const, (Measure.prod_dirac _).symm⟩
  have := Formalism.FourierDecayAlt.P.Dx2.SL.sigma_RC k (ph + (0 + 1)) ρ
  have hφ : MeasurePreserving (Prod.map (id : U.RC k (ph + (0 + 1)) ρ × U.RC k (ph + (0 + 1)) ρ → _)
      (fun b : U.XiH ph (0 + 1) σ => (b, v₀))) (U.muXi k ph 1 ρ σ) (Formalism.FourierDecayAlt.P.JCTx6.muG k ph 0 ρ σ) :=
    (MeasurePreserving.id _).prod hg
  have h2 := (hφ.integrable_comp h.aestronglyMeasurable).2 h
  refine h2.congr (ae_of_all _ fun ξ => ?_)
  have hs : G.superSum (G.upper v₀) = 0 := by simp [G.superSum]
  have hZ : (Matrix.of.symm (c • G.wMat (0 + 1) * G.upper v₀) : G.Mat (0 + 1)) = fun _ _ => c := by
    funext i j
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp)
    have hj : j = 0 := Fin.ext (by have := j.isLt; simp)
    subst hi hj
    simp [G.wMat, G.upper, G.strictUpper, Matrix.mul_apply]
  simp only [Function.comp_apply, Prod.map, id, Formalism.FourierDecayAlt.P.JCTx6.gInt, hs, hZ]
  simp [G.psi]

end Formalism.FourierDecayAlt.P.PBH
end
end

