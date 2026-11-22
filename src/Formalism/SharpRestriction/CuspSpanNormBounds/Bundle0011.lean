import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CuspidalRangeOfReproUnipotent
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0010

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BridgeUnipRad
section
noncomputable section

namespace Formalism.MainNotions.BridgeUnipRad

open MeasureTheory NumberField Matrix
open Formalism.MainNotions.S

section CM

variable (I : AutInst)

theorem emb_star (v : InfinitePlace I.F) (x : I.E) : I.φ v (star x) = starRingEnd ℂ (I.φ v x) := by
  obtain ⟨hcm, -, -, -⟩ := I.cm
  unfold Formalism.HermitianLatticesTheory.IsCMUnram at hcm
  exact hcm.2.1 (I.φ v) x

end CM

section Form

variable {n : ℕ}

theorem hform_eq (J : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  rw [Formalism.UG.hform.eq_1]
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

end Form

section Span

variable (I : AutInst)

def WC (v : InfinitePlace I.F) (W : Submodule I.E (Fin I.n → I.E)) : Submodule ℂ (Fin I.n → ℂ) :=
  Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set (Fin I.n → I.E)))

end Span

section Rad

variable {n : ℕ}

def UPerp (J' : Matrix (Fin n) (Fin n) ℂ) (U : Submodule ℂ (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {y | ∀ x ∈ U, Formalism.UG.hform (starRingEnd ℂ) J' x y = 0}

def URad (J' : Matrix (Fin n) (Fin n) ℂ) (U : Submodule ℂ (Fin n → ℂ)) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ x ∈ U, (g - 1) *ᵥ x = 0) ∧ (∀ y ∈ UPerp J' U, (g - 1) *ᵥ y ∈ U) ∧ ∀ y, (g - 1) *ᵥ y ∈ UPerp J' U

variable {J' : Matrix (Fin n) (Fin n) ℂ} {U : Submodule ℂ (Fin n → ℂ)}

theorem uperp_add {y y' : Fin n → ℂ} (hy : y ∈ UPerp J' U) (hy' : y' ∈ UPerp J' U) : y + y' ∈ UPerp J' U := by
  simp only [UPerp, Set.mem_setOf_eq] at hy hy' ⊢
  intro x hx
  have h1 := hy x hx
  have h2 := hy' x hx
  rw [hform_eq] at h1 h2 ⊢
  rw [mulVec_add, dotProduct_add, h1, h2, add_zero]

theorem uperp_neg {y : Fin n → ℂ} (hy : y ∈ UPerp J' U) : -y ∈ UPerp J' U := by
  simp only [UPerp, Set.mem_setOf_eq] at hy ⊢
  intro x hx
  have h1 := hy x hx
  rw [hform_eq] at h1 ⊢
  rw [mulVec_neg, dotProduct_neg, h1, neg_zero]

theorem uperp_zero : (0 : Fin n → ℂ) ∈ UPerp J' U := by
  simp only [UPerp, Set.mem_setOf_eq]
  intro x _
  rw [hform_eq, mulVec_zero, dotProduct_zero]

theorem urad_one : URad J' U 1 := by
  unfold URad
  refine ⟨fun x _ => by simp, fun y _ => by simp, fun y => ?_⟩
  simpa using (uperp_zero : (0 : Fin n → ℂ) ∈ UPerp J' U)

theorem urad_mul {A B : Matrix (Fin n) (Fin n) ℂ} (hA : URad J' U A) (hB : URad J' U B) : URad J' U (A * B) := by
  unfold URad at hA hB ⊢
  obtain ⟨a1, a2, a3⟩ := hA
  obtain ⟨b1, b2, b3⟩ := hB
  have key : ∀ v, (A * B - 1) *ᵥ v = (A - 1) *ᵥ v + (A - 1) *ᵥ ((B - 1) *ᵥ v) + (B - 1) *ᵥ v := by
    intro v
    simp only [sub_mulVec, one_mulVec, mulVec_sub, ← mulVec_mulVec]
    abel
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun y => ?_⟩
  · rw [key, a1 x hx, b1 x hx, mulVec_zero, add_zero, add_zero]
  · rw [key, a1 _ (b2 y hy), add_zero]
    exact U.add_mem (a2 y hy) (b2 y hy)
  · rw [key]
    exact uperp_add (uperp_add (a3 y) (a3 _)) (b3 y)

theorem urad_inv {A A' : Matrix (Fin n) (Fin n) ℂ} (hA : URad J' U A) (h1 : A' * A = 1) (h2 : A * A' = 1)
    (hu : ∀ a b, Formalism.UG.hform (starRingEnd ℂ) J' (A *ᵥ a) (A *ᵥ b) = Formalism.UG.hform (starRingEnd ℂ) J' a b) :
    URad J' U A' := by
  unfold URad at hA ⊢
  obtain ⟨a1, a2, a3⟩ := hA
  have key : ∀ v, (A' - 1) *ᵥ v = -(A' *ᵥ ((A - 1) *ᵥ v)) := by
    intro v
    simp only [sub_mulVec, one_mulVec, mulVec_sub, mulVec_mulVec, h1]
    abel
  have fixA : ∀ x ∈ U, A *ᵥ x = x := by
    intro x hx
    have := a1 x hx
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at this
    exact this
  have hA'A : ∀ z, A' *ᵥ (A *ᵥ z) = z := by
    intro z
    rw [mulVec_mulVec, h1, one_mulVec]
  have hAA' : ∀ z, A *ᵥ (A' *ᵥ z) = z := by
    intro z
    rw [mulVec_mulVec, h2, one_mulVec]
  have fixU : ∀ x ∈ U, A' *ᵥ x = x := by
    intro x hx
    conv_lhs => rw [← fixA x hx]
    exact hA'A x
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun y => ?_⟩
  · rw [sub_mulVec, one_mulVec, fixU x hx, sub_self]
  · rw [key, fixU _ (a2 y hy)]
    exact U.neg_mem (a2 y hy)
  · rw [key]
    apply uperp_neg
    have hz := a3 y
    simp only [UPerp, Set.mem_setOf_eq] at hz ⊢
    intro x hx
    rw [← hu x (A' *ᵥ ((A - 1) *ᵥ y)), fixA x hx, hAA']
    exact hz x hx

end Rad

section Sub

variable {n : ℕ} (ε : Fin n → Bool) {P J' : Matrix (Fin n) (Fin n) ℂ}

theorem conj_mat_mul (hP : IsUnit P) (g h : Formalism.REAL.UJ ε) :
    P * uMat (g * h) * P⁻¹ = (P * uMat g * P⁻¹) * (P * uMat h * P⁻¹) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have hm : uMat (g * h) = uMat g * uMat h := by first | rfl | simp [uMat]
  rw [hm]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul]

theorem conj_mat_one (hP : IsUnit P) : P * uMat (1 : Formalism.REAL.UJ ε) * P⁻¹ = 1 := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have h1 : uMat (1 : Formalism.REAL.UJ ε) = 1 := by first | rfl | simp [uMat]
  rw [h1, Matrix.mul_one, Matrix.mul_nonsing_inv P hd]

theorem conj_mat_unitary (hP : IsUnit P) (hJ : Pᴴ * J' * P = Formalism.REAL.Jm ε) (g : Formalism.REAL.UJ ε) (a b : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) J' ((P * uMat g * P⁻¹) *ᵥ a) ((P * uMat g * P⁻¹) *ᵥ b) =
      Formalism.UG.hform (starRingEnd ℂ) J' a b := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have hPiH : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPi, Matrix.conjTranspose_one]
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := by
    first
      | exact g.2
      | (have h := g.prop; rw [Formalism.REAL.UJ.eq_1] at h; exact h)
  set Q := P * uMat g * P⁻¹ with hQdef
  have hQ : Qᴴ * J' * Q = J' := by
    rw [hQdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    calc (P⁻¹)ᴴ * ((uMat g)ᴴ * Pᴴ) * J' * (P * uMat g * P⁻¹)
        = (P⁻¹)ᴴ * ((uMat g)ᴴ * (Pᴴ * J' * P) * uMat g) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (Pᴴ * J' * P) * P⁻¹ := by rw [hJ, hg]
      _ = ((P⁻¹)ᴴ * Pᴴ) * J' * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = J' := by rw [hPiH, hPi, Matrix.one_mul, Matrix.mul_one]
  simp only [hform_eq, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hQ]

def NSub (hP : IsUnit P) (hJ : Pᴴ * J' * P = Formalism.REAL.Jm ε) (U : Submodule ℂ (Fin n → ℂ)) :
    Subgroup (Formalism.REAL.UJ ε) where
  carrier := {g | URad J' U (P * uMat g * P⁻¹)}
  one_mem' := by
    show URad J' U (P * uMat (1 : Formalism.REAL.UJ ε) * P⁻¹)
    rw [conj_mat_one ε hP]
    exact urad_one
  mul_mem' := by
    intro g h hg hh
    show URad J' U (P * uMat (g * h) * P⁻¹)
    rw [conj_mat_mul ε hP]
    exact urad_mul hg hh
  inv_mem' := by
    intro g hg
    show URad J' U (P * uMat g⁻¹ * P⁻¹)
    refine urad_inv hg ?_ ?_ (conj_mat_unitary ε hP hJ g)
    · rw [← conj_mat_mul ε hP, inv_mul_cancel, conj_mat_one ε hP]
    · rw [← conj_mat_mul ε hP, mul_inv_cancel, conj_mat_one ε hP]

end Sub

def HCCusp : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
    ∀ u w : H, u ∈ lowKSub ε lam σ → w ∈ lowKSub ε lam σ →
    ∀ P J' : Matrix (Fin n) (Fin n) ℂ, IsUnit P → Pᴴ * J' * P = Formalism.REAL.Jm ε →
    ∀ U : Submodule ℂ (Fin n → ℂ), U ≠ ⊥ → (∀ x ∈ U, ∀ y ∈ U, Formalism.UG.hform (starRingEnd ℂ) J' x y = 0) →
    ∀ N : Subgroup (Formalism.REAL.UJ ε), (N : Set (Formalism.REAL.UJ ε)) = {g | URad J' U (P * uMat g * P⁻¹)} →
    ∀ ν : Measure N, ν.IsHaarMeasure →
    ∀ x y : Formalism.REAL.UJ ε, ∫ m, coefOn σ u w (x * (m : Formalism.REAL.UJ ε) * y) ∂ν = 0

def URadUnimod : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P J' : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * J' * P = Formalism.REAL.Jm ε →
    ∀ U : Submodule ℂ (Fin n → ℂ), U ≠ ⊥ → (∀ x ∈ U, ∀ y ∈ U, Formalism.UG.hform (starRingEnd ℂ) J' x y = 0) →
    ∀ N : Subgroup (Formalism.REAL.UJ ε), (N : Set (Formalism.REAL.UJ ε)) = {g | URad J' U (P * uMat g * P⁻¹)} →
    ∀ ν : Measure N, ν.IsHaarMeasure → ν.IsMulRightInvariant

end Formalism.MainNotions.BridgeUnipRad

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.DMiMulVecApply
section
open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

section Alg2

variable {k r : ℕ} {κ τ : ℝ}

theorem tV_eI (a : Fin r) : tV k r κ τ (eI k r a) = tF r κ τ a.val := by
  unfold tV eI; rw [if_pos a.isLt]

theorem tV_esI (a : Fin r) : tV k r κ τ (esI k r a) = (tF r κ τ a.val)⁻¹ := by
  unfold tV esI
  have h := a.isLt
  rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
  congr 2; simp only; omega

theorem tV_wb (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : tV k r κ τ i = 1 := by
  unfold tV; rw [if_neg (by omega), if_pos h2]

theorem dM_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (dM k r κ τ *ᵥ v) i = ((tV k r κ τ i : ℝ) : ℂ) * v i := by
  rw [dM, Matrix.mulVec_diagonal]

theorem dMi_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (dMi k r κ τ *ᵥ v) i = (((tV k r κ τ i)⁻¹ : ℝ) : ℂ) * v i := by
  rw [dMi, Matrix.mulVec_diagonal]

theorem dM_mulVec_wb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : dM k r κ τ *ᵥ z = z := by
  funext i; rw [dM_mulVec_apply]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h, mul_zero]
  · rw [tV_wb i (by omega) (by omega)]; simp

theorem dMi_mulVec_wb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : dMi k r κ τ *ᵥ z = z := by
  funext i; rw [dMi_mulVec_apply]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h, mul_zero]
  · rw [tV_wb i (by omega) (by omega)]; simp

theorem dM_mulVec_bvec (i : Fin (2 * r + k + 1)) :
    dM k r κ τ *ᵥ bvec i = ((tV k r κ τ i : ℝ) : ℂ) • bvec i := by
  funext j; rw [dM_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h; rfl
  · simp [bvec, h]

theorem dMi_mulVec_bvec (i : Fin (2 * r + k + 1)) :
    dMi k r κ τ *ᵥ bvec i = (((tV k r κ τ i)⁻¹ : ℝ) : ℂ) • bvec i := by
  funext j; rw [dMi_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h; rfl
  · simp [bvec, h]

theorem inWb_smul {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : ℂ) : inWb k r (a • z) := by
  intro i hi; rw [Pi.smul_apply, hz i hi, smul_zero]

theorem cj_mulVec (x : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) :
    cj k r κ τ x *ᵥ v = dMi k r κ τ *ᵥ (x *ᵥ (dM k r κ τ *ᵥ v)) := by
  rw [cj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem dM_mulVec_fvec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : Fin (r + 1)) :
    dM k r κ τ *ᵥ fvec k r ((τ : ℂ) • z) a = ((tF r κ τ a.val : ℝ) : ℂ) • fvec k r z a := by
  unfold fvec
  by_cases h : a.val < r
  · rw [dif_pos h, dif_pos h, dM_mulVec_bvec, tV_eI]
  · rw [dif_neg h, dif_neg h, dM_mulVec_wb (inWb_smul hz _)]
    have : a.val = r := by omega
    simp [tF, this]

theorem ell_cj (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (x : Mx k r) :
    ell k r ((τ : ℂ) • z) (cj k r κ τ x) = (κ : ℂ)⁻¹ * ell k r z x := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a.val + 1 < r
  · rw [dif_pos h, dif_pos h, cj_apply, tV_eI, tV_eI]
    have e : r - a.val = (r - (a.val + 1)) + 1 := by omega
    have hk := pow_pos hκ (r - (a.val + 1))
    have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    have hkc : (κ : ℂ) ^ (r - (a.val + 1)) ≠ 0 := pow_ne_zero _ hκc
    simp only [tF]
    rw [e, pow_succ]
    push_cast
    field_simp
  · rw [dif_neg h, dif_neg h, cj_mulVec, dM_mulVec_wb (inWb_smul hz _), Matrix.mulVec_smul,
      dMi_mulVec_apply, tV_eI, Pi.smul_apply, smul_eq_mul]
    have e : r - a.val = 1 := by omega
    have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    simp only [tF, e, pow_one]
    push_cast
    field_simp

theorem psi_cj (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) (x : Mx k r) :
    psi k r ((τ : ℂ) • z) ((κ : ℂ) * c) (cj k r κ τ x) = psi k r z c x := by
  unfold psi
  rw [ell_cj hκ hτ hz]
  have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have : (κ : ℂ) * c * ((κ : ℂ)⁻¹ * ell k r z x) = c * ell k r z x := by
    field_simp
  rw [this]

theorem delta_iff {s y : ℂ} {i j : Fin (2 * r + k + 1)} (hs : s ≠ 0) (h1 : i = j → s = 1) :
    (s * y = if i = j then 1 else 0) ↔ (y = if i = j then 1 else 0) := by
  by_cases h : i = j
  · rw [h1 h, one_mul]
  · simp only [h, if_false, mul_eq_zero, hs, false_or]

theorem cj_fac_ne (hκ : 0 < κ) (hτ : 0 < τ) (i j : Fin (2 * r + k + 1)) :
    ((((tV k r κ τ i)⁻¹ * tV k r κ τ j : ℝ)) : ℂ) ≠ 0 := by
  have := tV_pos (k := k) (r := r) hκ hτ i
  have := tV_pos (k := k) (r := r) hκ hτ j
  exact_mod_cast (mul_pos (inv_pos.mpr ‹0 < tV k r κ τ i›) this).ne'

theorem cj_fac_diag (hκ : 0 < κ) (hτ : 0 < τ) (i j : Fin (2 * r + k + 1)) (h : i = j) :
    ((((tV k r κ τ i)⁻¹ * tV k r κ τ j : ℝ)) : ℂ) = 1 := by
  subst h; rw [inv_mul_cancel₀ (tV_pos hκ hτ i).ne']; simp

theorem cj_mem_Nset_iff (hκ : 0 < κ) (hτ : 0 < τ) (x : Mx k r) :
    cj k r κ τ x ∈ Nset k r ↔ x ∈ Nset k r := by
  simp only [Nset, Set.mem_ofPred_eq, cj_mem_UH_iff hκ hτ, cj_apply]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · refine forall_congr' fun a => forall_congr' fun i => imp_congr_right fun _ => ?_
    exact delta_iff (cj_fac_ne hκ hτ _ _) (cj_fac_diag hκ hτ _ _)
  · refine forall_congr' fun i => forall_congr' fun j => imp_congr_right fun _ =>
      imp_congr_right fun _ => imp_congr_right fun _ => ?_
    exact delta_iff (cj_fac_ne hκ hτ _ _) (cj_fac_diag hκ hτ _ _)

theorem UWset_smul {z : Fin (2 * r + k + 1) → ℂ} (hτ : 0 < τ) : UWset k r ((τ : ℂ) • z) = UWset k r z := by
  ext g
  simp only [UWset, Set.mem_ofPred_eq, Matrix.mulVec_smul]
  have hτ' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h => ?_, fun h => by rw [h]⟩)
  exact smul_right_injective _ hτ' h

theorem cj_fix_iff (hκ : 0 < κ) (hτ : 0 < τ) (g : Mx k r) (v : Fin (2 * r + k + 1) → ℂ) (s : ℂ) (hs : s ≠ 0)
    (h1 : dM k r κ τ *ᵥ v = s • v) (h2 : dMi k r κ τ *ᵥ v = s⁻¹ • v) :
    cj k r κ τ g *ᵥ v = v ↔ g *ᵥ v = v := by
  rw [cj_mulVec, h1, Matrix.mulVec_smul, Matrix.mulVec_smul]
  constructor
  · intro h
    have h3 : dM k r κ τ *ᵥ (s • (dMi k r κ τ *ᵥ (g *ᵥ v))) = dM k r κ τ *ᵥ v := by rw [h]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, dM_mul_dMi hκ hτ, Matrix.one_mulVec, h1] at h3
    exact smul_right_injective _ hs h3
  · intro h; rw [h, h2, smul_smul, mul_inv_cancel₀ hs, one_smul]

theorem cj_fix_bvec_iff (hκ : 0 < κ) (hτ : 0 < τ) (g : Mx k r) (i : Fin (2 * r + k + 1)) :
    cj k r κ τ g *ᵥ bvec i = bvec i ↔ g *ᵥ bvec i = bvec i := by
  refine cj_fix_iff hκ hτ g _ ((tV k r κ τ i : ℝ) : ℂ) (by exact_mod_cast (tV_pos hκ hτ i).ne')
    (dM_mulVec_bvec i) ?_
  rw [dMi_mulVec_bvec, Complex.ofReal_inv]

theorem cj_mem_UWset_iff (hκ : 0 < κ) (hτ : 0 < τ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (g : Mx k r) :
    cj k r κ τ g ∈ UWset k r z ↔ g ∈ UWset k r z := by
  simp only [UWset, Set.mem_ofPred_eq, cj_mem_UH_iff hκ hτ]
  refine and_congr Iff.rfl (and_congr (forall_congr' fun a =>
    and_congr (cj_fix_bvec_iff hκ hτ g _) (cj_fix_bvec_iff hκ hτ g _)) ?_)
  exact cj_fix_iff hκ hτ g z 1 one_ne_zero (by rw [one_smul, dM_mulVec_wb hz])
    (by rw [inv_one, one_smul, dMi_mulVec_wb hz])

theorem cj_mem_RStab_iff (hκ : 0 < κ) (hτ : 0 < τ) (g a : Mx k r) :
    cj k r κ τ a ∈ RStab k r (cj k r κ τ g) ↔ a ∈ RStab k r g := by
  simp only [RStab, Set.mem_ofPred_eq]
  rw [← cj_inv hκ hτ, ← cj_mul hκ hτ, ← cj_mul hκ hτ, cj_mem_Nset_iff hκ hτ, cj_mem_Nset_iff hκ hτ]

end Alg2

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.DoubleBoundAndExtensionOfSmooth
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.DoubleDerivativeSmoothness

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

section Side

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

def FI (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (u v : H) : Mt k r × Mt k r → (Wp →L[ℂ] Wp) := fun p =>
  (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹

def DDSmoothAt (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Prop :=
  ∀ u ∈ DDsp σ w0, u ∈ smoothVecs (k := k) (r := r) σ

def KZeroAt (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H)) :
    Prop :=
  ∀ B : H → Wp, IsBesselMapSm z (psi k r z c) σ π B → (∀ v : H, IsKFinHpk (k := k) (r := r) σ v → B v = 0) →
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, B w = 0

def ExtDDAt (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Prop :=
  ∀ u ∈ DDsp σ w0, ∀ v ∈ DDsp σ w0, Integrable (FI z c π σ u v) (μW.prod μN) ∧
    ∀ B : H → Wp, IsBesselMapSm z (psi k r z c) σ π B →
      (∀ v' : H, IsKFinHpk (k := k) (r := r) σ v' →
        ∫ p, FI z c π σ u v' p ∂(μW.prod μN) = (innerSL ℂ (B v')).smulRight (B u)) →
      ∫ p, FI z c π σ u v p ∂(μW.prod μN) = (innerSL ℂ (B v)).smulRight (B u)

theorem s3dDD_of_at {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Mt k r)} {σ : Mx k r → (H →L[ℂ] H)} {w0 : H}
    (hAt : atFormAtPoint z c π μW μN μG νq σ) (hSm : DDSmoothAt σ w0) (hE : ExtDDAt z c π μW μN σ w0)
    (hK : KZeroAt z c π σ) : DoubleCosetSpanBesselBound z c π μW μN μG νq σ w0 := by
  obtain ⟨l, hl, ha, hb⟩ := hAt
  refine ⟨l, hl, fun u hu v hv => ⟨(hE u hu v hv).1,
    (hE u hu v hv).2 l hl (fun v' hv' => (ha u (hSm u hu) v' hv').2)⟩, ?_⟩
  intro u hu hu0 v hv
  by_cases hex : ∃ v', IsKFinHpk (k := k) (r := r) σ v' ∧ l v' ≠ 0
  · obtain ⟨v', hv', hlv'⟩ := hex
    have h := hb u (hSm u hu) hu0 v' hv'
    have ha0 : 0 < ‖l v'‖ ^ 2 := by positivity
    have hL : l2SG νq (fun g => l (σ g u)) = ENNReal.ofReal (‖u‖ ^ 2 / fdegH μG σ u) := by
      rw [show ‖u‖ ^ 2 * ‖l v'‖ ^ 2 / fdegH μG σ u = ‖l v'‖ ^ 2 * (‖u‖ ^ 2 / fdegH μG σ u) by ring,
        ENNReal.ofReal_mul ha0.le] at h
      exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 ha0).ne' ENNReal.ofReal_ne_top).1 h
    rw [hL, ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    ring
  · push Not at hex
    have h0 : l v = 0 := hK l hl hex v (hSm v hv)
    simp [h0]

end Side

def DDSteps (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG νq νq' : Measure (Mt D.R.k D.R.rS)) (w0 : H),
    NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ → IsDSHpk D.R.k D.R.rS L.ε μ σ → IsLowUnitH D.R.k D.R.rS L.ε μ σ w0 →
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG → IsQuotMeas μG (muSof L.μW L.μN) νq → IsQuotMeas μG (muSof L.μW' L.μN) νq' →
      DDSmoothAt σ w0 ∧ (ExtDDAt L.z L.c L.π L.μW L.μN σ w0 ∧ KZeroAt L.z L.c L.π σ) ∧
        (ExtDDAt L.z' L.c L.π' L.μW' L.μN σ w0 ∧ KZeroAt L.z' L.c L.π' σ)

theorem extension_smooth_of_admissible (D : D7) (Ch Cg Cq : ℝ) (h : adm22 D Ch Cg Cq) : ExtSm D Ch Cg Cq := by
  intro L lam0 μ ka b κ H _ _ _ σ μG νq νq' w0 hN hσ _ hG hq hq'
  have h' := h L lam0 μ ka b κ H σ μG νq νq' hN hσ hG hq hq'
  exact ⟨fun _ => h'.1, fun _ => h'.2⟩

theorem double_bound_of_admissible_and_steps (D : D7) (Ch Cg Cq : ℝ) (h : adm22 D Ch Cg Cq) (hS : DDSteps D Ch Cg Cq) :
    DoubleCosetBesselBound D Ch Cg Cq := by
  intro L lam0 μ ka b κ H _ _ _ σ μG νq νq' w0 hN hσ hw0 hG hq hq'
  have h' := h L lam0 μ ka b κ H σ μG νq νq' hN hσ hG hq hq'
  obtain ⟨hSm, ⟨hE, hK⟩, hE', hK'⟩ := hS L lam0 μ ka b κ H σ μG νq νq' w0 hN hσ hw0 hG hq hq'
  exact ⟨s3dDD_of_at h'.1 hSm hE hK, s3dDD_of_at h'.2 hSm hE' hK'⟩

theorem double_bound_and_extension_of_smooth (D : D7) (Ch Cg Cq : ℝ) (h : adm22 D Ch Cg Cq) (hS : DDSteps D Ch Cg Cq) :
    DoubleCosetBesselBound D Ch Cg Cq ∧ ExtSm D Ch Cg Cq :=
  ⟨double_bound_of_admissible_and_steps D Ch Cg Cq h hS, extension_smooth_of_admissible D Ch Cg Cq h⟩

end Formalism.MainNotions.DoubleDerivativeSmoothness
end
end

