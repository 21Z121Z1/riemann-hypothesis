import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0003
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.Bundle0001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0004
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.Bundle0002
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0001

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.InnerLowerSelf
section
noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem inner_lower_self {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {A : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {w : V}
    (hR : Formalism.REAL.KRel ε A) (hU : Formalism.REAL.KUnit ε A) (hw : Formalism.REAL.KHighest ε A Λ w)
    {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    ⟪A b a w, A b a w⟫_ℂ = (((Λ a - Λ b : ℝ)) : ℂ) * ⟪w, w⟫_ℂ := by
  have hba : b ≠ a := ne_of_gt hab
  have hc := hR a b b a he he.symm
  simp only [if_true] at hc
  have hx := congrArg (fun F : Module.End ℂ V => F w) hc
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hw.2 a b hab he, map_zero, sub_zero] at hx
  have h1 := hU b a he.symm w (A b a w)
  rw [h1, hx, hw.1 a, hw.1 b, ← sub_smul, inner_smul_right]
  push_cast
  ring

theorem kType_dom {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : KDom ε Λ := by
  intro a b hab he
  have h := inner_lower_self (KType.kRel T) (KType.kUnit T) (KType.kHighest_w T) hab he
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, T.w_norm] at h
  have h2 : ‖kunits T b a T.w‖ ^ 2 = Λ a - Λ b := by
    have h' : ((‖kunits T b a T.w‖ ^ 2 : ℝ) : ℂ) = ((Λ a - Λ b : ℝ) : ℂ) := by
      have h0 := h
      simp only [RCLike.ofReal_one, one_pow, mul_one] at h0
      simpa using h0
    exact Complex.ofReal_injective h'
  have h3 : (0 : ℝ) ≤ ‖kunits T b a T.w‖ ^ 2 := sq_nonneg _
  linarith

theorem kTypeIntDom_of
    (hint : ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (_T : KType ε Λ), ∀ a, ∃ m : ℤ, Λ a = m) :
    KTypeIntDomStatement :=
  fun n ε Λ T => ⟨hint n ε Λ T, kType_dom T⟩

theorem kTypeIntDom : KTypeIntDomStatement :=
  kTypeIntDom_of fun _ _ _ T => kType_int T

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.PrhoEntryHasDerivAt
section
noncomputable section

open Matrix Finset
open scoped Kronecker

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma prho_submatrix_mul {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (A B : Matrix ι ι ℂ) (hA : ∀ i k, P i → ¬ P k → A i k = 0) :
    ((A * B).submatrix Subtype.val Subtype.val : Matrix {i // P i} {i // P i} ℂ) =
      (A.submatrix Subtype.val Subtype.val : Matrix {i // P i} {i // P i} ℂ) *
        (B.submatrix Subtype.val Subtype.val : Matrix {i // P i} {i // P i} ℂ) := by
  ext p r
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Finset.sum_filter_of_ne (p := P) (fun k _ hk => by_contra fun h => hk (by rw [hA _ _ p.2 h, zero_mul]))]
  exact Finset.sum_subtype _ (fun k => by simp) _

lemma prho_sub_kron {ι κ : Type*} (A B : Matrix ι ι ℂ) (C : Matrix κ κ ℂ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext p q; simp [Matrix.kroneckerMap_apply, sub_mul]

lemma prho_kron_sub {ι κ : Type*} (A : Matrix ι ι ℂ) (B C : Matrix κ κ ℂ) :
    A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  ext p q; simp [Matrix.kroneckerMap_apply, mul_sub]

def adFull (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  g ⊗ₖ g.map (starRingEnd ℂ)

def adDFull (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  X ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) - (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ Xᵀ

lemma adFull_mul (g h : Matrix (Fin n) (Fin n) ℂ) : adFull (g * h) = adFull g * adFull h := by
  unfold adFull
  rw [Matrix.map_mul, mul_kronecker_mul]

lemma adFull_one : adFull (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold adFull
  rw [Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _), one_kronecker_one]

lemma adFull_star (g : Matrix (Fin n) (Fin n) ℂ) : star (adFull g) = adFull (star g) := by
  ext p q
  simp only [adFull, Matrix.star_apply, Matrix.kroneckerMap_apply, Matrix.map_apply, star_mul',
    RCLike.star_def, RCLike.conj_conj]

lemma adDFull_bracket (X Y : Matrix (Fin n) (Fin n) ℂ) :
    adDFull X * adDFull Y - adDFull Y * adDFull X = adDFull (X * Y - Y * X) := by
  simp only [adDFull, sub_mul, mul_sub, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.transpose_sub, Matrix.transpose_mul, prho_sub_kron, prho_kron_sub]
  abel

variable {ε : Fin n → Bool} {β : Bool}

lemma adFull_zero_out {g : Matrix (Fin n) (Fin n) ℂ} (hg : g * Jm ε = Jm ε * g) (p k : Fin n × Fin n)
    (hp : ε p.1 = β ∧ ε p.2 = !β) (hk : ¬ (ε k.1 = β ∧ ε k.2 = !β)) : adFull g p k = 0 := by
  simp only [adFull, Matrix.kroneckerMap_apply, Matrix.map_apply]
  by_cases h1 : ε k.1 = β
  · have h2 : ε p.2 ≠ ε k.2 := fun h => hk ⟨h1, by rw [← h]; exact hp.2⟩
    rw [uq_offdiag_zero hg h2, map_zero, mul_zero]
  · have h2 : ε p.1 ≠ ε k.1 := fun h => h1 (by rw [← h]; exact hp.1)
    rw [uq_offdiag_zero hg h2, zero_mul]

lemma adDFull_zero_out {X : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X) (p k : Fin n × Fin n)
    (hp : ε p.1 = β ∧ ε p.2 = !β) (hk : ¬ (ε k.1 = β ∧ ε k.2 = !β)) : adDFull X p k = 0 := by
  simp only [adDFull, Matrix.sub_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  by_cases h1 : ε k.1 = β
  · have h2 : ε p.2 ≠ ε k.2 := fun h => hk ⟨h1, by rw [← h]; exact hp.2⟩
    have h3 : p.2 ≠ k.2 := fun h => h2 (by rw [h])
    rw [Matrix.one_apply_ne h3, uq_offdiag_zero hX (Ne.symm h2), mul_zero, mul_zero, sub_zero]
  · have h2 : ε p.1 ≠ ε k.1 := fun h => h1 (by rw [← h]; exact hp.1)
    have h3 : p.1 ≠ k.1 := fun h => h2 (by rw [h])
    rw [Matrix.one_apply_ne h3, uq_offdiag_zero hX h2, zero_mul, zero_mul, sub_zero]

variable (ε β)

def pRhoM (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (pIdx ε β) (pIdx ε β) ℂ :=
  (adFull g).submatrix Subtype.val Subtype.val

lemma pRhoM_mul {g : Matrix (Fin n) (Fin n) ℂ} (hg : g * Jm ε = Jm ε * g) (h : Matrix (Fin n) (Fin n) ℂ) :
    pRhoM ε β (g * h) = pRhoM ε β g * pRhoM ε β h := by
  unfold pRhoM
  rw [adFull_mul]
  exact prho_submatrix_mul (fun p : Fin n × Fin n => ε p.1 = β ∧ ε p.2 = !β) _ _
    (fun i k hi hk => adFull_zero_out hg i k hi hk)

lemma pRhoM_one : pRhoM ε β (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold pRhoM
  rw [adFull_one]
  exact Matrix.submatrix_one _ Subtype.val_injective

lemma pRhoM_star (g : Matrix (Fin n) (Fin n) ℂ) : star (pRhoM ε β g) = pRhoM ε β (star g) := by
  unfold pRhoM
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, ← Matrix.star_eq_conjTranspose,
    adFull_star]

lemma pRhoM_mem (k : KG ε) : pRhoM ε β (toMK k) ∈ unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ) := by
  have hk : toMK k ∈ Kset ε := k.2
  have hs : star (toMK k) ∈ Kset ε := Kset_star ε hk
  rw [Unitary.mem_iff, pRhoM_star, ← pRhoM_mul ε β hs.2, ← pRhoM_mul ε β hk.2,
    Unitary.star_mul_self_of_mem hk.1, Unitary.mul_star_self_of_mem hk.1, pRhoM_one]
  exact ⟨rfl, rfl⟩

def pRho : KG ε →* unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ) where
  toFun k := ⟨pRhoM ε β (toMK k), pRhoM_mem ε β k⟩
  map_one' := Subtype.ext (pRhoM_one ε β)
  map_mul' k l := Subtype.ext (pRhoM_mul ε β (k.2 : toMK k ∈ Kset ε).2 (toMK l))

lemma pRho_apply (k : KG ε) (p q : pIdx ε β) :
    ((pRho ε β k : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ) p q =
      toMK k p.1.1 q.1.1 * star (toMK k p.1.2 q.1.2) := rfl

def pDRho : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (pIdx ε β) (pIdx ε β) ℂ where
  toFun X := (adDFull X).submatrix Subtype.val Subtype.val
  map_add' X Y := by
    ext p q
    simp only [adDFull, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply]
    ring
  map_smul' c X := by
    ext p q
    simp only [adDFull, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma pDRho_apply (X : Matrix (Fin n) (Fin n) ℂ) (p q : pIdx ε β) :
    pDRho ε β X p q = X p.1.1 q.1.1 * (1 : Matrix (Fin n) (Fin n) ℂ) p.1.2 q.1.2 -
      (1 : Matrix (Fin n) (Fin n) ℂ) p.1.1 q.1.1 * X q.1.2 p.1.2 := rfl

theorem pDRho_single (a b : Fin n) : pDRho ε β (Matrix.single a b 1) = pAdM ε β a b := by
  ext p q
  rw [pDRho_apply]
  simp only [pAdM, Matrix.single_apply, Matrix.one_apply]
  by_cases h1 : p.1.1 = a <;> by_cases h2 : q.1.1 = b <;> by_cases h3 : p.1.2 = q.1.2 <;>
    by_cases h4 : q.1.2 = a <;> by_cases h5 : p.1.2 = b <;> by_cases h6 : p.1.1 = q.1.1 <;>
    simp_all [eq_comm]

theorem pDRho_bracket {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X * Jm ε = Jm ε * X)
    (hY : Y * Jm ε = Jm ε * Y) :
    pDRho ε β X * pDRho ε β Y - pDRho ε β Y * pDRho ε β X = pDRho ε β (X * Y - Y * X) := by
  have e : ∀ Z : Matrix (Fin n) (Fin n) ℂ, pDRho ε β Z = (adDFull Z).submatrix Subtype.val Subtype.val :=
    fun _ => rfl
  have hs : ∀ A B : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ,
      ((A - B).submatrix Subtype.val Subtype.val : Matrix (pIdx ε β) (pIdx ε β) ℂ) =
        (A.submatrix Subtype.val Subtype.val : Matrix (pIdx ε β) (pIdx ε β) ℂ) -
          (B.submatrix Subtype.val Subtype.val : Matrix (pIdx ε β) (pIdx ε β) ℂ) := fun _ _ => rfl
  rw [e, e, e, ← prho_submatrix_mul (fun p : Fin n × Fin n => ε p.1 = β ∧ ε p.2 = !β) _ _
      (fun i k hi hk => adDFull_zero_out hX i k hi hk),
    ← prho_submatrix_mul (fun p : Fin n × Fin n => ε p.1 = β ∧ ε p.2 = !β) _ _
      (fun i k hi hk => adDFull_zero_out hY i k hi hk), ← hs, adDFull_bracket]

lemma prho_single_bracket (a b c d : Fin n) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1 h2; simp [Matrix.single_mul_single_same]
  · subst h1; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h2]
  · subst h2; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, h1]
  · simp [Matrix.single_mul_single_of_ne, h1, h2]

theorem pAdM_kRel : Formalism.REAL.KRel ε (pAdM ε β) := by
  intro a b c d hab hcd
  have e : ∀ a b, pAdM ε β a b = pDRho ε β (Matrix.single a b 1) := fun a b => (pDRho_single ε β a b).symm
  simp only [e]
  rw [pDRho_bracket ε β (single_mul_Jm hab 1) (single_mul_Jm hcd 1), prho_single_bracket]
  split_ifs <;> simp

theorem pRho_continuous :
    Continuous (fun k : KG ε =>
      ((pRho ε β k : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ)) := by
  have hm : Continuous (fun k : KG ε => toMK k) := (continuous_toM ε).comp continuous_subtype_val
  refine continuous_matrix fun p q => ?_
  simp only [pRho_apply]
  exact (hm.matrix_elem _ _).mul ((hm.matrix_elem _ _).star)

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma prho_entry_hasDerivAt (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have h := (L.hasFDerivAt).comp_hasDerivAt _ (hasDerivAt_exp_smul_const X ((0 : ℝ) : ℂ))
  have h2 := hasDerivAt_real_of_complex' (z := 0) h
  have e : L (NormedSpace.exp (((0 : ℝ) : ℂ) • X) * X) = X i j := by simp [L]
  exact h2.congr_deriv e

end Deriv

theorem pRho_hasDerivAt (X : Matrix (Fin n) (Fin n) ℂ) (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (i j : pIdx ε β) :
    HasDerivAt (fun t : ℝ =>
      ((pRho ε β (γ t) : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ) i j)
      (pDRho ε β X i j) 0 := by
  have hf : (fun t : ℝ =>
      ((pRho ε β (γ t) : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ) i j) =
      fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i.1.1 j.1.1 *
        star (NormedSpace.exp ((t : ℂ) • X) i.1.2 j.1.2) := by
    funext t
    rw [pRho_apply, hγ t]
  rw [hf]
  have h := (prho_entry_hasDerivAt X i.1.1 j.1.1).mul (prho_entry_hasDerivAt X i.1.2 j.1.2).star
  have hs : star (X i.1.2 j.1.2) = -X j.1.2 i.1.2 := by
    have := congrFun (congrFun (onep_skew hX) j.1.2) i.1.2
    simpa only [Matrix.conjTranspose_apply, Matrix.neg_apply] using this
  have e : X i.1.1 j.1.1 * star (NormedSpace.exp (((0 : ℝ) : ℂ) • X) i.1.2 j.1.2) +
      NormedSpace.exp (((0 : ℝ) : ℂ) • X) i.1.1 j.1.1 * star (X i.1.2 j.1.2) = pDRho ε β X i j := by
    rw [pDRho_apply, hs]
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_apply]
    split_ifs <;> simp [sub_eq_add_neg]
  exact h.congr_deriv e

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.TensHW
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem tensHW_mem_khwSub {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ W) (ν : Fin n → ℝ) (v : W) :
    v ∈ khwSub ε E ν ↔ Formalism.REAL.KHighest ε E ν v := by
  simp only [khwSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero, Formalism.REAL.KHighest,
    Formalism.REAL.IsWeight]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by simpa using h1 a, fun a b hab he => h2 a b ⟨hab, he⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a => by simpa using h1 a, fun a b h => h2 a b h.1 h.2⟩

theorem tensHW_hw_eq {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    {ε : Fin n → Bool} {A : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {w : V}
    (hA : Formalism.REAL.KRel ε A) (hU : Formalism.REAL.KUnit ε A) (hw : Formalism.REAL.KHighest ε A Λ w)
    (hspan : Formalism.REAL.kSpan ε A w = ⊤) {μ : Fin n → ℝ} {y : V}
    (hy : Formalism.REAL.KHighest ε A μ y) (hy0 : y ≠ 0) :
    μ = Λ ∧ ∃ c : ℂ, y = c • w := by
  rcases Formalism.REAL.kHiUniq V n ε A Λ μ w y hA hU hw (by rw [hspan]; exact Submodule.mem_top) hy with h | h
  · exact absurd h hy0
  · exact h

theorem tensHW_of (h : LowCompStatement) : TensHWStatement := by
  intro V _ _ n ε A Λ w ι _ _ M γ hA hU hw hspan hM hdiag
  have key : ∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : ι => V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (tensAct A M) ν x →
      ∃ i, ν = Λ + γ i ∧ x i ≠ 0 ∧ ∃ c : ℂ, x i = c • w := by
    intro ν x hx hK
    obtain ⟨β, ⟨i, hi, hxi⟩, hall⟩ := h V n ε A ι M γ hM hdiag ν x hx hK
    obtain ⟨hμ, c, hc⟩ := tensHW_hw_eq hA hU hw hspan (hall i hi) hxi
    refine ⟨i, ?_, hxi, c, hc⟩
    rw [hi, ← hμ, sub_add_cancel]
  refine ⟨fun ν x hx hK => ?_, fun ν => ?_⟩
  · obtain ⟨i, hi, -⟩ := key ν x hx hK
    exact ⟨i, hi⟩
  · classical
    let L : khwSub ε (tensAct A M) ν →ₗ[ℂ] ({i : ι // ν = Λ + γ i} → ℂ) :=
      { toFun := fun x i => ⟪w, (x : PiLp 2 (fun _ : ι => V)) i.1⟫_ℂ
        map_add' := fun x y => by ext i; simp
        map_smul' := fun c x => by ext i; simp }
    have hL : Function.Injective L := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx0
      by_contra hne
      have hx' : (x : PiLp 2 (fun _ : ι => V)) ≠ 0 := fun h0 => hne (Subtype.ext h0)
      have hK := (tensHW_mem_khwSub ε _ ν _).1 x.2
      obtain ⟨i, hi, hxi, c, hc⟩ := key ν x hx' hK
      have h1 : ⟪w, (x : PiLp 2 (fun _ : ι => V)) i⟫_ℂ = 0 := congrFun hx0 ⟨i, hi⟩
      rw [hc, inner_smul_right] at h1
      rcases mul_eq_zero.1 h1 with h2 | h2
      · exact hxi (by rw [hc, h2, zero_smul])
      · exact hxi (by rw [hc, inner_self_eq_zero.1 h2, smul_zero])
    have : FiniteDimensional ℂ (khwSub ε (tensAct A M) ν) := Module.Finite.of_injective L hL
    refine ⟨this, ?_⟩
    calc Module.finrank ℂ (khwSub ε (tensAct A M) ν)
        ≤ Module.finrank ℂ ({i : ι // ν = Λ + γ i} → ℂ) :=
          LinearMap.finrank_le_finrank_of_injective hL
      _ = Nat.card {i : ι // ν = Λ + γ i} := by
          rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

theorem tensHW : TensHWStatement := tensHW_of lowComp

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.TensRepB
section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

section Lin

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tensL_add_left (m m' : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    tensL (m + m') S = tensL m S + tensL m' S := by
  ext x i
  simp [tensL_apply, add_smul, Finset.sum_add_distrib]

theorem tensL_smul_left (c : ℂ) (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    tensL (c • m) S = c • tensL m S := by
  ext x i
  simp [tensL_apply, mul_smul, Finset.smul_sum]

theorem tensL_add_right (m : Matrix ι ι ℂ) (S S' : V →L[ℂ] V) :
    tensL m (S + S') = tensL m S + tensL m S' := by
  ext x i
  simp [tensL_apply, smul_add, Finset.sum_add_distrib]

theorem tensL_smul_right (c : ℂ) (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    tensL m (c • S) = c • tensL m S := by
  ext x i
  simp [tensL_apply, Finset.smul_sum, smul_comm c]

theorem tensL_one_apply (S : V →L[ℂ] V) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensL (1 : Matrix ι ι ℂ) S x i = S (x i) := by
  simp [tensL_apply, Matrix.one_apply]

theorem tensL_id_apply (m : Matrix ι ι ℂ) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensL m (1 : V →L[ℂ] V) x i = ∑ j, m i j • x j := by
  simp [tensL_apply]

end Lin

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]

def tensD (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) where
  toFun X := tensL (dρ X) 1 + tensL 1 (T.dτ X)
  map_add' X Y := by
    simp only [map_add, tensL_add_left, tensL_add_right]
    abel
  map_smul' c X := by
    simp only [map_smul, tensL_smul_left, tensL_smul_right, RingHom.id_apply, smul_add]

theorem tensD_apply (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
    (x : PiLp 2 (fun _ : ι => T.V)) (i : ι) :
    tensD T dρ X x i = T.dτ X (x i) + ∑ j, dρ X i j • x j := by
  simp [tensD, Matrix.one_apply, add_comm]

theorem tens_curve_zero {X : Matrix (Fin n) (Fin n) ℂ} (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) : γ 0 = 1 := by
  apply onep_KG_ext
  rw [hγ]
  show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = (1 : Matrix (Fin n) (Fin n) ℂ)
  simp

theorem tensD_hasDeriv (ρ : KG ε →* unitary (Matrix ι ι ℂ))
    (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (γ : ℝ → KG ε) (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X))
    (hd : ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
      (dρ X i j) 0) :
    HasDerivAt (fun t : ℝ => ((tensTau T ρ (γ t) : unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ]
      PiLp 2 (fun _ : ι => T.V))) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)))
      (tensD T dρ X) 0 := by
  have h0 := tens_curve_zero γ hγ
  have hD := hasDerivAt_tensL (V := T.V) hd (T.hasDeriv X hX γ hγ)
  simp only [tensTau_coe, tensOp_eq]
  convert hD using 1
  simp [tensD, h0]

theorem tensD_units (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ) (a b : Fin n) :
    ((tensD T dρ (Matrix.single a b 1) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) :
      Module.End ℂ (PiLp 2 (fun _ : ι => T.V))) =
      tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) a b := by
  refine LinearMap.ext fun x => PiLp.ext fun i => ?_
  simp [tensAct, tensD_apply, kunits]

include T in

def tensKRep (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hc : Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) : KRep ε where
  V := PiLp 2 (fun _ : ι => T.V)
  τ := tensTau T ρ
  cont := tensTau_cont T ρ hc
  dτ := tensD T dρ
  hasDeriv X hX γ hγ := tensD_hasDeriv T ρ dρ hX γ hγ (hd X hX γ hγ)

theorem tensKRep_units (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hc : Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) :
    (tensKRep T ρ dρ hc hd).units = tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) :=
  funext fun a => funext fun b => tensD_units T dρ a b

theorem tensKRep_op (ρ : KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hc : Continuous (fun k : KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0) (k : KG ε) :
    (tensKRep T ρ dρ hc hd).op k = tensOp T ρ k :=
  tensTau_coe T ρ k

theorem tensRep : TensRepStatement := by
  intro n ε Λ T ι _ _ ρ dρ hc hd
  exact ⟨tensTau T ρ, tensD T dρ, tensTau_cont T ρ hc,
    fun X hX γ hγ => tensD_hasDeriv T ρ dρ hX γ hγ (hd X hX γ hγ), fun a b => tensD_units T dρ a b⟩

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

