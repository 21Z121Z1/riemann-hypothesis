import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle0001
import Lemmata.MovedPointExistence.ExistsMoved

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem exists_mu {lam : Fin n → ℝ} (hlam : IsHCParam lam) : ∃ μ : Fin n → ℤ, IsMu lam μ := by
  choose m hm using hlam.2
  refine ⟨fun a => m a + (n : ℤ) - 1 - ((a : ℕ) : ℤ), ?_⟩
  unfold IsMu
  intro a
  have h := hm a
  simp only [rho]
  push_cast
  linarith

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool}

open PolarDecomposition

private lemma Jm_mul_self_eq_one' : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private lemma Jm_conjTranspose_eq_self' : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

lemma isHermitian_of_mem_noncompactPart' {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : Xᴴ = X := by
  obtain ⟨hG, hXJ⟩ := hX
  have hJ := Jm_mul_self_eq_one' (ε := ε)
  have h1 : Xᴴ * Jm ε = X * Jm ε := by
    rw [hXJ]
    unfold inG at hG
    exact eq_neg_of_add_eq_zero_left hG
  calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, hJ, mul_one]
    _ = X * Jm ε * Jm ε := by rw [h1]
    _ = X := by rw [mul_assoc, hJ, mul_one]

lemma inP_JXJ {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : Jm ε * X * Jm ε = -X := by
  rw [mul_assoc, hX.2, mul_neg, ← mul_assoc, Jm_mul_self_eq_one', one_mul]

lemma toMK_facts (k : KG ε) : (toMK k)ᴴ * toMK k = 1 ∧ toMK k * (toMK k)ᴴ = 1 ∧
    toMK k * Jm ε = Jm ε * toMK k := by
  have hk : toMK k ∈ Kset ε := k.2
  obtain ⟨hu, hc⟩ := hk
  refine ⟨?_, ?_, hc⟩
  · have h := Matrix.mem_unitaryGroup_iff'.1 hu
    rwa [Matrix.star_eq_conjTranspose] at h
  · have h := Matrix.mem_unitaryGroup_iff.1 hu
    rwa [Matrix.star_eq_conjTranspose] at h

lemma toMK_inv (k : KG ε) : toMK k⁻¹ = (toMK k)ᴴ := by
  have h1 : toMK k⁻¹ * toMK k = 1 := by
    unfold toMK toM
    simp
  have h2 := (toMK_facts k).2.1
  calc toMK k⁻¹ = toMK k⁻¹ * (toMK k * (toMK k)ᴴ) := by rw [h2, mul_one]
    _ = (toMK k)ᴴ := by rw [← mul_assoc, h1, one_mul]

lemma exists_toMK {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : ∃ u : KG ε, toMK u = k := by
  obtain ⟨hu, hc⟩ := hk
  have h1 : k * kᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.1 hu
    rwa [Matrix.star_eq_conjTranspose] at h
  have h2 : kᴴ * k = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.1 hu
    rwa [Matrix.star_eq_conjTranspose] at h
  have hUJ : inUJ ε k := by
    unfold inUJ
    rw [mul_assoc, ← hc, ← mul_assoc, h2, one_mul]
  refine ⟨⟨⟨⟨k, kᴴ, h1, h2⟩, ?_⟩, ?_⟩, rfl⟩
  · exact hUJ
  · exact (⟨hu, hc⟩ : k ∈ Kset ε)

lemma kexp_sq (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hH : Xᴴ = X) :
    (toMK k * NormedSpace.exp X)ᴴ * (toMK k * NormedSpace.exp X) = NormedSpace.exp (X + X) := by
  rw [Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose, hH, mul_assoc, ← mul_assoc (toMK k)ᴴ,
    (toMK_facts k).1, one_mul, ← Matrix.exp_add_of_commute _ _ (Commute.refl _)]

theorem polar_exists {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ∃ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X ∧ g = toMK k * NormedSpace.exp X := by
  obtain ⟨k, hk, Y, hY, hgk⟩ := polar_UJ (ε := ε) (g := g) hg
  obtain ⟨u, hu⟩ := exists_toMK hk
  exact ⟨u, Y, hY, by rw [hu]; exact hgk⟩

theorem polar_unique {k k' : KG ε} {X X' : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (hX' : inP ε X')
    (h : toMK k * NormedSpace.exp X = toMK k' * NormedSpace.exp X') : k = k' ∧ X = X' := by
  have hH := isHermitian_of_mem_noncompactPart' hX
  have hH' := isHermitian_of_mem_noncompactPart' hX'
  have hXX : X + X = X' + X' := by
    refine polar_exp_inj (by rw [conjTranspose_add, hH]) (by rw [conjTranspose_add, hH']) ?_
    rw [← kexp_sq k hH, ← kexp_sq k' hH', h]
  have hXe : X = X' := polar_half hXX
  subst hXe
  refine ⟨?_, rfl⟩
  have hm : toMK k = toMK k' := by
    have := congrArg (· * NormedSpace.exp (-X)) h
    simp only [Matrix.mul_assoc, polar_exp_mul_neg, Matrix.mul_one] at this
    exact this
  exact Subtype.ext (Subtype.ext (Units.ext hm))

theorem inUJ_kexp (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : inUJ ε (toMK k * NormedSpace.exp X) := by
  have hJ := Jm_mul_self_eq_one' (ε := ε)
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJ, hJ⟩, rfl⟩
  have hconj : Jm ε * NormedSpace.exp X * Jm ε = NormedSpace.exp (-X) := by
    have h := Matrix.exp_conj (Jm ε) X hJu
    rw [hJinv, inP_JXJ hX] at h
    exact h.symm
  have hf := toMK_facts k
  unfold inUJ
  rw [Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose, isHermitian_of_mem_noncompactPart' hX]
  calc NormedSpace.exp X * (toMK k)ᴴ * Jm ε * (toMK k * NormedSpace.exp X)
      = NormedSpace.exp X * ((toMK k)ᴴ * (Jm ε * toMK k)) * NormedSpace.exp X := by
        simp only [mul_assoc]
    _ = NormedSpace.exp X * ((toMK k)ᴴ * (toMK k * Jm ε)) * NormedSpace.exp X := by
        rw [← hf.2.2]
    _ = NormedSpace.exp X * Jm ε * NormedSpace.exp X := by
        rw [← mul_assoc (toMK k)ᴴ, hf.1, one_mul]
    _ = Jm ε * (Jm ε * NormedSpace.exp X * Jm ε) * NormedSpace.exp X := by
        simp only [← mul_assoc, hJ, one_mul]
    _ = Jm ε * NormedSpace.exp (-X) * NormedSpace.exp X := by rw [hconj]
    _ = Jm ε := by
        rw [mul_assoc, ← Matrix.exp_add_of_commute _ _ ((Commute.refl X).neg_left), neg_add_cancel,
          NormedSpace.exp_zero, mul_one]

theorem inP_conj (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    inP ε (toMK k * X * toMK k⁻¹) ∧
      NormedSpace.exp (toMK k * X * toMK k⁻¹) = toMK k * NormedSpace.exp X * toMK k⁻¹ := by
  have hf := toMK_facts k
  have hinv : (toMK k)⁻¹ = (toMK k)ᴴ := Matrix.inv_eq_right_inv hf.2.1
  have hu : IsUnit (toMK k) := ⟨⟨toMK k, (toMK k)ᴴ, hf.2.1, hf.1⟩, rfl⟩
  have hcJ : (toMK k)ᴴ * Jm ε = Jm ε * (toMK k)ᴴ := by
    have h := congrArg Matrix.conjTranspose hf.2.2
    simp only [Matrix.conjTranspose_mul, Jm_conjTranspose_eq_self'] at h
    exact h.symm
  have h2 : toMK k * X * (toMK k)ᴴ * Jm ε = -(Jm ε * (toMK k * X * (toMK k)ᴴ)) := by
    calc toMK k * X * (toMK k)ᴴ * Jm ε = toMK k * (X * Jm ε) * (toMK k)ᴴ := by
          rw [mul_assoc _ (toMK k)ᴴ, hcJ]
          simp only [mul_assoc]
      _ = toMK k * (-(Jm ε * X)) * (toMK k)ᴴ := by rw [hX.2]
      _ = -(Jm ε * (toMK k * X * (toMK k)ᴴ)) := by
          rw [mul_neg, neg_mul, ← mul_assoc (toMK k) (Jm ε) X, hf.2.2]
          simp only [mul_assoc]
  rw [toMK_inv]
  refine ⟨⟨?_, h2⟩, ?_⟩
  · unfold inG
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      isHermitian_of_mem_noncompactPart' hX, ← mul_assoc (toMK k) X, h2, neg_add_cancel]
  · have h := Matrix.exp_conj (toMK k) X hu
    rwa [hinv] at h

theorem exp_noncompactPart_posDef {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : (NormedSpace.exp X).PosDef := by
  have hH : Xᴴ = X := isHermitian_of_mem_noncompactPart' hX
  have hYH : ((1 / 2 : ℂ) • X)ᴴ = (1 / 2 : ℂ) • X := by
    rw [Matrix.conjTranspose_smul, hH]
    norm_num
  have hsplit : NormedSpace.exp X =
      (NormedSpace.exp ((1 / 2 : ℂ) • X))ᴴ * NormedSpace.exp ((1 / 2 : ℂ) • X) := by
    rw [← Matrix.exp_conjTranspose, hYH, ← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul]
    norm_num
  rw [hsplit]
  apply Matrix.PosDef.conjTranspose_mul_self
  exact Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_exp _)

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InhabA
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7.InhabA

open ReciprocityTheory.ChartRestriction.DS

section DetDeriv

open NormedSpace

variable {ι : Type} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry (X : Matrix ι ι ℂ) (i j : ι) :
    HasDerivAt (fun t : ℝ => (exp (t • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, exp_zero, one_mul] at h
  let L : Matrix ι ι ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_det_of_one (A : ℝ → Matrix ι ι ℂ) (A' : Matrix ι ι ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 := by
  first | exact Bl.MovedPointExistence.goal1 .. | (apply Bl.MovedPointExistence.goal1 <;> assumption) | (intros; apply Bl.MovedPointExistence.goal1 <;> assumption)

end DetDeriv

variable {m : ℕ}

theorem eq_zero_of_comm {ε : Fin m → Bool} {g : Matrix (Fin m) (Fin m) ℂ} (hg : g * Jm ε = Jm ε * g)
    (i j : Fin m) (hij : ε i ≠ ε j) : g i j = 0 := by
  have h := congrFun (congrFun hg i) j
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  cases hi : ε i <;> cases hj : ε j
  · exact absurd (hi.trans hj.symm) hij
  · simp only [hi, hj, Bool.false_eq_true, if_false, if_true] at h
    linear_combination h / 2
  · simp only [hi, hj, Bool.false_eq_true, if_false, if_true] at h
    linear_combination -h / 2
  · exact absurd (hi.trans hj.symm) hij

theorem submatrix_mul_blk {ε : Fin m → Bool} (s : Bool) {g : Matrix (Fin m) (Fin m) ℂ}
    (hg : ∀ i j, ε i ≠ ε j → g i j = 0) (h : Matrix (Fin m) (Fin m) ℂ) :
    (g * h).submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1) =
      g.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1) *
        h.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1) := by
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Finset.sum_filter_of_ne (p := fun l => ε l = s)]
  · exact Finset.sum_subtype _ (fun l => by simp) (fun l => g x.1 l * h l y.1)
  · intro l _ hl
    by_contra hne
    exact hl (by rw [hg x.1 l (by rw [x.2]; exact Ne.symm hne), zero_mul])

theorem star_det_mul_det {ε : Fin m → Bool} (s : Bool) {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ Kset ε) :
    star (k.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det *
      (k.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det = 1 := by
  have hb := eq_zero_of_comm hk.2
  have hbs : ∀ i j, ε i ≠ ε j → kᴴ i j = 0 := fun i j hij => by
    rw [Matrix.conjTranspose_apply, hb j i (Ne.symm hij), star_zero]
  have hu : kᴴ * k = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').1 hk.1
    simpa [Matrix.star_eq_conjTranspose] using this
  rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, Matrix.conjTranspose_submatrix,
    ← submatrix_mul_blk s hbs k, hu, Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]

theorem det_ne_zero {ε : Fin m → Bool} (s : Bool) {k : Matrix (Fin m) (Fin m) ℂ} (hk : k ∈ Kset ε) :
    (k.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det ≠ 0 := by
  intro h
  have := star_det_mul_det s hk
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem hasDerivAt_blockDet (ε : Fin m → Bool) (s : Bool) (X : Matrix (Fin m) (Fin m) ℂ) :
    HasDerivAt (fun t : ℝ => ((NormedSpace.exp ((t : ℂ) • X)).submatrix
        (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).det)
      (∑ a ∈ univ.filter (fun a => ε a = s), X a a) 0 := by
  have h := hasDerivAt_det_of_one
    (fun t : ℝ => (NormedSpace.exp (t • X)).submatrix
        (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1))
    (X.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1))
    (by simp [NormedSpace.exp_zero, Matrix.submatrix_one _ Subtype.val_injective])
    (fun i j => hasDerivAt_exp_entry X i.1 j.1)
  have ht : (X.submatrix (fun x : {a // ε a = s} => x.1) (fun x : {a // ε a = s} => x.1)).trace =
      ∑ a ∈ univ.filter (fun a => ε a = s), X a a := by
    rw [Matrix.trace]
    exact (Finset.sum_subtype _ (fun l => by simp) (fun l => X l l)).symm
  rw [ht] at h
  simpa only [Complex.coe_smul] using h

end ReciprocityTheory.ChartRestriction.DS.S7.InhabA
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFactsA
section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

lemma kfa_mul_Jm_apply (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Y * Jm ε) a b = Y a b * (if ε b then 1 else -1) := by
  unfold Jm
  rw [Matrix.mul_diagonal]

lemma kfa_Jm_mul_apply (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Jm ε * Y) a b = (if ε a then 1 else -1) * Y a b := by
  unfold Jm
  rw [Matrix.diagonal_mul]

lemma kfa_comm_iff_block (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y * Jm ε = Jm ε * Y ↔ IsBlock ε Y := by
  constructor
  · intro h a b hab
    have h1 := congrFun (congrFun h a) b
    rw [kfa_mul_Jm_apply, kfa_Jm_mul_apply] at h1
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>
      simp [ha, hb] at h1 hab <;>
      first
      | exact h1
      | linear_combination h1
      | linear_combination (-1 / 2 : ℂ) * h1
      | linear_combination (1 / 2 : ℂ) * h1
  · intro h
    ext a b
    rw [kfa_mul_Jm_apply, kfa_Jm_mul_apply]
    by_cases hab : ε a = ε b
    · rw [hab]
      ring
    · rw [h a b hab]
      ring

lemma kfa_inK_iff (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    inK ε Y ↔ Yᴴ = -Y ∧ IsBlock ε Y := by
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  unfold inK inG
  rw [← kfa_comm_iff_block]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have h3 : (Yᴴ + Y) * Jm ε = 0 := by
      rw [Matrix.add_mul, h2]
      exact h1
    have h4 := congrArg (· * Jm ε) h3
    simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one, Matrix.zero_mul] at h4
    exact eq_neg_of_add_eq_zero_left h4
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h1, Matrix.neg_mul, h2, neg_add_cancel]

section ExpL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma kfa_exp_cont (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
  first
  | exact NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)
  | fun_prop

lemma kfa_exp_comm {J X : Matrix (Fin n) (Fin n) ℂ} (h : X * J = J * X) :
    NormedSpace.exp X * J = J * NormedSpace.exp X := Commute.exp_left h

end ExpL

lemma kfa_exp_neg_mul (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_left, neg_add_cancel, NormedSpace.exp_zero]

lemma kfa_exp_mul_neg (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_right, add_neg_cancel, NormedSpace.exp_zero]

lemma kfa_exp_conjTranspose {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Yᴴ = -Y) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • Y))ᴴ = NormedSpace.exp (-((t : ℂ) • Y)) := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hY, smul_neg]
  simp only [Complex.star_def, Complex.conj_ofReal]

def kfaUnit (Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  ⟨NormedSpace.exp ((t : ℂ) • Y), NormedSpace.exp (-((t : ℂ) • Y)), kfa_exp_mul_neg _, kfa_exp_neg_mul _⟩

lemma kfa_mem_Kset (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Y) ∈ Kset ε := by
  have hYJ : Y * Jm ε = Jm ε * Y := hY.2
  have hsk : Yᴴ = -Y := ((kfa_inK_iff ε Y).1 hY).1
  unfold Kset
  rw [Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, kfa_exp_conjTranspose hsk,
      kfa_exp_mul_neg]
  · exact kfa_exp_comm (by rw [Matrix.smul_mul, Matrix.mul_smul, hYJ])

lemma kfa_inUJ (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) :
    inUJ ε (NormedSpace.exp ((t : ℂ) • Y)) := by
  have hYJ : Y * Jm ε = Jm ε * Y := hY.2
  have hsk : Yᴴ = -Y := ((kfa_inK_iff ε Y).1 hY).1
  have hc : NormedSpace.exp ((t : ℂ) • Y) * Jm ε = Jm ε * NormedSpace.exp ((t : ℂ) • Y) :=
    kfa_exp_comm (by rw [Matrix.smul_mul, Matrix.mul_smul, hYJ])
  unfold inUJ
  rw [kfa_exp_conjTranspose hsk, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, kfa_exp_neg_mul,
    Matrix.one_mul]

def kfaUJ (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) : UJ ε :=
  ⟨kfaUnit Y t, kfa_inUJ ε hY t⟩

def kfaKG (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) : KG ε :=
  ⟨kfaUJ ε hY t, kfa_mem_Kset ε hY t⟩

lemma kfa_toMK (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) :
    toMK (kfaKG ε hY t) = NormedSpace.exp ((t : ℂ) • Y) := rfl

lemma kfa_continuous (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    Continuous (kfaKG ε hY) := by
  have hu : Continuous (kfaUnit Y) := by
    refine Units.continuous_iff.2 ⟨kfa_exp_cont Y, ?_⟩
    show Continuous fun t : ℝ => NormedSpace.exp (-((t : ℂ) • Y))
    simpa only [smul_neg] using kfa_exp_cont (-Y)
  exact (hu.subtype_mk _).subtype_mk _

lemma kfa_add (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (s t : ℝ) :
    kfaKG ε hY (s + t) = kfaKG ε hY s * kfaKG ε hY t := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • Y) =
    NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • Y)
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

