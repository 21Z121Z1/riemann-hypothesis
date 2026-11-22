import Mathlib

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.DotVecMulVec
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic.TraceLipschitz

theorem cs_pd {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ} (hP : P.PosDef) (a b : ι → ℂ) :
    ‖star a ⬝ᵥ (P *ᵥ b)‖ ^ 2 ≤ (star a ⬝ᵥ (P *ᵥ a)).re * (star b ⬝ᵥ (P *ᵥ b)).re := by
  let _ := P.toSeminormedAddCommGroup hP.posSemidef
  let _ := P.toInnerProductSpace hP.posSemidef
  have cs := inner_mul_inner_self_le (𝕜 := ℂ) a b
  have e1 : (inner ℂ a b : ℂ) = star a ⬝ᵥ (P *ᵥ b) := by
    change (P *ᵥ b) ⬝ᵥ star a = _
    rw [dotProduct_comm]
  have e2 : (inner ℂ b a : ℂ) = star (star a ⬝ᵥ (P *ᵥ b)) := by
    rw [← e1]; exact (inner_conj_symm (𝕜 := ℂ) b a).symm
  have e3 : (inner ℂ a a : ℂ) = star a ⬝ᵥ (P *ᵥ a) := by
    change (P *ᵥ a) ⬝ᵥ star a = _
    rw [dotProduct_comm]
  have e4 : (inner ℂ b b : ℂ) = star b ⬝ᵥ (P *ᵥ b) := by
    change (P *ᵥ b) ⬝ᵥ star b = _
    rw [dotProduct_comm]
  rw [e1, e2, e3, e4, norm_star] at cs
  simp only [RCLike.re_to_complex] at cs
  rw [sq]
  exact cs

theorem dot_vecMulVec {ι : Type*} [Fintype ι] (a z : ι → ℂ) :
    (star z ⬝ᵥ (vecMulVec a (star a) *ᵥ z)).re = ‖star z ⬝ᵥ a‖ ^ 2 := by
  have key : star z ⬝ᵥ (vecMulVec a (star a) *ᵥ z) = (star z ⬝ᵥ a) * star (star z ⬝ᵥ a) := by
    simp only [dotProduct, mulVec, vecMulVec_apply, Pi.star_apply, star_sum, star_mul', star_star]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key, Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem st_lip : ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ,
    |Real.smoothTransition a - Real.smoothTransition b| ≤ K * |a - b| := by
  obtain ⟨K, hK⟩ := (Real.smoothTransition.contDiff (n := 1)).contDiffOn.exists_lipschitzOnWith
    (s := Set.Icc (0 : ℝ) 1) (by simp) (convex_Icc 0 1) isCompact_Icc
  refine ⟨K, K.2, fun a b => ?_⟩
  have hp : ∀ x : ℝ, Real.smoothTransition (max 0 (min x 1)) = Real.smoothTransition x := by
    intro x
    by_cases h0 : x ≤ 0
    · rw [show max 0 (min x 1) = (0 : ℝ) by rw [min_eq_left (by linarith), max_eq_left h0],
        Real.smoothTransition.zero_of_nonpos le_rfl, Real.smoothTransition.zero_of_nonpos h0]
    by_cases h1 : 1 ≤ x
    · rw [show max 0 (min x 1) = (1 : ℝ) by rw [min_eq_right h1, max_eq_right zero_le_one],
        Real.smoothTransition.one_of_one_le le_rfl, Real.smoothTransition.one_of_one_le h1]
    · push Not at h0 h1
      rw [min_eq_left h1.le, max_eq_right h0.le]
  have hm : ∀ x : ℝ, max 0 (min x 1) ∈ Set.Icc (0 : ℝ) 1 := fun x =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  rw [← hp a, ← hp b]
  have h1 := hK.dist_le_mul _ (hm a) _ (hm b)
  rw [Real.dist_eq, Real.dist_eq] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ K.2)
  calc |max 0 (min a 1) - max 0 (min b 1)| ≤ |min a 1 - min b 1| := by
        rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
    _ ≤ |a - b| := by
        have := abs_min_sub_min_le_max a 1 b 1
        simpa using this

theorem sq_diff {ck ch : ℂ} {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4)
    (h1 : ‖ck - ch‖ ^ 2 ≤ 4 * δ ^ 2 * a * b) (h2 : ‖ch‖ ^ 2 ≤ a * b) :
    |‖ck‖ ^ 2 - ‖ch‖ ^ 2| ≤ 5 * δ * (a * b) := by
  have hP : 0 ≤ a * b := mul_nonneg ha hb
  have hxe := abs_norm_sub_norm_le ck ch
  have hd := norm_nonneg (ck - ch)
  have he := norm_nonneg ch
  have hx := norm_nonneg ck
  have hde : ‖ck - ch‖ * ‖ch‖ ≤ 2 * δ * (a * b) := by
    by_contra H
    push Not at H
    have h3 := mul_self_lt_mul_self (by positivity) H
    have h4 := mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    nlinarith
  have h5 : 0 ≤ δ * (1 / 4 - δ) * (a * b) := mul_nonneg (mul_nonneg hδ (sub_nonneg.2 hδ1)) hP
  rw [abs_le] at hxe ⊢
  have u1 := mul_le_mul_of_nonneg_right hxe.2 (add_nonneg hx he)
  have u2 := mul_le_mul_of_nonneg_left (show ‖ck‖ ≤ ‖ch‖ + ‖ck - ch‖ by linarith [hxe.2]) hd
  have l1 := mul_le_mul_of_nonneg_right (show ‖ch‖ - ‖ck‖ ≤ ‖ck - ch‖ by linarith [hxe.1]) (add_nonneg he hx)
  constructor <;> nlinarith

theorem alg_bound {s A δ Zh FinalFormK Sh Sk M m C₁ c : ℝ} (hs : 0 < s) (hm : 0 < m) (hZh : m ≤ Zh)
    (hZk : m ≤ FinalFormK) (hM : M ≤ C₁ * m) (hC₁ : 0 ≤ C₁) (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hSh0 : 0 ≤ Sh) (hSh : Sh ≤ 4 * s * A * Zh) (hS : |Sk - Sh| ≤ M * δ * s * A * c)
    (hZ : |FinalFormK - Zh| ≤ M * δ * c) :
    |(s ^ 2 * FinalFormK)⁻¹ * Sk - (s ^ 2 * Zh)⁻¹ * Sh| ≤ C₁ * (5 * c) * δ / s * A := by
  have hZh0 : 0 < Zh := hm.trans_le hZh
  have hZk0 : 0 < FinalFormK := hm.trans_le hZk
  have hs0 : s ≠ 0 := hs.ne'
  have hZh1 : Zh ≠ 0 := hZh0.ne'
  have hZk1 : FinalFormK ≠ 0 := hZk0.ne'
  have e : (s ^ 2 * FinalFormK)⁻¹ * Sk - (s ^ 2 * Zh)⁻¹ * Sh =
      ((Sk - Sh) * Zh + Sh * (Zh - FinalFormK)) / (s ^ 2 * Zh * FinalFormK) := by
    field_simp <;> ring
  have hden : 0 < s ^ 2 * Zh * FinalFormK := mul_pos (mul_pos (pow_pos hs 2) hZh0) hZk0
  rw [e, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have h1 : |(Sk - Sh) * Zh + Sh * (Zh - FinalFormK)| ≤ |Sk - Sh| * Zh + Sh * |Zh - FinalFormK| := by
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_of_pos hZh0, abs_of_nonneg hSh0]
  have h4 : 0 ≤ 4 * s * A * Zh := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs.le) hA) hZh0.le
  have h2 : |Sk - Sh| * Zh + Sh * |Zh - FinalFormK| ≤
      M * δ * s * A * c * Zh + 4 * s * A * Zh * (M * δ * c) :=
    add_le_add (mul_le_mul_of_nonneg_right hS hZh0.le)
      (mul_le_mul hSh (by rw [abs_sub_comm]; exact hZ) (abs_nonneg _) h4)
  have hMZ : M ≤ C₁ * FinalFormK := hM.trans (mul_le_mul_of_nonneg_left hZk hC₁)
  have hP : 0 ≤ δ * s * A * c * Zh :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hδ hs.le) hA) hc) hZh0.le
  have eR : C₁ * (5 * c) * δ / s * A * (s ^ 2 * Zh * FinalFormK) = 5 * (C₁ * FinalFormK) * (δ * s * A * c * Zh) := by
    field_simp <;> ring
  have eL : M * δ * s * A * c * Zh + 4 * s * A * Zh * (M * δ * c) = 5 * M * (δ * s * A * c * Zh) := by
    ring
  rw [eR]
  refine (h1.trans h2).trans ?_
  rw [eL]
  exact mul_le_mul_of_nonneg_right (by linarith) hP

end PositivityTheory.KB.SmoothPartitionUnityBasic.TraceLipschitz
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GeomQuarter
section
noncomputable section

namespace PositivityTheory.KB.SmoothPartitionUnityBasic.GeometricWindowBounds

theorem geom_quarter (m : ℕ) : ∑ i ∈ Finset.range m, (1 / 4 : ℝ) ^ i ≤ 4 / 3 := by
  have hp : 0 ≤ (1 / 4 : ℝ) ^ m := by positivity
  rw [geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1), div_le_iff_of_neg (by norm_num)]
  linarith

theorem geo_sum (S : Finset ℤ) (n0 : ℤ) (hS : ∀ n ∈ S, n0 ≤ n) :
    ∑ n ∈ S, ((4 : ℝ) ^ n)⁻¹ ≤ 4 / 3 * ((4 : ℝ) ^ n0)⁻¹ := by
  have key : ∀ n ∈ S, ((4 : ℝ) ^ n)⁻¹ = ((4 : ℝ) ^ n0)⁻¹ * (1 / 4 : ℝ) ^ (n - n0).toNat := by
    intro n hn
    have e : n = n0 + ((n - n0).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (sub_nonneg.2 (hS n hn))]; ring
    conv_lhs => rw [e]
    rw [zpow_add₀ (by norm_num), zpow_natCast, mul_inv, one_div, inv_pow]
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hinj : Set.InjOn (fun n : ℤ => (n - n0).toNat) S := by
    intro x hx y hy hxy
    have hxy' : (x - n0).toNat = (y - n0).toNat := hxy
    have h1 := Int.toNat_of_nonneg (sub_nonneg.2 (hS x hx))
    have h2 := Int.toNat_of_nonneg (sub_nonneg.2 (hS y hy))
    omega
  have hsum : ∑ i ∈ S.image (fun n : ℤ => (n - n0).toNat), (1 / 4 : ℝ) ^ i =
      ∑ n ∈ S, (1 / 4 : ℝ) ^ (n - n0).toNat := Finset.sum_image hinj
  rw [← hsum]
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_range_sup_succ _)
    fun _ _ _ => by positivity).trans (geom_quarter _)

theorem geo_rel (T : Finset ℤ) {x0 B : ℝ} (hx0 : 0 < x0) (hB : 0 ≤ B) (f : ℤ → ℝ)
    (hf : ∀ n ∈ T, |f n| ≤ B * ((4 : ℝ) ^ n)⁻¹) (hz : ∀ n ∈ T, f n ≠ 0 → x0 < (4 : ℝ) ^ n) :
    |∑ n ∈ T, f n| ≤ 4 / 3 * B / x0 := by
  rw [← Finset.sum_filter_of_ne hz]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ n ∈ T.filter (fun n => x0 < (4 : ℝ) ^ n), |f n| ≤ B * ((4 : ℝ) ^ n)⁻¹ :=
    fun n hn => hf n (Finset.mem_filter.1 hn).1
  refine (Finset.sum_le_sum hb).trans ?_
  rw [← Finset.mul_sum]
  rcases (T.filter (fun n => x0 < (4 : ℝ) ^ n)).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty, mul_zero]
    exact div_nonneg (mul_nonneg (by norm_num) hB) hx0.le
  · have hmin := (Finset.mem_filter.1 (Finset.min'_mem _ hne)).2
    have h1 := geo_sum (T.filter (fun n => x0 < (4 : ℝ) ^ n)) (Finset.min' _ hne)
      fun n hn => Finset.min'_le _ n hn
    have h2 : ((4 : ℝ) ^ Finset.min' _ hne)⁻¹ ≤ x0⁻¹ := inv_anti₀ hx0 hmin.le
    calc B * ∑ n ∈ T.filter (fun n => x0 < (4 : ℝ) ^ n), ((4 : ℝ) ^ n)⁻¹ ≤ B * (4 / 3 * x0⁻¹) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))) hB
      _ = 4 / 3 * B / x0 := by ring

theorem zpow_window {x0 y0 : ℝ} (hx : 0 < x0) (hy : 0 < y0) :
    ∃ a b : ℤ, ∀ n : ℤ, x0 < (4 : ℝ) ^ n → (4 : ℝ) ^ n < y0 → n ∈ Finset.Icc a b := by
  obtain ⟨a, ha, -⟩ := exists_mem_Ioc_zpow hx (by norm_num : (1 : ℝ) < 4)
  obtain ⟨b, -, hb⟩ := exists_mem_Ioc_zpow hy (by norm_num : (1 : ℝ) < 4)
  refine ⟨a, b, fun n h1 h2 => Finset.mem_Icc.2 ⟨?_, ?_⟩⟩
  · exact ((zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).1 (ha.trans h1)).le
  · have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).1 (h2.trans_le hb)
    omega

theorem fin_alg {δ A R μh lh ld c Cm E D1 D2 : ℝ} (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hc : 0 < c)
    (hlh : 0 < lh) (hld : 0 < ld) (hCm : 0 ≤ Cm) (hE : 0 ≤ E) (hR : μh * A ≤ R) (hμ : c * ld ≤ μh)
    (h1 : |D1| ≤ (5 / 4 * Cm + 1) * δ * (μh * A)) (h2 : |D2| ≤ 4 / 3 * (E * δ * A) / (3 / 16 * lh)) :
    |D1 + D2| ≤ ((5 / 4 * Cm + 1) + 64 / 9 * E / c) * (1 + (lh * ld)⁻¹) * δ * R := by
  have hμ0 : 0 ≤ μh := (mul_pos hc hld).le.trans hμ
  have hR0 : 0 ≤ R := (mul_nonneg hμ0 hA).trans hR
  have hAR : A ≤ R / (c * ld) := by
    rw [le_div_iff₀ (mul_pos hc hld)]
    calc A * (c * ld) = (c * ld) * A := by ring
      _ ≤ μh * A := mul_le_mul_of_nonneg_right hμ hA
      _ ≤ R := hR
  have hlh0 : lh ≠ 0 := hlh.ne'
  have hld0 : ld ≠ 0 := hld.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have e2 : 4 / 3 * (E * δ * A) / (3 / 16 * lh) = 64 / 9 * E * δ * A / lh := by
    field_simp <;> ring
  have h2' : |D2| ≤ 64 / 9 * E / c * δ * R * (lh * ld)⁻¹ := by
    rw [e2] at h2
    refine h2.trans ?_
    rw [div_le_iff₀ hlh]
    have e3 : 64 / 9 * E / c * δ * R * (lh * ld)⁻¹ * lh = 64 / 9 * E * δ * (R / (c * ld)) := by
      field_simp <;> ring
    rw [e3]
    exact mul_le_mul_of_nonneg_left hAR (by positivity)
  have h1' : |D1| ≤ (5 / 4 * Cm + 1) * δ * R := h1.trans (mul_le_mul_of_nonneg_left hR (by positivity))
  have hP : 0 ≤ (lh * ld)⁻¹ := inv_nonneg.2 (mul_pos hlh hld).le
  have hQ : 0 ≤ 64 / 9 * E / c := by positivity
  have hS : 0 ≤ 5 / 4 * Cm + 1 := by positivity
  have hδR : 0 ≤ δ * R := mul_nonneg hδ hR0
  calc |D1 + D2| ≤ |D1| + |D2| := abs_add_le _ _
    _ ≤ (5 / 4 * Cm + 1) * δ * R + 64 / 9 * E / c * δ * R * (lh * ld)⁻¹ := add_le_add h1' h2'
    _ ≤ _ := by
        nlinarith [mul_nonneg hQ hδR, mul_nonneg hS hδR, mul_nonneg (mul_nonneg hQ hδR) hP,
          mul_nonneg (mul_nonneg hS hδR) hP]

end PositivityTheory.KB.SmoothPartitionUnityBasic.GeometricWindowBounds
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.QuadBd
section
open Matrix

namespace PositivityTheory.KB.SmoothPartitionUnityBasic.DerivationBounds

theorem quad_bd (N : ℕ) (V : Matrix (Fin N) (Fin N) ℂ) (M : ℝ) (hM : 0 ≤ M) (hV : ∀ a b, ‖V a b‖ ≤ M)
    (y : Fin N → ℂ) : |(star y ⬝ᵥ (V *ᵥ y)).re| ≤ N * M * (star y ⬝ᵥ y).re := by
  have e1 : star y ⬝ᵥ (V *ᵥ y) = ∑ a, ∑ b, star (y a) * V a b * y b := by
    simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have e2 : (star y ⬝ᵥ y).re = ∑ a, ‖y a‖ ^ 2 := by
    simp only [dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.mul_re]
  rw [e2]
  calc |(star y ⬝ᵥ (V *ᵥ y)).re| ≤ ‖star y ⬝ᵥ (V *ᵥ y)‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ a, ∑ b, ‖y a‖ * M * ‖y b‖ := by
        rw [e1]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul, norm_mul, norm_star]
        gcongr
        exact hV a b
    _ ≤ ∑ a, ∑ b, (M / 2 * ‖y a‖ ^ 2 + M / 2 * ‖y b‖ ^ 2) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        nlinarith [mul_nonneg hM (sq_nonneg (‖y a‖ - ‖y b‖))]
    _ = N * M * ∑ a, ‖y a‖ ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum]
        ring

end PositivityTheory.KB.SmoothPartitionUnityBasic.DerivationBounds
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.ReNonnegPsd
section
open Matrix
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic.BasicAux

set_option linter.unusedSectionVars false

variable {n : Type} [Fintype n] [DecidableEq n]

theorem herm_swap (A : Matrix n n ℂ) (hA : A.IsHermitian) (a b : n → ℂ) :
    star b ⬝ᵥ (A *ᵥ a) = star (star a ⬝ᵥ (A *ᵥ b)) := by
  rw [Matrix.star_dotProduct a (A *ᵥ b), star_star, Matrix.star_mulVec, hA.eq, Matrix.dotProduct_mulVec]

theorem herm_re_swap (A : Matrix n n ℂ) (hA : A.IsHermitian) (a b : n → ℂ) :
    (star b ⬝ᵥ (A *ᵥ a)).re = (star a ⬝ᵥ (A *ᵥ b)).re := by
  rw [herm_swap A hA a b]
  simp

theorem herm_im (A : Matrix n n ℂ) (hA : A.IsHermitian) (a : n → ℂ) :
    (star a ⬝ᵥ (A *ᵥ a)).im = 0 := by
  have h := congrArg Complex.im (herm_swap A hA a a)
  simp at h
  linarith

theorem expand (A : Matrix n n ℂ) (u v : n → ℂ) (s : ℂ) :
    star (u + s • v) ⬝ᵥ (A *ᵥ (u + s • v)) = star u ⬝ᵥ (A *ᵥ u) + s * (star u ⬝ᵥ (A *ᵥ v)) +
      star s * (star v ⬝ᵥ (A *ᵥ u)) + star s * s * (star v ⬝ᵥ (A *ᵥ v)) := by
  simp only [star_add, star_smul, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem re_nonneg_psd {H : Matrix n n ℂ} (hH : H.PosSemidef) (x : n → ℂ) :
    0 ≤ (star x ⬝ᵥ (H *ᵥ x)).re := by
  have := hH.dotProduct_mulVec_nonneg x
  exact (Complex.nonneg_iff.1 this).1

private theorem hermitian_form_add_real_smul_expand (M : Matrix n n ℂ) (hM : M.IsHermitian) (u v : n → ℂ) (s : ℝ) :
    (star (u + (s:ℂ) • v) ⬝ᵥ (M *ᵥ (u + (s:ℂ) • v))).re =
      (star u ⬝ᵥ (M *ᵥ u)).re + 2 * s * (star u ⬝ᵥ (M *ᵥ v)).re + s ^ 2 * (star v ⬝ᵥ (M *ᵥ v)).re := by
  have hs : star (s:ℂ) = s := by simp
  rw [expand, hs, ← Complex.ofReal_mul]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  rw [herm_re_swap M hM u v]
  ring

private theorem re_inner_sq_le_sq_mul_of_hermitian_form_bound (A H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian) (δ : ℝ)
    (hb : ∀ x : n → ℂ, |(star x ⬝ᵥ (A *ᵥ x)).re| ≤ δ * (star x ⬝ᵥ (H *ᵥ x)).re) (u v : n → ℂ) :
    ((star u ⬝ᵥ (A *ᵥ v)).re) ^ 2 ≤ δ ^ 2 * (star u ⬝ᵥ (H *ᵥ u)).re * (star v ⬝ᵥ (H *ᵥ v)).re := by
  have hq : ∀ t : ℝ, 0 ≤ (δ * (star v ⬝ᵥ (H *ᵥ v)).re) * (t * t) + (-2 * (star u ⬝ᵥ (A *ᵥ v)).re) * t
      + δ * (star u ⬝ᵥ (H *ᵥ u)).re := by
    intro t
    have b1 := hb (u + (t:ℂ) • v)
    have b2 := hb (u + ((-t:ℝ):ℂ) • v)
    rw [hermitian_form_add_real_smul_expand A hA, hermitian_form_add_real_smul_expand H hH] at b1
    rw [hermitian_form_add_real_smul_expand A hA, hermitian_form_add_real_smul_expand H hH] at b2
    have c1 := (abs_le.mp b1).2
    have c2 := (abs_le.mp b2).1
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

theorem csq (A H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.PosSemidef) (δ : ℝ) (hδ : 0 ≤ δ)
    (hb : ∀ x : n → ℂ, |(star x ⬝ᵥ (A *ᵥ x)).re| ≤ δ * (star x ⬝ᵥ (H *ᵥ x)).re) (u v : n → ℂ) :
    ‖star u ⬝ᵥ (A *ᵥ v)‖ ^ 2 ≤ δ ^ 2 * (star u ⬝ᵥ (H *ᵥ u)).re * (star v ⬝ᵥ (H *ᵥ v)).re := by
  have hH' := hH.isHermitian
  set c := star u ⬝ᵥ (A *ᵥ v) with hc
  have hu := re_nonneg_psd hH u
  have hv := re_nonneg_psd hH v
  have h := re_inner_sq_le_sq_mul_of_hermitian_form_bound A H hA hH' δ hb u (star c • v)
  have e1 : star u ⬝ᵥ (A *ᵥ (star c • v)) = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, ← hc, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    rfl
  have e2 : star (star c • v) ⬝ᵥ (H *ᵥ (star c • v)) = ((‖c‖ ^ 2 : ℝ) : ℂ) * (star v ⬝ᵥ (H *ᵥ v)) := by
    rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, star_star, smul_eq_mul, smul_eq_mul,
      Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    rw [Complex.star_def]
    ring
  rw [e1, e2, Complex.ofReal_re, Complex.re_ofReal_mul] at h
  have hn : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  rcases hn.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) hu) hv
  · exact le_of_mul_le_mul_left (by nlinarith [h]) hpos

theorem invmono (A B : Matrix n n ℂ) (hA : A.PosDef) (hB : B.PosDef) (c : ℝ) (hc : 0 < c)
    (hle : ∀ x : n → ℂ, c * (star x ⬝ᵥ (A *ᵥ x)).re ≤ (star x ⬝ᵥ (B *ᵥ x)).re) (u : n → ℂ) :
    c * (star u ⬝ᵥ (B⁻¹ *ᵥ u)).re ≤ (star u ⬝ᵥ (A⁻¹ *ᵥ u)).re := by
  have hAh := hA.isHermitian
  have hBu := hB.isUnit
  have hAu := hA.isUnit
  set y := B⁻¹ *ᵥ u with hy
  set z := A⁻¹ *ᵥ u with hz
  have hBy : B *ᵥ y = u := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det B).mp hBu),
      Matrix.one_mulVec]
  have hAz : A *ᵥ z = u := by
    rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hAu),
      Matrix.one_mulVec]
  have e1 : (star u ⬝ᵥ y).re = (star y ⬝ᵥ (B *ᵥ y)).re := by
    rw [hBy, star_dotProduct u y]
    simp
  have e2 : (star z ⬝ᵥ (A *ᵥ z)).re = (star u ⬝ᵥ z).re := by
    rw [hAz, star_dotProduct z u]
    simp
  have e3 : (star y ⬝ᵥ (A *ᵥ z)).re = (star y ⬝ᵥ (B *ᵥ y)).re := by
    rw [hAz, hBy]
  have e4 : (star z ⬝ᵥ (A *ᵥ y)).re = (star y ⬝ᵥ (A *ᵥ z)).re := herm_re_swap A hAh y z
  have hn := re_nonneg_psd hA.posSemidef (z + ((-c:ℝ):ℂ) • y)
  rw [hermitian_form_add_real_smul_expand A hAh z y (-c), e2, e4, e3] at hn
  have hl := hle y
  rw [e1]
  nlinarith [mul_le_mul_of_nonneg_left hl hc.le]

theorem cd_det {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : Type} [Fintype n] [DecidableEq n]
    {k : WithTop ℕ∞} (f : E → Matrix n n ℂ) (hf : ∀ i j, ContDiff ℝ k (fun x => f x i j)) :
    ContDiff ℝ k (fun x => (f x).det) := by
  simp only [Matrix.det_apply]
  refine ContDiff.sum fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact contDiff_const.mul (contDiff_prod fun i _ => hf _ _)

theorem cd_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : Type} [Fintype n] [DecidableEq n]
    {k : WithTop ℕ∞} (f : E → Matrix n n ℂ) (hf : ∀ i j, ContDiff ℝ k (fun x => f x i j)) (i j : n) (x : E)
    (hx : (f x).det ≠ 0) : ContDiffAt ℝ k (fun x => (f x)⁻¹ i j) x := by
  have hdet : ContDiff ℝ k (fun x => (f x).det) := cd_det f hf
  have hadj : ContDiff ℝ k (fun x => (f x).adjugate i j) := by
    simp only [Matrix.adjugate_apply]
    apply cd_det (fun x => (f x).updateRow j (Pi.single i 1))
    intro a b
    by_cases h : a = j <;> simp [Matrix.updateRow_apply, h, contDiff_const, hf]
  have hinv : ContDiffAt ℝ k (fun x => ((f x).det)⁻¹) x := hdet.contDiffAt.inv hx
  have heq : (fun x => (f x)⁻¹ i j) = fun x => ((f x).det)⁻¹ * (f x).adjugate i j := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [heq]
  exact hinv.mul hadj.contDiffAt

end PositivityTheory.KB.SmoothPartitionUnityBasic.BasicAux
end

