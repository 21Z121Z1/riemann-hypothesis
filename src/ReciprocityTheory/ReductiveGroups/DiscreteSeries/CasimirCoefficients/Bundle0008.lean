import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0005
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0006
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0004

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecMomentsB
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

lemma dm_swap4 (F : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ k, ∑ l, ∑ a, ∑ b, F k l a b = ∑ a, ∑ b, ∑ k, ∑ l, F k l a b := by
  calc ∑ k, ∑ l, ∑ a, ∑ b, F k l a b = ∑ k, ∑ a, ∑ l, ∑ b, F k l a b :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
    _ = ∑ a, ∑ k, ∑ l, ∑ b, F k l a b := Finset.sum_comm
    _ = ∑ a, ∑ k, ∑ b, ∑ l, F k l a b :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun k _ => Finset.sum_comm))
    _ = ∑ a, ∑ b, ∑ k, ∑ l, F k l a b := Finset.sum_congr rfl (fun a _ => Finset.sum_comm)

variable {U Y : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}

lemma dm_Ye (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (a b : Fin n) :
    Y a b = ∑ j, U a j * (y j : ℂ) * star (U b j) := by
  rw [hY, dm_entry]

lemma dm_herm (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (a b : Fin n) :
    Y b a = star (Y a b) := by
  rw [dm_Ye hY, dm_Ye hY, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [star_mul', star_star]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

lemma trace_diag_conj_eq (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (i : ℕ) :
    ∑ k, (y k : ℂ) * dmK U i k k = ∑ a, dmChi i a * Y a a := by
  simp only [dmK, Finset.mul_sum, dm_Ye hY]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma trace_sq_diag_conj_eq (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (i : ℕ) :
    ∑ k, ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) =
      ∑ a, ∑ b, dmChi i a * dmChi i b * (Y b a * Y a b) := by
  have hL : ∀ k l, (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) =
      ∑ a, ∑ b, (y k : ℂ) * (y l : ℂ) *
        ((dmChi i a * (star (U a k) * U a l)) * (dmChi i b * (star (U b l) * U b k))) := by
    intro k l
    rw [dmK, dmK, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  have hR : ∀ a b, dmChi i a * dmChi i b * (Y b a * Y a b) =
      ∑ k, ∑ l, dmChi i a * dmChi i b *
        ((U b k * (y k : ℂ) * star (U a k)) * (U a l * (y l : ℂ) * star (U b l))) := by
    intro a b
    rw [dm_Ye hY b a, dm_Ye hY a b, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  simp only [hL, hR]
  rw [dm_swap4]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

lemma trace_pow_two_diag_conj (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (i : ℕ) :
    ∑ k, (y k : ℂ) ^ 2 * dmK U i k k = ∑ a, dmChi i a * ∑ b, Y a b * Y b a := by
  have hYY : Y * Y = U * Matrix.diagonal (fun j => (y j : ℂ) ^ 2) * Uᴴ := by
    rw [hY]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, dm_UhU hU, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _),
      Matrix.diagonal_mul_diagonal]
    simp only [sq]
  have hrow : ∀ a, ∑ b, Y a b * Y b a = ∑ k, U a k * (y k : ℂ) ^ 2 * star (U a k) := by
    intro a
    rw [← Matrix.mul_apply, hYY, dm_entry]
  simp only [hrow, dmK, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma dm_hs (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) :
    hs Y = ∑ k, y k ^ 2 := by
  apply Complex.ofReal_injective
  have h3 := trace_pow_two_diag_conj hU hY n
  have hchi : ∀ a : Fin n, dmChi n a = 1 := by intro a; simp [dmChi, a.isLt]
  have hKn : ∀ k, dmK U n k k = 1 := by
    intro k
    have h := congrFun (congrFun (dm_UhU hU) k) k
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    simp only [dmK, hchi, one_mul]
    rw [← h]
    rfl
  simp only [hchi, hKn, one_mul, mul_one] at h3
  rw [hs, Complex.ofReal_sum, Complex.ofReal_sum]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, h3]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.ofReal_pow, dm_normsq, ← dm_herm hY a b]

lemma dm_S (J : Finset (Fin n)) : ((∑ j ∈ J, y j : ℝ) : ℂ) = ∑ k, dmInd J k * (y k : ℂ) := by
  push_cast
  unfold dmInd
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma dm_mean (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hd : ∀ a, Y a a = 0) {i : ℕ} (hi : i ≤ n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * ((∑ j ∈ J.1, y j : ℝ) : ℂ) = 0 := by
  simp only [dm_S, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ k, ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * (y k : ℂ)) =
      (y k : ℂ) * dmK U i k k := by
    intro k
    rw [← sum_minorWeights_indicator hU hi k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    ring
  simp only [h, trace_diag_conj_eq hY, hd, mul_zero, Finset.sum_const_zero]

lemma dm_var (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hd : ∀ a, Y a a = 0) {i : ℕ} (hi : i ≤ n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * ((∑ j ∈ J.1, y j : ℝ) : ℂ) ^ 2 =
      ∑ a, ∑ b, dmChi i a * (1 - dmChi i b) * (Y a b * Y b a) := by
  calc ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * ((∑ j ∈ J.1, y j : ℝ) : ℂ) ^ 2
        = ∑ J : {J : Finset (Fin n) // J.card = i}, ∑ k, ∑ l,
            ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) * ((y k : ℂ) * (y l : ℂ)) := by
          refine Finset.sum_congr rfl fun J _ => ?_
          rw [dm_S, sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
    _ = ∑ k, ∑ J : {J : Finset (Fin n) // J.card = i}, ∑ l,
            ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) * ((y k : ℂ) * (y l : ℂ)) :=
          Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ J : {J : Finset (Fin n) // J.card = i},
            ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) * ((y k : ℂ) * (y l : ℂ)) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k +
            if k = l then dmK U i k k else 0) := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          rw [← dm_m hU hi k l, Finset.mul_sum]
          refine Finset.sum_congr rfl fun J _ => ?_
          ring
    _ = (∑ k, (y k : ℂ) * dmK U i k k) * (∑ l, (y l : ℂ) * dmK U i l l) -
          ∑ k, ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) +
          ∑ k, (y k : ℂ) ^ 2 * dmK U i k k := by
          have hk : ∀ k, ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k +
              if k = l then dmK U i k k else 0) =
              ∑ l, ((y k : ℂ) * dmK U i k k) * ((y l : ℂ) * dmK U i l l) -
              ∑ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) + (y k : ℂ) ^ 2 * dmK U i k k := by
            intro k
            have e : ∀ l, (y k : ℂ) * (y l : ℂ) * (dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k +
                if k = l then dmK U i k k else 0) =
                ((y k : ℂ) * dmK U i k k) * ((y l : ℂ) * dmK U i l l) -
                (y k : ℂ) * (y l : ℂ) * (dmK U i k l * dmK U i l k) +
                if k = l then (y k : ℂ) ^ 2 * dmK U i k k else 0 := by
              intro l
              split_ifs with h
              · subst h; ring
              · ring
            rw [Finset.sum_congr rfl fun l _ => e l, Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.sum_ite_eq]
            simp only [Finset.mem_univ, if_true]
          rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_mul_sum]
    _ = ∑ a, ∑ b, dmChi i a * (1 - dmChi i b) * (Y a b * Y b a) := by
          rw [trace_diag_conj_eq hY, trace_sq_diag_conj_eq hY, trace_pow_two_diag_conj hU hY]
          simp only [hd, mul_zero, Finset.sum_const_zero, zero_sub]
          have e : ∀ a b, dmChi i a * (1 - dmChi i b) * (Y a b * Y b a) =
              dmChi i a * (Y a b * Y b a) - dmChi i a * dmChi i b * (Y b a * Y a b) := by
            intro a b; ring
          simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
          ring

lemma dm_rhs (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) (i : ℕ) :
    ∑ a, ∑ b, dmChi i a * (1 - dmChi i b) * (Y a b * Y b a) =
      ((∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) < i ∧ i ≤ (a : ℕ) then ‖Y a b‖ ^ 2 else 0 : ℝ) : ℂ) := by
  conv_lhs => rw [Finset.sum_comm]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : (b : ℕ) < i <;> by_cases ha : (a : ℕ) < i
  · rw [if_neg (fun h => absurd h.2 (not_le.mpr ha))]; simp [dmChi, hb, ha]
  · rw [if_pos ⟨hb, not_lt.mp ha⟩, dm_normsq, ← dm_herm hY a b]
    simp only [dmChi, if_pos hb, if_neg ha]; ring
  · rw [if_neg (fun h => hb h.1)]; simp [dmChi, hb, ha]
  · rw [if_neg (fun h => hb h.1)]; simp [dmChi, hb, ha]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiCas
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem isUpperTri_one : IsUpperTri (1 : Matrix (Fin n) (Fin n) ℂ) :=
  fun _ _ h => Matrix.one_apply_ne h.ne'

private theorem isLowerTri_one : IsLowerTri (1 : Matrix (Fin n) (Fin n) ℂ) :=
  fun _ _ h => Matrix.one_apply_ne h.ne

private theorem diag_line (a l : Fin n) (t : ℂ) :
    (1 + t • Matrix.single a a (1 : ℂ)) l l = if l = a then 1 + t else 1 := by
  by_cases h : l = a
  · subst h
    simp
  · have : ¬(a = l ∧ a = l) := fun h' => h h'.1.symm
    simp [h, Matrix.single_apply_of_ne (h := this)]

private theorem diag_prod (μ : Fin n → ℤ) (a : Fin n) (t : ℂ) :
    ∏ l, ((if l = a then 1 + t else 1) : ℂ) ^ (-μ l) = (1 + t) ^ (-μ a) := by
  rw [Finset.prod_eq_single a (fun l _ hl => by simp [hl]) (by simp)]
  simp

private theorem hasDerivAt_scale (μ : Fin n → ℤ) (a : Fin n) (c : ℂ) :
    HasDerivAt (fun t : ℂ => (1 + t) ^ (-μ a) * c) (-(μ a : ℂ) * c) 0 := by
  have h1 : HasDerivAt (fun t : ℂ => 1 + t) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℂ)).const_add 1
  have h2 := (hasDerivAt_zpow (-μ a) (1 + 0 : ℂ) (Or.inl (by simp))).comp (0 : ℂ) h1
  simpa [Function.comp_def] using h2.mul_const c

private theorem eventually_ne_line : ∀ᶠ t : ℂ in nhds 0, 1 + t ≠ 0 :=
  (continuous_const.add continuous_id).continuousAt.eventually_ne (by simp)

theorem lhol_phiM_lower (μ : Fin n → ℤ) {a b : Fin n} (hab : b < a) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) : Lhol (Matrix.single a b 1) (PhiM μ) z = 0 := by
  have hconst : ∀ t : ℂ, PhiM μ (z + t • (Matrix.single a b 1 * z)) = PhiM μ z := by
    intro t
    have hc : IsLowerTri (1 + t • Matrix.single a b (1 : ℂ)) := by
      intro i j hij
      have : ¬(a = i ∧ b = j) := fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (hab.trans hij) (lt_irrefl _)
      simp [Matrix.one_apply_ne hij.ne, Matrix.single_apply_of_ne (h := this)]
    have hcd : ∀ l, (1 + t • Matrix.single a b (1 : ℂ)) l l = 1 := by
      intro l
      have : ¬(a = l ∧ b = l) := fun ⟨h1, h2⟩ => hab.ne' (h1.trans h2.symm)
      simp [Matrix.single_apply_of_ne (h := this)]
    obtain ⟨-, h⟩ := phiM_tri_mul μ hc isUpperTri_one (fun l => by rw [hcd l]; exact one_ne_zero)
      (fun l => by simp) hz
    have e : (1 + t • Matrix.single a b (1 : ℂ)) * z * 1 = z + t • (Matrix.single a b 1 * z) := by
      rw [Matrix.mul_one, add_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [← e, h, Finset.prod_eq_one (fun l _ => by rw [hcd l, Matrix.one_apply_eq, mul_one, _root_.one_zpow]),
      one_mul]
  have hd := hasDerivAt_line (differentiableAt_phiM μ hz) (Matrix.single a b 1 * z)
  have h0 : HasDerivAt (fun t : ℂ => PhiM μ (z + t • (Matrix.single a b 1 * z))) 0 0 := by
    simp only [hconst]
    exact hasDerivAt_const _ _
  exact hd.unique h0

theorem rhol_phiM_upper (μ : Fin n → ℤ) {a b : Fin n} (hab : a < b) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) : Rhol (Matrix.single a b 1) (PhiM μ) z = 0 := by
  have hconst : ∀ t : ℂ, PhiM μ (z + t • (z * Matrix.single a b 1)) = PhiM μ z := by
    intro t
    have hc : IsUpperTri (1 + t • Matrix.single a b (1 : ℂ)) := by
      intro i j hij
      have : ¬(a = i ∧ b = j) := fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (hab.trans hij) (lt_irrefl _)
      simp [Matrix.one_apply_ne hij.ne', Matrix.single_apply_of_ne (h := this)]
    have hcd : ∀ l, (1 + t • Matrix.single a b (1 : ℂ)) l l = 1 := by
      intro l
      have : ¬(a = l ∧ b = l) := fun ⟨h1, h2⟩ => hab.ne (h1.trans h2.symm)
      simp [Matrix.single_apply_of_ne (h := this)]
    obtain ⟨-, h⟩ := phiM_tri_mul μ isLowerTri_one hc (fun l => by simp)
      (fun l => by rw [hcd l]; exact one_ne_zero) hz
    have e : 1 * z * (1 + t • Matrix.single a b (1 : ℂ)) = z + t • (z * Matrix.single a b 1) := by
      rw [Matrix.one_mul, mul_add, Matrix.mul_one, Matrix.mul_smul]
    rw [← e, h, Finset.prod_eq_one (fun l _ => by rw [hcd l, Matrix.one_apply_eq, one_mul, _root_.one_zpow]),
      one_mul]
  have hd := hasDerivAt_line (differentiableAt_phiM μ hz) (z * Matrix.single a b 1)
  have h0 : HasDerivAt (fun t : ℂ => PhiM μ (z + t • (z * Matrix.single a b 1))) 0 0 := by
    simp only [hconst]
    exact hasDerivAt_const _ _
  exact hd.unique h0

theorem lhol_phiM_diag (μ : Fin n → ℤ) (a : Fin n) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Lhol (Matrix.single a a 1) (PhiM μ) z = -(μ a : ℂ) * PhiM μ z := by
  have key : ∀ t : ℂ, 1 + t ≠ 0 →
      PhiM μ (z + t • (Matrix.single a a 1 * z)) = (1 + t) ^ (-μ a) * PhiM μ z := by
    intro t ht
    have hc : IsLowerTri (1 + t • Matrix.single a a (1 : ℂ)) := by
      intro i j hij
      have : ¬(a = i ∧ a = j) := fun ⟨h1, h2⟩ => hij.ne (h1.symm.trans h2)
      simp [Matrix.one_apply_ne hij.ne, Matrix.single_apply_of_ne (h := this)]
    obtain ⟨-, h⟩ := phiM_tri_mul μ hc isUpperTri_one
      (fun l => by rw [diag_line]; split_ifs <;> simp [ht]) (fun l => by simp) hz
    have e : (1 + t • Matrix.single a a (1 : ℂ)) * z * 1 = z + t • (Matrix.single a a 1 * z) := by
      rw [Matrix.mul_one, add_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [← e, h]
    congr 1
    simp only [Matrix.one_apply_eq, mul_one, diag_line]
    exact diag_prod μ a t
  have hev : (fun t : ℂ => PhiM μ (z + t • (Matrix.single a a 1 * z))) =ᶠ[nhds 0]
      fun t => (1 + t) ^ (-μ a) * PhiM μ z := by
    filter_upwards [eventually_ne_line] with t ht using key t ht
  have hd := hasDerivAt_line (differentiableAt_phiM μ hz) (Matrix.single a a 1 * z)
  exact hd.unique ((hasDerivAt_scale μ a _).congr_of_eventuallyEq hev)

theorem rhol_phiM_diag (μ : Fin n → ℤ) (a : Fin n) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Rhol (Matrix.single a a 1) (PhiM μ) z = -(μ a : ℂ) * PhiM μ z := by
  have key : ∀ t : ℂ, 1 + t ≠ 0 →
      PhiM μ (z + t • (z * Matrix.single a a 1)) = (1 + t) ^ (-μ a) * PhiM μ z := by
    intro t ht
    have hc : IsUpperTri (1 + t • Matrix.single a a (1 : ℂ)) := by
      intro i j hij
      have : ¬(a = i ∧ a = j) := fun ⟨h1, h2⟩ => hij.ne' (h1.symm.trans h2)
      simp [Matrix.one_apply_ne hij.ne', Matrix.single_apply_of_ne (h := this)]
    obtain ⟨-, h⟩ := phiM_tri_mul μ isLowerTri_one hc (fun l => by simp)
      (fun l => by rw [diag_line]; split_ifs <;> simp [ht]) hz
    have e : 1 * z * (1 + t • Matrix.single a a (1 : ℂ)) = z + t • (z * Matrix.single a a 1) := by
      rw [Matrix.one_mul, mul_add, Matrix.mul_one, Matrix.mul_smul]
    rw [← e, h]
    congr 1
    simp only [Matrix.one_apply_eq, one_mul, diag_line]
    exact diag_prod μ a t
  have hev : (fun t : ℂ => PhiM μ (z + t • (z * Matrix.single a a 1))) =ᶠ[nhds 0]
      fun t => (1 + t) ^ (-μ a) * PhiM μ z := by
    filter_upwards [eventually_ne_line] with t ht using key t ht
  have hd := hasDerivAt_line (differentiableAt_phiM μ hz) (z * Matrix.single a a 1)
  exact hd.unique ((hasDerivAt_scale μ a _).congr_of_eventuallyEq hev)

theorem lhol_lhol_phiM (μ : Fin n → ℤ) (a b : Fin n) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) :
    Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) (PhiM μ)) z =
      ((casCoef μ a b : ℝ) : ℂ) * PhiM μ z := by
  have hO : IsOpen (OmegaSet n) := isOpen_omega
  have hlow : ∀ a b : Fin n, b < a →
      Lhol (Matrix.single b a 1) (Lhol (Matrix.single a b 1) (PhiM μ)) z = 0 := by
    intro a b hab
    have hev : Lhol (Matrix.single a b (1 : ℂ)) (PhiM μ) =ᶠ[nhds z] fun _ => (0 : ℂ) := by
      filter_upwards [hO.mem_nhds hz] with w hw using lhol_phiM_lower μ hab hw
    show fderiv ℂ (Lhol (Matrix.single a b (1 : ℂ)) (PhiM μ)) z _ = 0
    rw [hev.fderiv_eq]
    simp
  have e1 := lhol_phiM_diag μ a hz
  have e2 := lhol_phiM_diag μ b hz
  unfold Lhol at e1 e2
  rcases lt_trichotomy a b with h | rfl | h
  · rw [hlow b a h, casCoef, if_neg h.ne, if_neg (not_lt.mpr h.le)]
    simp
  · have hev : Lhol (Matrix.single a a (1 : ℂ)) (PhiM μ) =ᶠ[nhds z] fun w => -(μ a : ℂ) * PhiM μ w := by
      filter_upwards [hO.mem_nhds hz] with w hw using lhol_phiM_diag μ a hw
    have hf : fderiv ℂ (fun w => -(μ a : ℂ) * PhiM μ w) z = -(μ a : ℂ) • fderiv ℂ (PhiM μ) z :=
      ((differentiableAt_phiM μ hz).hasFDerivAt.const_mul (-(μ a : ℂ))).fderiv
    show fderiv ℂ (Lhol (Matrix.single a a (1 : ℂ)) (PhiM μ)) z _ = _
    rw [hev.fderiv_eq]
    erw [hf]
    rw [_root_.smul_apply, smul_eq_mul, e1, casCoef, if_pos rfl, if_neg (lt_irrefl a)]
    push_cast
    ring
  · rw [lhol_comm (contDiffAt_phiM μ hz) _ _, hlow a b h]
    simp only [Matrix.single_mul_single_same, mul_one, sub_mul, map_sub]
    rw [e1, e2, casCoef, if_neg h.ne', if_pos h]
    push_cast
    ring

theorem casL_phiM (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) : casL (PhiM μ) z = ((casVal lam : ℝ) : ℂ) * PhiM μ z := by
  show ∑ a, ∑ b, Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) (PhiM μ)) z = _
  simp only [lhol_lhol_phiM μ _ _ hz, ← Finset.sum_mul]
  rw [← sum_casCoef μ lam hμ]
  push_cast
  rfl

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

