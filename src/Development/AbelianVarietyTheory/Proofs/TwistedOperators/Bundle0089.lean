import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0083
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralExpOneSubTwoMulSmul
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

theorem integral_one_sub_two_mul_pow (n : ℕ) :
    ∫ s in (0 : ℝ)..1, (1 - 2 * s) ^ n = (1 - (-1) ^ (n + 1)) / (2 * ((n : ℝ) + 1)) := by
  have h := intervalIntegral.integral_comp_sub_mul (a := (0 : ℝ)) (b := 1)
    (fun x : ℝ => x ^ n) (two_ne_zero' ℝ) 1
  simp only [mul_one, mul_zero, sub_zero] at h
  rw [h, integral_pow, smul_eq_mul]
  have e : (1 : ℝ) - 2 = -1 := by norm_num
  rw [e, one_pow]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

private theorem exp_smul_eq_tsum (A : Type) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (X : A) (t : ℝ) :
    NormedSpace.exp (t • X) = ∑' n : ℕ, t ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n) := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  refine tsum_congr fun n => ?_
  rw [smul_pow, smul_smul, smul_smul, mul_comm]

private theorem norm_one_sub_neg_one_pow_div_le_one (n : ℕ) :
    ‖(1 - (-1 : ℝ) ^ (n + 1)) / (2 * ((n : ℝ) + 1))‖ ≤ 1 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Real.norm_eq_abs, abs_le]
  rcases neg_one_pow_eq_or ℝ (n + 1) with h | h <;> rw [h]
  · norm_num
  · rw [show (1 : ℝ) - -1 = 2 by norm_num, div_mul_eq_div_div, div_self (two_ne_zero' ℝ)]
    have h0 : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    refine ⟨by linarith, (div_le_one hn).2 ?_⟩
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith

theorem integral_exp_one_sub_two_mul_smul (A : Type) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (X : A) :
    ∫ s in (0 : ℝ)..1, NormedSpace.exp ((1 - 2 * s) • X)
      = ∑' k : ℕ, (((2 * k + 1).factorial : ℝ)⁻¹) • X ^ (2 * k) := by
  have hc : Summable fun n : ℕ => ‖((n.factorial : ℝ)⁻¹) • X ^ n‖ :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) X
  simp_rw [exp_smul_eq_tsum]
  rw [intervalIntegral.integral_of_le zero_le_one]
  have hint : ∀ n : ℕ, Integrable (fun s : ℝ => (1 - 2 * s) ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := fun n =>
    (Continuous.intervalIntegrable (by fun_prop) 0 1).1
  have hbound : ∀ n : ℕ, ∫ s in Set.Ioc (0 : ℝ) 1, ‖(1 - 2 * s) ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n)‖
      ≤ ‖((n.factorial : ℝ)⁻¹) • X ^ n‖ := by
    intro n
    rw [← intervalIntegral.integral_of_le zero_le_one]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := ‖((n.factorial : ℝ)⁻¹) • X ^ n‖)
      (f := fun s : ℝ => ‖(1 - 2 * s) ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n)‖) (fun s hs => by
        rw [Set.uIoc_of_le zero_le_one] at hs
        rw [norm_norm, norm_smul, norm_pow]
        refine mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ?_)
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hs.1, hs.2])
    rw [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hsum : Summable fun n : ℕ =>
      ∫ s in Set.Ioc (0 : ℝ) 1, ‖(1 - 2 * s) ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n)‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hbound hc
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  have hterm : ∀ n : ℕ, ∫ s in Set.Ioc (0 : ℝ) 1, (1 - 2 * s) ^ n • (((n.factorial : ℝ)⁻¹) • X ^ n)
      = ((1 - (-1) ^ (n + 1)) / (2 * ((n : ℝ) + 1))) • (((n.factorial : ℝ)⁻¹) • X ^ n) := by
    intro n
    rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_smul_const,
      integral_one_sub_two_mul_pow]
  rw [tsum_congr hterm]
  set g : ℕ → A := fun n => ((1 - (-1) ^ (n + 1)) / (2 * ((n : ℝ) + 1))) •
    (((n.factorial : ℝ)⁻¹) • X ^ n) with hgdef
  have hg : Summable g := Summable.of_norm_bounded hc fun n => by
    rw [hgdef, norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_one_sub_neg_one_pow_div_le_one n)
  have he : Summable fun k : ℕ => g (2 * k) :=
    hg.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  have ho : Summable fun k : ℕ => g (2 * k + 1) :=
    hg.comp_injective ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ)))
  rw [← tsum_even_add_odd he ho]
  have hodd : ∀ k : ℕ, g (2 * k + 1) = 0 := by
    intro k
    rw [hgdef]
    simp only
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]
    norm_num
  have heven : ∀ k : ℕ, g (2 * k) = (((2 * k + 1).factorial : ℝ)⁻¹) • X ^ (2 * k) := by
    intro k
    rw [hgdef]
    simp only
    rw [pow_succ, pow_mul, smul_smul, Nat.factorial_succ]
    congr 1
    push_cast
    have h1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    norm_num
  simp_rw [hodd, heven, tsum_zero, add_zero]

end GlobalTheory.PolarU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KroneckerTransposeMulVecVecM
section
noncomputable section
namespace GlobalTheory.PolarU
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
open scoped Kronecker

section general
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def kronLeftHom (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    Matrix m m ℂ →+* Matrix (m × n) (m × n) ℂ where
  toFun Y := Y ⊗ₖ (1 : Matrix n n ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker _ _ _

def kronRightHom (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] :
    Matrix n n ℂ →+* Matrix (m × n) (m × n) ℂ where
  toFun Z := (1 : Matrix m m ℂ) ⊗ₖ Z
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  map_zero' := Matrix.kronecker_zero _
  map_add' A B := Matrix.kronecker_add _ _ _

theorem continuous_kronLeftHom : Continuous (kronLeftHom m n) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun Y : Matrix m m ℂ => Y i.1 j.1 * (1 : Matrix n n ℂ) i.2 j.2
  exact (continuous_apply_apply i.1 j.1).mul continuous_const

theorem continuous_kronRightHom : Continuous (kronRightHom m n) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun Z : Matrix n n ℂ => (1 : Matrix m m ℂ) i.1 j.1 * Z i.2 j.2
  exact continuous_const.mul (continuous_apply_apply i.2 j.2)

theorem exp_kronecker_one (Y : Matrix m m ℂ) :
    NormedSpace.exp (Y ⊗ₖ (1 : Matrix n n ℂ)) = NormedSpace.exp Y ⊗ₖ (1 : Matrix n n ℂ) := by

  open Norms.Operator in
  exact (NormedSpace.map_exp (kronLeftHom m n) continuous_kronLeftHom Y).symm

theorem exp_one_kronecker (Z : Matrix n n ℂ) :
    NormedSpace.exp ((1 : Matrix m m ℂ) ⊗ₖ Z) = (1 : Matrix m m ℂ) ⊗ₖ NormedSpace.exp Z := by
  open Norms.Operator in
  exact (NormedSpace.map_exp (kronRightHom m n) continuous_kronRightHom Z).symm

end general

theorem kronecker_transpose_mulVec_vecM {p q : ℕ} (A B V : Mat p q) :
    (A ⊗ₖ Bᵀ) *ᵥ vecM V = vecM (A * V * B) := by
  funext ab
  obtain ⟨a, b⟩ := ab
  simp only [vecM, Matrix.mulVec, dotProduct, Matrix.kronecker_apply, Matrix.transpose_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem exp_adMat_mulVec (p q : ℕ) (Y V : Mat p q) :
    NormedSpace.exp (adMat Y) *ᵥ vecM V =
      vecM (NormedSpace.exp Y * V * NormedSpace.exp (-Y)) := by

  have hsplit : adMat Y = Y ⊗ₖ (1 : Mat p q) + (1 : Mat p q) ⊗ₖ (-Yᵀ) := by
    rw [adMat, sub_eq_add_neg]
    congr 1
    ext i j
    simp [Matrix.kronecker_apply, Matrix.kroneckerMap_apply]
  have hcomm : Commute (Y ⊗ₖ (1 : Mat p q)) ((1 : Mat p q) ⊗ₖ (-Yᵀ)) := by
    show _ * _ = _ * _
    simp only [← Matrix.mul_kronecker_mul, one_mul, mul_one]
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, exp_kronecker_one, exp_one_kronecker,
    ← Matrix.mul_kronecker_mul, mul_one, one_mul, ← Matrix.transpose_neg, Matrix.exp_transpose]
  exact kronecker_transpose_mulVec_vecM _ _ _

end GlobalTheory.PolarU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthAddLeOfDisjoint
section
open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm

namespace GlobalTheory.JointHarm

theorem exists_length_of_antitone {α : ℕ → ℕ} (hα : Antitone α) {m : ℕ}
    (hm : ∀ i, m ≤ i → α i = 0) : ∃ t, t ≤ m ∧ ∀ i, α i = 0 ↔ t ≤ i := by
  classical
  have h : ∃ i, α i = 0 := ⟨m, hm m le_rfl⟩
  refine ⟨Nat.find h, Nat.find_min' h (hm m le_rfl), fun i => ⟨fun hi => Nat.find_min' h hi,
    fun hi => ?_⟩⟩
  have := hα hi
  rw [Nat.find_spec h] at this
  exact Nat.le_zero.1 this

theorem length_add_le_of_disjoint {α β : ℕ → ℕ} {t u n : ℕ} (ht : ∀ i, α i = 0 ↔ t ≤ i)
    (hu : ∀ i, β i = 0 ↔ u ≤ i) (htn : t ≤ n) (hun : u ≤ n)
    (h : ∀ i : Fin n, α i = 0 ∨ β i.rev = 0) : t + u ≤ n := by
  by_contra hc
  have h1 := h ⟨t - 1, by omega⟩
  rw [ht, hu, Fin.val_rev] at h1
  simp only at h1
  omega

def posList (α : ℕ → ℕ) (t : ℕ) : List ℤ := (List.range t).map fun i => (α i : ℤ)

def negList (β : ℕ → ℕ) (t : ℕ) : List ℤ := ((List.range t).map fun i => -(β i : ℤ)).reverse

@[simp] theorem length_posList (α : ℕ → ℕ) (t : ℕ) : (posList α t).length = t := by
  simp [posList]

@[simp] theorem length_negList (β : ℕ → ℕ) (t : ℕ) : (negList β t).length = t := by
  simp [negList]

theorem posList_pos {α : ℕ → ℕ} {t : ℕ} (ht : ∀ i, α i = 0 ↔ t ≤ i) :
    ∀ v ∈ posList α t, 0 < v := by
  intro v hv
  simp only [posList, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  have := ht i
  omega

theorem negList_neg {β : ℕ → ℕ} {t : ℕ} (ht : ∀ i, β i = 0 ↔ t ≤ i) :
    ∀ v ∈ negList β t, v < 0 := by
  intro v hv
  simp only [negList, List.mem_reverse, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  have := ht i
  omega

theorem posList_pairwise {α : ℕ → ℕ} (hα : Antitone α) (t : ℕ) :
    (posList α t).Pairwise (· ≥ ·) := by
  rw [posList, List.pairwise_map]
  refine List.pairwise_lt_range.imp fun {a b} h => ?_
  have := hα h.le
  omega

theorem negList_pairwise {β : ℕ → ℕ} (hβ : Antitone β) (t : ℕ) :
    (negList β t).Pairwise (· ≥ ·) := by
  rw [negList, List.pairwise_reverse, List.pairwise_map]
  refine List.pairwise_lt_range.imp fun {a b} h => ?_
  have := hβ h.le
  omega

theorem getD_pad_posList_negList {α β : ℕ → ℕ} {t u n : ℕ} (ht : ∀ i, α i = 0 ↔ t ≤ i)
    (hu : ∀ i, β i = 0 ↔ u ≤ i) (hn : t + u ≤ n) (i : Fin n) :
    (pad (posList α t) (n - (posList α t).length - (negList β u).length) (negList β u)).getD i 0
      = (α i : ℚ) - β i.rev := by
  obtain ⟨i, hi⟩ := i
  simp only [length_posList, length_negList, Fin.val_rev]
  have hlen : i < (pad (posList α t) (n - t - u) (negList β u)).length := by
    simp [pad]; omega
  rw [List.getD_eq_getElem _ _ hlen]
  simp only [pad, List.getElem_map, List.getElem_append, List.length_append, length_posList,
    List.length_replicate, List.getElem_replicate]
  split_ifs with h1 h2
  · rw [(hu _).2 (by omega)]
    simp [posList]
  · rw [(hu _).2 (by omega), (ht _).2 (by omega)]
    simp
  · rw [(ht _).2 (by omega)]
    simp only [negList, List.getElem_reverse, List.getElem_map, List.getElem_range,
      List.length_map, List.length_range]
    have : u - 1 - (i - (t + (n - t - u))) = n - (i + 1) := by omega
    rw [this]
    simp

theorem jointShape_of_fnShape (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ)
    (h : FnShape p q r s μ μ') : JointShape p q r s μ μ' := by
  obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, zα, zβ, zγ, zδ, d1, d2, d3, d4, e1, e2, e3, e4⟩ := h
  obtain ⟨a, ha, ta⟩ := exists_length_of_antitone hα zα
  obtain ⟨b, hb, tb⟩ := exists_length_of_antitone hβ zβ
  obtain ⟨c, hc, tc⟩ := exists_length_of_antitone hγ zγ
  obtain ⟨d, hd, td⟩ := exists_length_of_antitone hδ zδ
  rw [le_min_iff] at ha hb hc hd
  have l1 := length_add_le_of_disjoint ta tb ha.1 hb.1 d1
  have l2 := length_add_le_of_disjoint tc td hc.1 hd.1 d2
  have l3 := length_add_le_of_disjoint ta td ha.2 hd.2 d3
  have l4 := length_add_le_of_disjoint tc tb hc.2 hb.2 d4
  refine ⟨posList α a, negList β b, posList γ c, negList δ d, posList_pos ta, posList_pos tc,
    negList_neg tb, negList_neg td, posList_pairwise hα a, negList_pairwise hβ b,
    posList_pairwise hγ c, negList_pairwise hδ d, by simpa using l1, by simpa using l2,
    by simpa using l3, by simpa using l4, ?_, ?_⟩
  · funext x
    rcases x with i | i
    · exact (e1 i).trans (getD_pad_posList_negList ta tb l1 i).symm
    · exact (e2 i).trans (getD_pad_posList_negList tc td l2 i).symm
  · funext x
    rcases x with i | i
    · exact (e3 i).trans (getD_pad_posList_negList ta td l3 i).symm
    · exact (e4 i).trans (getD_pad_posList_negList tc tb l4 i).symm

end GlobalTheory.JointHarm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolarJacobianBlockDiagConjInvariant
section
noncomputable section
namespace GlobalTheory.PolarU.Conj
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
open scoped Kronecker

theorem conj_pow_of_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] (A A' S : Matrix n n ℂ)
    (h : A * A' = 1) (m : ℕ) : (A * S * A') ^ m = A * S ^ m * A' := by
  have h' : A' * A = 1 := mul_eq_one_comm.mp h
  induction m with
  | zero => simp [h]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    calc A * S ^ m * A' * (A * S * A') = A * S ^ m * (A' * A) * S * A' := by
          simp only [mul_assoc]
      _ = A * (S ^ m * S) * A' := by rw [h', mul_one]; simp only [mul_assoc]

theorem conj_tsum_of_mul_eq_one {n : Type} [Fintype n] [DecidableEq n] (A A' : Matrix n n ℂ)
    (h : A * A' = 1) (f : ℕ → Matrix n n ℂ) :
    A * (∑' m, f m) * A' = ∑' m, A * f m * A' := by
  have h' : A' * A = 1 := mul_eq_one_comm.mp h
  by_cases hf : Summable f
  · rw [← hf.tsum_mul_left A, ← (hf.mul_left A).tsum_mul_right A']
  · have hg : ¬ Summable (fun m => A * f m * A') := by
      intro hg
      apply hf
      have hs := (hg.mul_left A').mul_right A
      refine hs.congr (fun m => ?_)
      rw [show A' * (A * f m * A') * A = (A' * A) * f m * (A' * A) by simp only [mul_assoc],
        h', one_mul, mul_one]
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hg]
    simp

theorem submatrix_mul_of_left {n : Type} [Fintype n] (P : n → Prop) [DecidablePred P]
    (A S : Matrix n n ℂ) (hA : ∀ i j, P i → ¬ P j → A i j = 0) :
    (A * S).submatrix (Subtype.val : {i // P i} → n) (Subtype.val : {i // P i} → n) =
      A.submatrix Subtype.val (Subtype.val : {i // P i} → n) *
        S.submatrix Subtype.val Subtype.val := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have key : ∀ k ∈ (Finset.univ : Finset n), A (i : n) k * S k (j : n) ≠ 0 → P k := by
    intro k _ hk
    by_contra hPk
    exact hk (by rw [hA _ _ i.2 hPk, zero_mul])
  rw [← Finset.sum_filter_of_ne key]
  exact Finset.sum_subtype _ (by simp) (fun k => A (i : n) k * S k (j : n))

theorem submatrix_mul_of_right {n : Type} [Fintype n] (P : n → Prop) [DecidablePred P]
    (S A : Matrix n n ℂ) (hA : ∀ i j, ¬ P i → P j → A i j = 0) :
    (S * A).submatrix (Subtype.val : {i // P i} → n) (Subtype.val : {i // P i} → n) =
      S.submatrix Subtype.val (Subtype.val : {i // P i} → n) *
        A.submatrix Subtype.val Subtype.val := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have key : ∀ k ∈ (Finset.univ : Finset n), S (i : n) k * A k (j : n) ≠ 0 → P k := by
    intro k _ hk
    by_contra hPk
    exact hk (by rw [hA _ _ hPk j.2, mul_zero])
  rw [← Finset.sum_filter_of_ne key]
  exact Finset.sum_subtype _ (by simp) (fun k => S (i : n) k * A k (j : n))

variable {p q : ℕ}

theorem kron_noMix {k l : Mat p q} (hk : IsKC k) (hl : IsKC l) (i j : Ix p q × Ix p q)
    (h : ¬ (sameBlock i.1 i.2 ↔ sameBlock j.1 j.2)) : (k ⊗ₖ lᵀ) i j = 0 := by
  simp only [Matrix.kroneckerMap_apply, Matrix.transpose_apply]
  by_cases h1 : sameBlock i.1 j.1
  · have h2 : ¬ sameBlock j.2 i.2 := by
      intro h2
      apply h
      rcases i with ⟨a | a, b | b⟩ <;> rcases j with ⟨c | c, d | d⟩ <;> simp_all [sameBlock]
    rw [hl _ _ h2, mul_zero]
  · rw [hk _ _ h1, zero_mul]

theorem kron_mul_eq_one {k k' : Mat p q} (h : k * k' = 1) :
    (k ⊗ₖ k'ᵀ) * (k' ⊗ₖ kᵀ) = 1 := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul, h, Matrix.transpose_one,
    Matrix.one_kronecker_one]

theorem adMat_conj {k k' : Mat p q} (h : k * k' = 1) (Y : Mat p q) :
    adMat (k * Y * k') = (k ⊗ₖ k'ᵀ) * adMat Y * (k' ⊗ₖ kᵀ) := by
  have h1 : k'ᵀ * kᵀ = 1 := by rw [← Matrix.transpose_mul, h, Matrix.transpose_one]
  unfold adMat
  rw [Matrix.mul_sub, Matrix.sub_mul]
  simp only [← Matrix.mul_kronecker_mul]
  simp [h, h1, Matrix.transpose_mul, mul_assoc]

theorem sinhcAd_conj {k k' : Mat p q} (h : k * k' = 1) (Y : Mat p q) :
    sinhcAd (k * Y * k') = (k ⊗ₖ k'ᵀ) * sinhcAd Y * (k' ⊗ₖ kᵀ) := by
  unfold sinhcAd
  rw [adMat_conj h, conj_tsum_of_mul_eq_one _ _ (kron_mul_eq_one h)]
  refine tsum_congr (fun j => ?_)
  rw [conj_pow_of_mul_eq_one _ _ _ (kron_mul_eq_one h), Matrix.mul_smul, Matrix.smul_mul]

theorem polJ_conj (p q : ℕ) (k k' Y : Mat p q) (h : k * k' = 1) (hk : IsKC k) (hk' : IsKC k') :
    polJ (k * Y * k') = polJ Y := by
  unfold polJ
  rw [sinhcAd_conj h]
  have hK : ∀ i j : Ix p q × Ix p q, ¬ sameBlock i.1 i.2 → ¬ ¬ sameBlock j.1 j.2 →
      (k ⊗ₖ k'ᵀ) i j = 0 := fun i j hi hj => kron_noMix hk hk' i j (by tauto)
  have hK' : ∀ i j : Ix p q × Ix p q, ¬ ¬ sameBlock i.1 i.2 → ¬ sameBlock j.1 j.2 →
      (k' ⊗ₖ kᵀ) i j = 0 := fun i j hi hj => kron_noMix hk' hk i j (by tauto)
  have e1 : ((k ⊗ₖ k'ᵀ) * sinhcAd Y * (k' ⊗ₖ kᵀ)).submatrix (Subtype.val : PIx p q → _)
      Subtype.val = ((k ⊗ₖ k'ᵀ) * sinhcAd Y).submatrix (Subtype.val : PIx p q → _) Subtype.val *
        (k' ⊗ₖ kᵀ).submatrix Subtype.val Subtype.val :=
    submatrix_mul_of_right (fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2) _ _ hK'
  have e2 : ((k ⊗ₖ k'ᵀ) * sinhcAd Y).submatrix (Subtype.val : PIx p q → _) Subtype.val =
      (k ⊗ₖ k'ᵀ).submatrix (Subtype.val : PIx p q → _) Subtype.val *
        (sinhcAd Y).submatrix Subtype.val Subtype.val :=
    submatrix_mul_of_left (fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2) _ _ hK
  have e3 : ((k ⊗ₖ k'ᵀ) * (k' ⊗ₖ kᵀ)).submatrix (Subtype.val : PIx p q → _) Subtype.val =
      (k ⊗ₖ k'ᵀ).submatrix (Subtype.val : PIx p q → _) Subtype.val *
        (k' ⊗ₖ kᵀ).submatrix Subtype.val Subtype.val :=
    submatrix_mul_of_left (fun ab : Ix p q × Ix p q => ¬ sameBlock ab.1 ab.2) _ _ hK
  rw [kron_mul_eq_one h, Matrix.submatrix_one _ Subtype.val_injective] at e3
  have e5 := congrArg Matrix.det e3
  rw [Matrix.det_one, Matrix.det_mul] at e5
  rw [e1, e2, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← e5, one_mul]

end GlobalTheory.PolarU.Conj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SinhcAdMulVecOfAdSqEigen
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU

open scoped Matrix.Norms.Operator in

theorem summable_sinhc_series_mat {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    Summable fun k : ℕ => (((2 * k + 1).factorial : ℂ)⁻¹) • A ^ (2 * k) := by
  have h0 : Summable fun m : ℕ => ‖((m.factorial : ℂ)⁻¹) • A ^ m‖ :=
    NormedSpace.norm_expSeries_summable' A
  have h1 : Summable fun k : ℕ => ‖(((2 * k).factorial : ℂ)⁻¹) • A ^ (2 * k)‖ :=
    h0.comp_injective (i := fun k : ℕ => 2 * k) (fun a b h => by simpa using h)
  refine Summable.of_norm_bounded h1 fun k => ?_
  rw [norm_smul, norm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
  refine inv_anti₀ (by exact_mod_cast Nat.factorial_pos _) ?_
  exact_mod_cast Nat.factorial_le (Nat.le_succ _)

theorem hasSum_shc_series (x : ℝ) :
    HasSum (fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k)) (shc x) := by
  unfold shc
  split_ifs with hx
  · subst hx
    have := hasSum_single (f := fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * (0 : ℝ) ^ (2 * k)) 0
      (fun k hk => by simp [hk])
    simpa using this
  · have h := (Real.hasSum_sinh x).div_const x
    have e : (fun k : ℕ => (((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k))
        = fun k : ℕ => x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) / x := by
      funext k
      rw [pow_succ]
      field_simp
    rw [e]
    exact h

theorem sinhcAd_mulVec_of_sq_eigen : ∀ (p q : ℕ) (Y : Mat p q) (v : Ix p q × Ix p q → ℂ) (x : ℝ),
    (adMat Y ^ 2) *ᵥ v = ((x : ℂ) ^ 2) • v → sinhcAd Y *ᵥ v = ((shc x : ℝ) : ℂ) • v := by
  intro p q Y v x h
  have hk : ∀ k : ℕ, (adMat Y ^ (2 * k)) *ᵥ v = ((x : ℂ) ^ (2 * k)) • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [mul_add, mul_one, pow_add, pow_add, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih,
        smul_smul, mul_comm]
  let L : Matrix (Ix p q × Ix p q) (Ix p q × Ix p q) ℂ →+ (Ix p q × Ix p q → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_zero' := Matrix.zero_mulVec v
      map_add' := fun M N => Matrix.add_mulVec M N v }
  have hL : Continuous L := continuous_id.matrix_mulVec continuous_const
  have h1 := (summable_sinhc_series_mat (adMat Y)).hasSum.map L hL
  have h2 : HasSum (fun k : ℕ => (((((2 * k + 1).factorial : ℝ)⁻¹) * x ^ (2 * k) : ℝ) : ℂ) • v)
      (((shc x : ℝ) : ℂ) • v) := (Complex.hasSum_ofReal.2 (hasSum_shc_series x)).smul_const v
  refine h1.unique ?_
  convert h2 using 1
  funext k
  show (_ • _) *ᵥ v = _
  rw [Matrix.smul_mulVec, hk, smul_smul]
  push_cast
  rfl

end GlobalTheory.PolarU
end

