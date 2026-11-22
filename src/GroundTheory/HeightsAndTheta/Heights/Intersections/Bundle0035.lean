import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagMinorsTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

theorem card_pivotCols_ge {n : ℕ} (a : Fin (n - 1)) :
    Fintype.card {b : Fin n // (a : ℕ) ≤ b} = n - a := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun b : Fin n => (a : ℕ) ≤ b) = Finset.Ici (Fin.castLE (Nat.sub_le n 1) a) := by
    ext b; simp [Fin.le_def]
  rw [this, Fin.card_Ici]
  simp

theorem card_pivotIndex (n : ℕ) :
    Fintype.card (Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b}) = flagDim n + (n - 1) := by
  rw [Fintype.card_sigma]
  simp_rw [card_pivotCols_ge]
  rw [Fin.sum_univ_eq_sum_range (fun i => n - i) (n - 1)]
  rcases n with _ | m
  · simp [flagDim]
  · simp only [Nat.add_sub_cancel, flagDim]
    have hr : ∑ i ∈ Finset.range m, (m + 1 - i) = ∑ i ∈ Finset.range m, (i + 2) := by
      rw [← Finset.sum_range_reflect (fun i => i + 2) m]
      exact Finset.sum_congr rfl fun i hi => by simp at hi; omega
    rw [hr, Finset.sum_add_distrib]
    have h2 := Finset.sum_range_id_mul_two m
    have h3 : (m + 1) * m = (∑ i ∈ Finset.range m, i) * 2 + 2 * m := by
      rw [h2]; rcases m with _ | k
      · simp
      · simp only [Nat.add_sub_cancel]; ring
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [h3]
    omega

theorem det_mem_subring {R : Type} [CommRing R] {m : Type} [Fintype m] [DecidableEq m] (S : Subring R)
    (M : Matrix m m R) (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine S.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (S.prod_mem fun i _ => h _ _) _

section

variable (F : Type) [Field F] (n : ℕ)

def flagMinorAlg : Subalgebra F (MvPolynomial (Fin n × Fin n) F) :=
  Algebra.adjoin F (Set.range fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat F n) q.1 q.2)

abbrev PivotIdx := Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b}

theorem pivotMinor_mem_flagMinorAlg (q : PivotIdx n) : pivotMinor (genMat F n) q.1 q.2.1 ∈ flagMinorAlg F n := by
  rw [pivotMinor_eq_flagMinor _ q.1 q.2.1 q.2.2]
  exact Algebra.subset_adjoin ⟨⟨q.1, _⟩, rfl⟩

def pivotElt (q : PivotIdx n) : flagMinorAlg F n := ⟨_, pivotMinor_mem_flagMinorAlg F n q⟩

def pivotAlg : Subalgebra F (flagMinorAlg F n) := Algebra.adjoin F (Set.range (pivotElt F n))

def pivotAlgP : Subalgebra F (MvPolynomial (Fin n × Fin n) F) :=
  Algebra.adjoin F (Set.range fun q : PivotIdx n => pivotMinor (genMat F n) q.1 q.2.1)

theorem pivotAlgP_eq_map : pivotAlgP F n = (pivotAlg F n).map (flagMinorAlg F n).val := by
  rw [pivotAlg, AlgHom.map_adjoin, ← Set.range_comp]
  rfl

theorem leadMinor_mem_pivotAlgP (a : Fin (n - 1)) : leadMinor (genMat F n) a ∈ pivotAlgP F n :=
  Algebra.subset_adjoin ⟨⟨a, ⟨Fin.castLE (Nat.sub_le n 1) a, le_rfl⟩⟩, rfl⟩

theorem pivotMatrix_mem_pivotAlgP (j : Fin (n - 1)) (r : Fin (j + 1)) (b : Fin n) :
    pivotMatrix (genMat F n) (Fin.castLE (by have := j.2; omega) r) b ∈ pivotAlgP F n := by
  have hr : (r : ℕ) < n - 1 := by have := j.2; have := r.2; omega
  simp only [pivotMatrix, Matrix.of_apply, Fin.val_castLE, dif_pos hr]
  by_cases h : (r : ℕ) ≤ b
  · exact Algebra.subset_adjoin ⟨⟨⟨r, hr⟩, ⟨b, h⟩⟩, rfl⟩
  · rw [pivotMinor_eq_zero _ ⟨r, hr⟩ b (by simp only; omega)]
    exact zero_mem _

theorem exists_of_mem_pivotAlgP {y : MvPolynomial (Fin n × Fin n) F} (hy : y ∈ pivotAlgP F n) :
    ∃ z : pivotAlg F n, ((z : flagMinorAlg F n) : MvPolynomial (Fin n × Fin n) F) = y := by
  rw [pivotAlgP_eq_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact ⟨⟨z, hz⟩, rfl⟩

theorem isAlgebraic_flagMinor (h₁ : FlagPivotIdentity.Statement)
    (hne : ∀ a : Fin (n - 1), leadMinor (genMat F n) a ≠ 0) (q : Σ j, PluckerBlocks n n j) :
    IsAlgebraic (pivotAlg F n)
      (⟨flagMinor (genMat F n) q.1 q.2, Algebra.subset_adjoin ⟨q, rfl⟩⟩ : flagMinorAlg F n) := by
  obtain ⟨j, S⟩ := q
  obtain ⟨c, hc⟩ := exists_of_mem_pivotAlgP F n (y := ∏ a ∈ Finset.Iic j, leadMinor (genMat F n) a)
    (Subalgebra.prod_mem _ fun a _ => leadMinor_mem_pivotAlgP F n a)
  obtain ⟨d, hd⟩ := exists_of_mem_pivotAlgP F n
    (y := leadMinor (genMat F n) j * flagMinor (pivotMatrix (genMat F n)) j S)
    (Subalgebra.mul_mem _ (leadMinor_mem_pivotAlgP F n j)
      (det_mem_subring (pivotAlgP F n).toSubring _ fun r s => pivotMatrix_mem_pivotAlgP F n j r _))
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact (Finset.prod_ne_zero_iff.mpr fun a _ => hne a) hc.symm
  have h1 : c • (⟨flagMinor (genMat F n) j S, Algebra.subset_adjoin ⟨⟨j, S⟩, rfl⟩⟩ : flagMinorAlg F n) =
      algebraMap (pivotAlg F n) (flagMinorAlg F n) d := by
    apply Subtype.val_injective
    change ((c : flagMinorAlg F n) : MvPolynomial (Fin n × Fin n) F) * flagMinor (genMat F n) j S =
      ((d : flagMinorAlg F n) : MvPolynomial (Fin n × Fin n) F)
    rw [hc, hd, ← h₁ (MvPolynomial (Fin n × Fin n) F) n (genMat F n) j S, mul_comm]
  exact IsAlgebraic.of_smul (mem_nonZeroDivisors_of_ne_zero hc0) (h1 ▸ isAlgebraic_algebraMap d)

theorem isAlgebraic_pivotAlg (h₁ : FlagPivotIdentity.Statement)
    (hne : ∀ a : Fin (n - 1), leadMinor (genMat F n) a ≠ 0) :
    Algebra.IsAlgebraic (pivotAlg F n) (flagMinorAlg F n) := by
  constructor
  rintro ⟨y, hy⟩
  induction hy using Algebra.adjoin_induction with
  | mem y hy' =>
    obtain ⟨q, rfl⟩ := hy'
    exact isAlgebraic_flagMinor F n h₁ hne q
  | algebraMap r => exact isAlgebraic_algebraMap (algebraMap F (pivotAlg F n) r)
  | add y z hy hz ihy ihz =>
    have e : (⟨y + z, add_mem hy hz⟩ : flagMinorAlg F n) = ⟨y, hy⟩ + ⟨z, hz⟩ := Subtype.ext rfl
    rw [e]
    exact ihy.add ihz
  | mul y z hy hz ihy ihz =>
    have e : (⟨y * z, mul_mem hy hz⟩ : flagMinorAlg F n) = ⟨y, hy⟩ * ⟨z, hz⟩ := Subtype.ext rfl
    rw [e]
    exact ihy.mul ihz

end

theorem FlagMinorsTrdeg.proof (h₁ : FlagPivotIdentity.Statement) (h₂ : FlagPivotAlgIndep.Statement) :
    FlagMinorsTrdeg.Statement := by
  intro F _ n
  have hx : AlgebraicIndependent F (pivotElt F n) :=
    AlgebraicIndependent.of_comp (flagMinorAlg F n).val (h₂ F n)
  have hne : ∀ a : Fin (n - 1), leadMinor (genMat F n) a ≠ 0 := fun a h =>
    hx.ne_zero ⟨a, ⟨Fin.castLE (Nat.sub_le n 1) a, le_rfl⟩⟩ (Subtype.ext h)
  have tb := hx.isTranscendenceBasis_iff_isAlgebraic.mpr (isAlgebraic_pivotAlg F n h₁ hne)
  have e := tb.cardinalMk_eq_trdeg
  rw [Cardinal.mk_fintype, card_pivotIndex] at e
  exact e.symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagPivotAlgIndep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

namespace FlagPivotAlgIndep

variable (F : Type) [Field F] (n : ℕ)

abbrev genFrac (p : Fin n × Fin n) : FractionRing (MvPolynomial (Fin n × Fin n) F) :=
  algebraMap (MvPolynomial (Fin n × Fin n) F) _ (X p)

theorem genFrac_ne_zero (p : Fin n × Fin n) : genFrac F n p ≠ 0 := by
  simp only [genFrac, ne_eq, IsFractionRing.to_map_eq_zero_iff]
  exact X_ne_zero p

def spec (p : Fin n × Fin n) : FractionRing (MvPolynomial (Fin n × Fin n) F) :=
  if (p.2 : ℕ) < p.1 then 0
  else if h : (p.1 : ℕ) = 0 then genFrac F n p
  else genFrac F n p / genFrac F n (⟨p.1 - 1, by omega⟩, ⟨p.1 - 1, by omega⟩)

theorem prod_spec (m : ℕ) (hm : m < n) (c : Fin n) (hc : m ≤ (c : ℕ)) :
    (∏ i : Fin m, spec F n (⟨i, by omega⟩, ⟨i, by omega⟩)) * spec F n (⟨m, hm⟩, c) = genFrac F n (⟨m, hm⟩, c) := by
  induction m generalizing c with
  | zero => simp [spec]
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega) ⟨m, by omega⟩ le_rfl]
    have e : (⟨m + 1 - 1, by omega⟩ : Fin n) = ⟨m, by omega⟩ := Fin.ext (by simp)
    simp only [spec, show ¬ ((c : ℕ) < m + 1) by omega, if_false, show m + 1 ≠ 0 by omega, dif_neg, not_false_eq_true, e]
    exact mul_div_cancel₀ _ (genFrac_ne_zero F n _)

theorem spec_pivotMinor (a : Fin (n - 1)) (b : Fin n) (hab : (a : ℕ) ≤ b) :
    aeval (spec F n) (pivotMinor (genMat F n) a b) = genFrac F n (Fin.castLE (Nat.sub_le n 1) a, b) := by
  have ha : (a : ℕ) < n := by have := a.2; omega
  unfold pivotMinor
  rw [AlgHom.map_det, Matrix.det_of_isUpperTriangular]
  · rw [Fin.prod_univ_castSucc]
    refine Eq.trans ?_ (prod_spec F n a ha b hab)
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [AlgHom.mapMatrix_apply, Matrix.map_apply, genMat, pivotCols, aeval_X]
      rfl
    · simp [AlgHom.mapMatrix_apply, Matrix.map_apply, genMat, pivotCols, aeval_X]
      rfl
  · intro i j hji
    have hji' : (j : ℕ) < i := hji
    have hj : (j : ℕ) < a := by have := i.2; omega
    simp [AlgHom.mapMatrix_apply, Matrix.map_apply, genMat, pivotCols, aeval_X, spec, hj, hji']

theorem proof : FlagPivotAlgIndep.Statement := by
  intro F _ n
  refine AlgebraicIndependent.of_comp (aeval (spec F n)) ?_
  have hfun : ⇑(aeval (spec F n)) ∘
        (fun q : Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b} => pivotMinor (genMat F n) q.1 q.2.1) =
      ⇑(IsScalarTower.toAlgHom F (MvPolynomial (Fin n × Fin n) F) (FractionRing (MvPolynomial (Fin n × Fin n) F))) ∘
        ((X : Fin n × Fin n → MvPolynomial (Fin n × Fin n) F) ∘
          fun q : Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b} => (Fin.castLE (Nat.sub_le n 1) q.1, q.2.1)) := by
    funext q
    exact spec_pivotMinor F n q.1 q.2.1 q.2.2
  rw [hfun]
  refine AlgebraicIndependent.map' ?_ (IsFractionRing.injective _ _)
  refine (algebraicIndependent_X (Fin n × Fin n) F).comp _ ?_
  rintro ⟨a, b, hb⟩ ⟨a', b', hb'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : a = a' := Fin.ext (by simpa using congrArg Fin.val h1)
  subst h1' h2
  rfl

end FlagPivotAlgIndep

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagPivotIdentity
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace FlagPivotIdentity

variable {R : Type} [CommRing R] {n : ℕ}

def leadDet (M : Matrix (Fin n) (Fin n) R) (k : ℕ) : R :=
  if h : k ≤ n then (M.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0

def pivotCof (M : Matrix (Fin n) (Fin n) R) {a : ℕ} (ha : a + 1 ≤ n) (i : Fin (a + 1)) : R :=
  (-1) ^ ((i : ℕ) + a) * (M.submatrix (Fin.castLE ha ∘ i.succAbove) (Fin.castLE (by omega))).det

theorem pivotMinor_eq_sum (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) (b : Fin n) :
    pivotMinor M a b = ∑ i : Fin (a + 1),
      pivotCof M (a := a) (by have := a.2; omega) i * M (Fin.castLE (by have := a.2; omega) i) b := by
  unfold pivotMinor
  rw [Matrix.det_succ_column _ (Fin.last a)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcol : pivotCols a b ∘ (Fin.last (a : ℕ)).succAbove = Fin.castLE (by have := a.2; omega) := by
    funext c
    rw [Fin.succAbove_last]
    ext
    simp [pivotCols]
  have hlast : pivotCols a b (Fin.last a) = b := by simp [pivotCols]
  simp only [pivotCof, Matrix.submatrix_apply, Matrix.submatrix_submatrix, Fin.val_last, hlast, hcol]
  ring

def pivotCoeff (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) : Matrix (Fin (j + 1)) (Fin (j + 1)) R :=
  Matrix.of fun a i =>
    if h : (i : ℕ) ≤ a then pivotCof M (a := a) (by have := j.2; have := a.2; omega) ⟨i, by omega⟩ else 0

theorem sum_castLE {m k : ℕ} (h : k ≤ m) (f : Fin m → R) (hf : ∀ i : Fin m, k ≤ (i : ℕ) → f i = 0) :
    ∑ i : Fin k, f (Fin.castLE h i) = ∑ i : Fin m, f i := by
  have e : ∑ i : Fin k, f (Fin.castLE h i) = ∑ i ∈ Finset.univ.map (Fin.castLEEmb h), f i := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hf i ?_
  by_contra hlt
  push Not at hlt
  exact hi (Finset.mem_map.2 ⟨⟨i, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem pivotMatrix_rows (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) {m : ℕ} (e : Fin m → Fin n) :
    (pivotMatrix M).submatrix (Fin.castLE (n := (j : ℕ) + 1) (by have := j.2; omega)) e =
      pivotCoeff M j * M.submatrix (Fin.castLE (n := (j : ℕ) + 1) (by have := j.2; omega)) e := by
  ext a b
  have ha : (a : ℕ) < n - 1 := by have := j.2; have := a.2; omega
  rw [Matrix.mul_apply]
  simp only [Matrix.submatrix_apply, pivotMatrix, Matrix.of_apply, Fin.val_castLE, dif_pos ha]
  rw [pivotMinor_eq_sum M ⟨a, ha⟩ (e b)]
  rw [← sum_castLE (m := (j : ℕ) + 1) (k := (a : ℕ) + 1) (Nat.succ_le_of_lt a.2)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi : ((Fin.castLE (n := (a : ℕ) + 1) (m := (j : ℕ) + 1) (Nat.succ_le_of_lt a.2) i) : ℕ) ≤ a :=
      Nat.lt_succ_iff.mp i.2
    simp only [pivotCoeff, Matrix.of_apply]
    rw [dif_pos hi]
    rfl
  · intro i hi
    have : ¬ ((i : ℕ) ≤ a) := by omega
    simp only [pivotCoeff, Matrix.of_apply]
    rw [dif_neg this, zero_mul]

theorem pivotCoeff_isLowerTriangular (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) :
    (pivotCoeff M j).IsLowerTriangular := by
  intro a i hai
  have hai' : (a : ℕ) < i := OrderDual.toDual_lt_toDual.mp hai
  have : ¬ ((i : ℕ) ≤ a) := by omega
  simp only [pivotCoeff, Matrix.of_apply, dif_neg this]

theorem pivotCoeff_diag (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) (a : Fin (j + 1)) :
    pivotCoeff M j a a = leadDet M a := by
  have ha : (a : ℕ) ≤ n := by have := j.2; have := a.2; omega
  simp only [pivotCoeff, Matrix.of_apply, dif_pos le_rfl, pivotCof, leadDet, dif_pos ha]
  have hl : (⟨a, Nat.lt_succ_self _⟩ : Fin ((a : ℕ) + 1)) = Fin.last a := rfl
  rw [hl, Fin.succAbove_last, Even.neg_one_pow ⟨a, rfl⟩, one_mul]
  rfl

theorem leadMinor_eq (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) :
    leadMinor M a = leadDet M (a + 1) := by
  have h : (a : ℕ) + 1 ≤ n := by have := a.2; omega
  unfold leadMinor pivotMinor leadDet
  rw [dif_pos h]
  congr 2
  funext c
  rcases c with ⟨c, hc⟩
  ext
  simp only [pivotCols, Fin.castLE_mk]
  split_ifs <;> (simp; try omega)

theorem leadDet_zero (M : Matrix (Fin n) (Fin n) R) : leadDet M 0 = 1 := by
  simp [leadDet]

theorem proof : FlagPivotIdentity.Statement := by
  intro R _ n M j S
  have hP : flagMinor (pivotMatrix M) j S =
      (∏ k ∈ Finset.range j, leadDet M (k + 1)) * flagMinor M j S := by
    unfold flagMinor
    rw [pivotMatrix_rows, Matrix.det_mul,
      Matrix.det_of_isLowerTriangular _ (pivotCoeff_isLowerTriangular M j)]
    simp only [pivotCoeff_diag]
    rw [Fin.prod_univ_eq_prod_range (fun k => leadDet M k), Finset.prod_range_succ', leadDet_zero, mul_one]
  have hI : ∏ a ∈ Finset.Iic j, leadMinor M a = ∏ k ∈ Finset.range (j + 1), leadDet M (k + 1) := by
    simp only [leadMinor_eq]
    have e := Finset.prod_map (Finset.Iic j) Fin.valEmbedding (fun k => leadDet M (k + 1))
    rw [Fin.map_valEmbedding_Iic] at e
    rw [← show (Finset.Iic (j : ℕ)) = Finset.range (j + 1) by ext; simp, e]
    rfl
  rw [hP, hI, Finset.prod_range_succ, leadMinor_eq]
  ring

end FlagPivotIdentity

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFIntZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def eulerDirs {n : ℕ} (F : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y : Fin n → ℂ) : Submodule ℂ (Fin n → ℂ) where
  carrier := {x | ∃ c : K → ℂ, fderiv ℂ F y x = bsmul c (F y)}
  add_mem' := by
    rintro x x' ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨c + c', by rw [map_add, hc, hc']; funext p; simp [bsmul, add_mul]⟩
  zero_mem' := ⟨0, by rw [map_zero]; funext p; simp [bsmul]⟩
  smul_mem' := by
    rintro a x ⟨c, hc⟩
    exact ⟨a • c, by rw [map_smul, hc]; funext p; simp [bsmul, mul_assoc]⟩

theorem eulerDirs_finrank (hR : pointFormRank_holds.Statement) {Q : Ideal (MRing ι)} {d n : ℕ} (hQ : IsArithVar Q d)
    {F : (Fin n → ℂ) → (Σ k, ι k) → ℂ} {y : Fin n → ℂ} (hF : AnalyticAt ℂ F y)
    (hFQ : ∀ᶠ y' in 𝓝 y, F y' ∈ mcPts Q) : n < Module.finrank ℂ (eulerDirs F y) + d := by
  by_contra hlt
  push Not at hlt
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (eulerDirs F y)
  have hsum := Submodule.finrank_add_eq_of_isCompl hU
  rw [Module.finrank_fin_fun] at hsum
  have hdm : d ≤ Module.finrank ℂ U := by omega
  set bU := Module.finBasis ℂ U
  let Mlin : (Fin (Module.finrank ℂ U) → ℂ) →ₗ[ℂ] (Fin n → ℂ) := U.subtype ∘ₗ bU.equivFun.symm.toLinearMap
  let M : (Fin (Module.finrank ℂ U) → ℂ) →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap Mlin
  have hMU : ∀ x, M x ∈ U := fun x => Submodule.coe_mem (bU.equivFun.symm x)
  have hMinj : Function.Injective M := fun a b h => bU.equivFun.symm.injective (Subtype.ext h)
  have hA : HasFDerivAt (fun y' => y + M y') M 0 := (M.hasFDerivAt).const_add y
  have hy : y + M 0 = y := by rw [map_zero, add_zero]
  have hF' : AnalyticAt ℂ F (y + M 0) := by rw [hy]; exact hF
  have hGa : AnalyticAt ℂ (fun y' => F (y + M y')) 0 :=
    hF'.comp (f := fun y' => y + M y') (analyticAt_const.add (M.analyticAt 0))
  have hGQ : ∀ᶠ y' in 𝓝 (0 : Fin (Module.finrank ℂ U) → ℂ), F (y + M y') ∈ mcPts Q := by
    have ht : Tendsto (fun y' => y + M y') (𝓝 0) (𝓝 y) := by
      have := hA.continuousAt.tendsto
      rwa [hy] at this
    exact ht.eventually hFQ
  obtain ⟨x, hx, c, hxc⟩ := hR K ι Q d _ (fun y' => F (y + M y')) 0 hQ hdm hGa hGQ
  have hFd : HasFDerivAt F (fderiv ℂ F y) (y + M 0) := by rw [hy]; exact hF.differentiableAt.hasFDerivAt
  have hGd : HasFDerivAt (fun y' => F (y + M y')) ((fderiv ℂ F y).comp M) 0 :=
    hFd.comp (f := fun y' => y + M y') 0 hA
  rw [hGd.fderiv, ContinuousLinearMap.comp_apply, hy] at hxc
  have hmem : M x ∈ eulerDirs F y ⊓ U := ⟨⟨c, hxc⟩, hMU x⟩
  rw [hU.inf_eq_bot, Submodule.mem_bot] at hmem
  exact hx (hMinj (by rw [hmem, map_zero]))

theorem map_star_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    M.map (starRingEnd ℂ) *ᵥ x = star (M *ᵥ star x) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

theorem PFIntZero.maDensity_eq_zero (hR : pointFormRank_holds.Statement)
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} {d r : ℕ}
    {L : Fin d → HermLine ι} {L' : Fin d → HermLine ι'} (N : Fin r → HermLine ι') (hv : IsBlockMap κ v)
    (hQ : IsArithVar (imageZ v P') d) (hL : ∀ j, IsSmoothHerm (L j))
    (hLL : ∀ j, IsPullHerm κ v (L j) (L' j))
    {Ψ : (((k : K') → ι' k) → ℂ) →ₗ[ℂ] (Fin (d + r + 1) → ℂ)} {y : Fin (d + r) → ℂ}
    {w : ((k : K') → ι' k) → ℂ} {γ : (Fin (d + r) → ℂ) → (Σ k', ι' k') → ℂ} (hγ : IsSheet P' Ψ y w γ) :
    maDensity (fun j y' => Real.log ((Fin.append L' N j).h (γ y'))) y = 0 := by
  set F : (Fin (d + r) → ℂ) → (Σ k, ι k) → ℂ := fun y' p => γ y' (v p) with hF
  have hγa : AnalyticAt ℂ γ y := sheet_analyticAt osgood hγ
  have hFa : AnalyticAt ℂ F y := analyticAt_pi_iff.mpr fun p => analyticAt_coord hγa (v p)
  have hFy : ∀ k, ∃ i, F y ⟨k, i⟩ ≠ 0 := blocks_ne_zero_restrict hv hγ.2.self_of_nhds.2.1.1
  have hFQ : ∀ᶠ y' in 𝓝 y, F y' ∈ mcPts (imageZ v P') := by
    filter_upwards [hγ.2] with y' h
    refine ⟨blocks_ne_zero_restrict hv h.2.1.1, fun f hf => ?_⟩
    have h0 := h.2.1.2 _ (Ideal.mem_comap.mp hf)
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_rename, eval_rename] at h0
    exact h0
  set A : Fin (d + r) → Matrix (Fin (d + r)) (Fin (d + r)) ℂ :=
    fun j => cxHessian (fun y' => Real.log ((Fin.append L' N j).h (γ y'))) y with hAdef
  have hker : ∀ k ∈ Finset.univ.map (Fin.castAddEmb r), ∀ x ∈ eulerDirs F y,
      (A k).map (starRingEnd ℂ) *ᵥ x = 0 := by
    intro k hk x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hk
    obtain ⟨c, hc⟩ := hx
    have hpot : (fun y' => Real.log ((Fin.append L' N (Fin.castAddEmb r j)).h (γ y'))) =
        fun y' => Real.log ((L j).h (F y')) := by
      funext y'
      rw [Fin.coe_castAddEmb, Fin.append_left, (hLL j).2]
    have h := pointFormEuler_holds.proof K ι (L j) (d + r) F y x c (hL j) hFa hFy hc
    rw [map_star_mulVec, hAdef]
    simp only
    rw [hpot, h, star_zero]
  have hmix := mixedDisc_eq_zero_of_ker (fun k => (A k).map (starRingEnd ℂ)) (eulerDirs F y) _
    (by rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]; exact eulerDirs_finrank hR hQ hFa hFQ) hker
  rw [mixedDisc_map_star, map_eq_zero] at hmix
  show _ * _ * (mixedDisc A).re = 0
  rw [hmix, Complex.zero_re, mul_zero]

theorem PFIntZero.proof (hR : pointFormRank_holds.Statement) : PFIntZero.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r L L' N A s hv _ hQ hL hLL
  classical
  unfold arInt ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have h0 : ∀ y w, sheetDensity P' hΨ.choose (fun j z => Real.log ((Fin.append L' N j).h z)) (logNorm A s) y w
        = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · exact mul_eq_zero_of_right _ (PFIntZero.maDensity_eq_zero hR N hv hQ hL hLL hγ.choose_spec)
      · rfl
    simp [h0]
  · rfl

end GroundTheory.Heights₂.Heights.Inter
end
end

