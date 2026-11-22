import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
import GroundTheory.PAdicHodge.Bundle0004
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0030
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0005

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithmeticIntersectionMultilinearPolarStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_intersection_multilinear_polar : MetricLocalStatement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] (P : Ideal (MRing ι)) (n : ℕ) (A : σ → HermLine ι) (c : Fin n → σ → ℤ), IsArithVar P n → (∀ a, IsSmoothHerm (A a)) → (∀ r, IsSmoothHerm (combLine A (c r))) ∧ II K ι P n (fun r => combLine A (c r)) = polar n (fun w => II K ι P n fun r => A (w r)) (fun r a => (c r a : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.combLine_intersection | exact GlobalTheory.CompanionTheory.Ar.PB.combLine_intersection | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.combLine_intersection <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagValuationNormalization
section
noncomputable section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.IwBlock

theorem exists_blocks_add {L : Type} [Field L] (V : ValuationSubring L) (n m : ℕ)
    (A : Matrix (Fin (n + m)) (Fin (n + m)) L)
    (hA : ∀ a b : Fin (n + m), ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → A a b = 0) (hd : A.det ≠ 0) :
    ∃ (K : Matrix (Fin (n + m)) (Fin (n + m)) V) (U : Matrix (Fin (n + m)) (Fin (n + m)) L),
      IsUnit K.det ∧ (∀ a b : Fin (n + m), ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → U a b = 0) ∧
      U.BlockTriangular id ∧ (∀ a, U a a ≠ 0) ∧ A = K.map (algebraMap V L) * U := by
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  let A₁ : Matrix (Fin n) (Fin n) L := fun i k => A (e (Sum.inl i)) (e (Sum.inl k))
  let A₂ : Matrix (Fin m) (Fin m) L := fun i k => A (e (Sum.inr i)) (e (Sum.inr k))
  have lt_l : ∀ i : Fin n, ((e (Sum.inl i) : Fin (n + m)) : ℕ) < n := fun i => by simp [e]
  have ge_r : ∀ i : Fin m, ¬ ((e (Sum.inr i) : Fin (n + m)) : ℕ) < n := fun i => by simp [e]
  have val_l : ∀ i : Fin n, ((e (Sum.inl i) : Fin (n + m)) : ℕ) = i := fun i => by simp [e]
  have val_r : ∀ i : Fin m, ((e (Sum.inr i) : Fin (n + m)) : ℕ) = n + i := fun i => by simp [e]
  have hB : A.submatrix e e = fromBlocks A₁ 0 0 A₂ := by
    ext (i | i) (k | k)
    · rfl
    · exact hA _ _ fun h => ge_r k (h.1 (lt_l i))
    · exact hA _ _ fun h => ge_r i (h.2 (lt_l k))
    · rfl
  have hdet : A₁.det * A₂.det ≠ 0 := by
    rw [← det_fromBlocks_zero₂₁ A₁ 0 A₂, ← hB, det_submatrix_equiv_self]
    exact hd
  obtain ⟨k₁, U₁, hk₁, hU₁, hd₁, e₁⟩ := GlobalTheory.ValIwasawa.iwasawa_matrix (V := V) A₁ (left_ne_zero_of_mul hdet)
  obtain ⟨k₂, U₂, hk₂, hU₂, hd₂, e₂⟩ := GlobalTheory.ValIwasawa.iwasawa_matrix (V := V) A₂ (right_ne_zero_of_mul hdet)
  refine ⟨(fromBlocks k₁ 0 0 k₂).submatrix e.symm e.symm, (fromBlocks U₁ 0 0 U₂).submatrix e.symm e.symm,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁]
    exact hk₁.mul hk₂
  · intro a b h
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    rcases x with i | i <;> rcases y with k | k
    · exact absurd (iff_of_true (lt_l i) (lt_l k)) h
    · simp
    · simp
    · exact absurd (iff_of_false (ge_r i) (ge_r k)) h
  · intro a b h
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    have h' : ((e y : Fin (n + m)) : ℕ) < (e x : Fin (n + m)) := h
    rcases x with i | i <;> rcases y with k | k
    · rw [val_l, val_l] at h'
      simpa using hU₁ (show k < i from h')
    · simp
    · simp
    · rw [val_r, val_r] at h'
      simpa using hU₂ (show k < i from Nat.lt_of_add_lt_add_left h')
  · intro a
    obtain ⟨x, rfl⟩ := e.surjective a
    rcases x with i | i
    · simpa using hd₁ i
    · simpa using hd₂ i
  · have h1 : A = (fromBlocks A₁ 0 0 A₂).submatrix e.symm e.symm := by
      rw [← hB]; ext a b; simp
    have h3 : fromBlocks A₁ 0 0 A₂ =
        (fromBlocks k₁ 0 0 k₂).map (algebraMap V L) * fromBlocks U₁ 0 0 U₂ := by
      rw [fromBlocks_map, fromBlocks_multiply, ← e₁, ← e₂,
        Matrix.map_zero _ (map_zero (algebraMap V L)), Matrix.map_zero _ (map_zero (algebraMap V L))]
      simp
    rw [h1, h3, ← submatrix_mul_equiv _ _ _ e.symm _]
    rfl

theorem exists_blocks {L : Type} [Field L] (V : ValuationSubring L) (N n : ℕ) (hn : n ≤ N)
    (A : Matrix (Fin N) (Fin N) L)
    (hA : ∀ a b : Fin N, ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → A a b = 0) (hd : A.det ≠ 0) :
    ∃ (K : Matrix (Fin N) (Fin N) V) (U : Matrix (Fin N) (Fin N) L),
      IsUnit K.det ∧ (∀ a b : Fin N, ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → U a b = 0) ∧
      U.BlockTriangular id ∧ (∀ a, U a a ≠ 0) ∧ A = K.map (algebraMap V L) * U := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact exists_blocks_add V n m A hA hd

theorem inv_diag_ne_zero {L : Type} [Field L] {N : ℕ} {U : Matrix (Fin N) (Fin N) L}
    (hU : U.BlockTriangular id) (hd : IsUnit U.det) (a : Fin N) : U⁻¹ a a ≠ 0 := by
  have hI : U⁻¹.BlockTriangular id := by
    letI := Matrix.invertibleOfIsUnitDet U hd
    exact blockTriangular_inv_of_blockTriangular hU
  intro e
  have h := congrFun (congrFun (nonsing_inv_mul U hd) a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single a (fun c _ hc => ?_) (by simp), e,
    zero_mul] at h
  · exact zero_ne_one h
  · rcases lt_or_gt_of_ne hc with l | l
    · rw [hI l, zero_mul]
    · rw [hU l, mul_zero]

theorem main : ∀ (L : Type) [Field L] (V : ValuationSubring L) (N j : ℕ) (A : Matrix (Fin N) (Fin N) L), IsBlockDiag j A → A.det ≠ 0 → ∃ b : Matrix (Fin N) (Fin N) L, IsBlockDiag j b ∧ b.BlockTriangular id ∧ (∀ a, b a a ≠ 0) ∧ (∀ a c, (A * b) a c ∈ V) ∧ (A * b).det ≠ 0 ∧ ((A * b).det)⁻¹ ∈ V := by
  intro L _ V N j A hA hd
  obtain ⟨K, U, hK, hUb, hUt, hUd, hAe⟩ := exists_blocks V N (N - j) (Nat.sub_le N j) A hA hd
  have hUdet : IsUnit U.det := by
    rw [det_of_upperTriangular hUt]
    exact (Finset.prod_ne_zero_iff.2 fun a _ => hUd a).isUnit
  have hAU : A * U⁻¹ = K.map (algebraMap V L) := by
    rw [hAe, Matrix.mul_nonsing_inv_cancel_right _ _ hUdet]
  have hKdet : (K.map (algebraMap V L)).det = algebraMap V L K.det := (RingHom.map_det _ K).symm
  have hUb' : IsBlockDiag j U := hUb
  refine ⟨U⁻¹, hUb'.inv hUdet, ?_, inv_diag_ne_zero hUt hUdet, fun a c => ?_, ?_, ?_⟩
  · letI := Matrix.invertibleOfIsUnitDet U hUdet
    exact blockTriangular_inv_of_blockTriangular hUt
  · rw [hAU]
    exact (K a c).2
  · rw [hAU, hKdet]
    exact (hK.map (algebraMap V L)).ne_zero
  · rw [hAU, hKdet]
    obtain ⟨u, hu⟩ := hK
    rw [← hu]
    have e : (algebraMap V L (u : V))⁻¹ = algebraMap V L ((u⁻¹ : Vˣ) : V) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← map_mul, Units.mul_inv, map_one]
    rw [e]
    exact ((u⁻¹ : Vˣ) : V).2

end GlobalTheory.CompanionTheory.Ar.PB.IwBlock
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {R : Type} [CommRing R] {N : ℕ}

theorem minorIJ_eq_det (h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) (k : ℕ) (hI : I.card = k)
    (hJ : J.card = k) : minorIJ h I J = (h.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det := by
  subst hJ
  unfold minorIJ
  rw [dif_pos hI]

theorem minorIJ_of_card_ne (h : Matrix (Fin N) (Fin N) R) {I J : Finset (Fin N)} (e : I.card ≠ J.card) :
    minorIJ h I J = 0 := by
  unfold minorIJ
  rw [dif_neg e]

theorem minorIJ_mul_of_card (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) (k : ℕ) (hI : I.card = k)
    (hJ : J.card = k) :
    minorIJ (T * h) I J = ∑ s : GroundTheory.PAdicHodge.KSubset N k, minorIJ T I s.1 * minorIJ h s.1 J := by
  rw [minorIJ_eq_det _ _ _ k hI hJ]
  have e : (T * h).submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ) =
      T.submatrix (I.orderEmbOfFin hI) id * h.submatrix id (J.orderEmbOfFin hJ) := by
    ext a b
    simp [Matrix.mul_apply]
  rw [e, GroundTheory.PAdicHodge.det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [minorIJ_eq_det T I s.1 k hI s.2, minorIJ_eq_det h s.1 J k s.2 hJ]
  rfl

theorem minorIJ_mul (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (T * h) I J = ∑ I', minorIJ T I I' * minorIJ h I' J := by
  by_cases e : I.card = J.card
  · rw [minorIJ_mul_of_card T h I J I.card rfl e.symm]
    have h1 : ∑ I' : Finset (Fin N), minorIJ T I I' * minorIJ h I' J =
        ∑ I' ∈ Finset.univ.filter (fun I' : Finset (Fin N) => I'.card = I.card),
          minorIJ T I I' * minorIJ h I' J := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun s _ hs => ?_
      have hc : s.card ≠ I.card := fun hc => hs (by simp [hc])
      rw [minorIJ_of_card_ne T (Ne.symm hc), zero_mul]
    rw [h1]
    exact (Finset.sum_subtype (Finset.univ.filter fun I' : Finset (Fin N) => I'.card = I.card)
      (p := fun s : Finset (Fin N) => s.card = I.card) (fun s => by simp)
      (fun I' => minorIJ T I I' * minorIJ h I' J)).symm
  · rw [minorIJ_of_card_ne _ e]
    symm
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : I.card = s.card
    · rw [minorIJ_of_card_ne h (fun h' => e (hs.trans h')), mul_zero]
    · rw [minorIJ_of_card_ne T hs, zero_mul]

theorem minorIJ_eq_zero_of_row (h : Matrix (Fin N) (Fin N) R) {I C : Finset (Fin N)} {a : Fin N} (ha : a ∈ I)
    (hz : ∀ c ∈ C, h a c = 0) : minorIJ h I C = 0 := by
  by_cases e : I.card = C.card
  · rw [minorIJ_eq_det h I C _ e rfl]
    have hr : a ∈ Set.range (I.orderEmbOfFin e) := by
      rw [Finset.range_orderEmbOfFin]
      exact ha
    obtain ⟨x, rfl⟩ := hr
    refine Matrix.det_eq_zero_of_row_eq_zero x fun y => ?_
    simp only [Matrix.submatrix_apply]
    refine hz _ ?_
    exact Finset.orderEmbOfFin_mem _ _ _
  · exact minorIJ_of_card_ne h e

theorem sum_mem_eq_sum_enum (C : Finset (Fin N)) (f : Fin N → R) :
    ∑ k ∈ C, f k = ∑ z, f (C.orderEmbOfFin rfl z) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ C rfl]
  rw [Finset.sum_map]
  rfl

theorem prod_mem_eq_prod_enum (C : Finset (Fin N)) (f : Fin N → R) :
    ∏ k ∈ C, f k = ∏ z, f (C.orderEmbOfFin rfl z) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ C rfl]
  rw [Finset.prod_map]
  rfl

theorem minorIJ_mul_of_support (A B : Matrix (Fin N) (Fin N) R) (I C : Finset (Fin N))
    (hz : ∀ k c, c ∈ C → k ∉ C → B k c = 0) :
    minorIJ (A * B) I C = minorIJ A I C * minorIJ B C C := by
  by_cases e : I.card = C.card
  · rw [minorIJ_eq_det _ I C _ e rfl, minorIJ_eq_det A I C _ e rfl, minorIJ_eq_det B C C _ rfl rfl, ← Matrix.det_mul]
    congr 1
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    have hy : C.orderEmbOfFin rfl y ∈ C := Finset.orderEmbOfFin_mem _ _ _
    have h1 : ∑ k, A (I.orderEmbOfFin e x) k * B k (C.orderEmbOfFin rfl y) =
        ∑ k ∈ C, A (I.orderEmbOfFin e x) k * B k (C.orderEmbOfFin rfl y) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
      rw [hz k _ hy hk, mul_zero]
    rw [h1, sum_mem_eq_sum_enum C]
  · rw [minorIJ_of_card_ne _ e, minorIJ_of_card_ne _ e, zero_mul]

theorem minorIJ_self_of_triangular (B : Matrix (Fin N) (Fin N) R) (hB : B.BlockTriangular id) (C : Finset (Fin N)) :
    minorIJ B C C = ∏ c ∈ C, B c c := by
  rw [minorIJ_eq_det B C C _ rfl rfl]
  have ht : (B.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl)).BlockTriangular id := by
    intro x y hxy
    exact hB ((C.orderEmbOfFin rfl).strictMono hxy)
  rw [Matrix.det_of_upperTriangular ht, prod_mem_eq_prod_enum C (fun c => B c c)]
  rfl

theorem mem_stepCols_block {N j : ℕ} {i c : Fin N} (hj : j ≤ N) (hc : c ∈ stepCols N j i) :
    if (i : ℕ) + 1 ≤ j then N - j ≤ (c : ℕ) else (c : ℕ) < N - j := by
  have hi := i.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  split_ifs at hc ⊢ with h
  · exact hc.1
  · omega

theorem support_stepCols {N j : ℕ} {i : Fin N} (hj : j ≤ N) (bb : Matrix (Fin N) (Fin N) R)
    (hd : IsBlockDiag j bb) (ht : bb.BlockTriangular id) (k c : Fin N) (hc : c ∈ stepCols N j i)
    (hk : k ∉ stepCols N j i) : bb k c = 0 := by
  by_cases hkc : c < k
  · exact ht hkc
  have hkc' : (k : ℕ) ≤ c := by simpa using not_lt.mp hkc
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc hk
  split_ifs at hc hk with h
  · refine hd k c fun hiff => ?_
    have : ¬ (k : ℕ) < N - j → False := fun h' => hk ⟨by omega, by omega⟩
    have h3 : (k : ℕ) < N - j := by omega
    have := hiff.mp h3
    omega
  · exact absurd (by omega) hk

theorem isBlockDiag_mul {j : ℕ} {T h : Matrix (Fin N) (Fin N) R} (hT : IsBlockDiag j T) (hh : IsBlockDiag j h) :
    IsBlockDiag j (T * h) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : ((a : ℕ) < N - j ↔ (k : ℕ) < N - j)
  · rw [hh k b (fun h' => hab (hk.trans h')), mul_zero]
  · rw [hT a k hk, zero_mul]

theorem support_wIdx {j : ℕ} {h : Matrix (Fin N) (Fin N) R} (hh : IsBlockDiag j h) (k c : Fin N)
    (hc : c ∈ wIdx N j) (hk : k ∉ wIdx N j) : h k c = 0 := by
  simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hc hk
  refine hh k c fun hiff => ?_
  have := hiff.mp (not_le.mp hk)
  omega

theorem support_omIdx {j : ℕ} {h : Matrix (Fin N) (Fin N) R} (hh : IsBlockDiag j h) (k c : Fin N)
    (hc : c ∈ omIdx N j) (hk : k ∉ omIdx N j) : h k c = 0 := by
  simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hc hk
  refine hh k c fun hiff => hk (hiff.mpr hc)

theorem detFac_mul {j : ℕ} (i : Fin N) {T h : Matrix (Fin N) (Fin N) R} (hh : IsBlockDiag j h) :
    detFac j i (T * h) = detFac j i T * detFac j i h := by
  unfold detFac
  rw [minorIJ_mul_of_support T h _ _ (support_wIdx hh), minorIJ_mul_of_support T h _ _ (support_omIdx hh)]
  split_ifs <;> ring

theorem minor_stepCols_eq_zero {N j : ℕ} {i : Fin N} (hj : j ≤ N) (h : Matrix (Fin N) (Fin N) R)
    (I : Finset (Fin N)) (hd : IsBlockDiag j h) (hI : ¬ IsStepRows N j i I) :
    minorIJ h I (stepCols N j i) = 0 := by
  by_cases e : I.card = (stepCols N j i).card
  · have hs : ¬ I ⊆ if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j := fun hs => hI ⟨e, hs⟩
    obtain ⟨a, ha, has⟩ := Finset.not_subset.mp hs
    refine minorIJ_eq_zero_of_row h ha fun c hc => hd a c fun hiff => ?_
    have hb := mem_stepCols_block hj hc
    split_ifs at has hb with h1
    · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at has
      have := hiff.mp (not_le.mp has)
      omega
    · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at has
      exact has (hiff.mpr hb)
  · exact minorIJ_of_card_ne h e

theorem minors_main : ∀ (R : Type) [CommRing R] (N j : ℕ) (i : Fin N), j ≤ N →
    (∀ (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)),
      minorIJ (T * h) I J = ∑ I', minorIJ T I I' * minorIJ h I' J) ∧
    (∀ (h : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N)), IsBlockDiag j h → ¬ IsStepRows N j i I →
      minorIJ h I (stepCols N j i) = 0 ∨ stepCols N j i = ∅) ∧
    (∀ (h bb : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N)), IsBlockDiag j bb → bb.BlockTriangular id →
      minorIJ (h * bb) I (stepCols N j i) = minorIJ h I (stepCols N j i) * ∏ c ∈ stepCols N j i, bb c c) ∧
    ∀ T h : Matrix (Fin N) (Fin N) R, IsBlockDiag j T → IsBlockDiag j h →
      IsBlockDiag j (T * h) ∧ detFac j i (T * h) = detFac j i T * detFac j i h := by
  intro R _ N j i hj
  refine ⟨minorIJ_mul, fun h I hd hI => Or.inl (minor_stepCols_eq_zero hj h I hd hI), ?_, ?_⟩
  · intro h bb I hd ht
    rw [minorIJ_mul_of_support h bb I _ (support_stepCols hj bb hd ht),
      minorIJ_self_of_triangular bb ht]
  · intro T h hT hh
    exact ⟨isBlockDiag_mul hT hh, detFac_mul i hh⟩

end GlobalTheory.CompanionTheory.Ar.PB.MinorCalc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartLatticeShiftNonzeroStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_shift_nonzero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (α : K → ℤ) (dβ : K → ℕ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1) 1, e ≠ 0) → ∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1 - dβ κ) 1, e ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.section_sub_degree | exact GlobalTheory.CompanionTheory.Ar.PB.section_sub_degree | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.section_sub_degree <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CombLineHEqExp
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem coef_sub_smul {Ψ : Type} [Fintype Ψ] {N : ℕ} (R : RootModel Ψ N) (lam nu : Wt Ψ N) (s : ℝ)
    (j : Option (Ψ × Fin N)) :
    R.coef (lam - s • nu) s j = R.coef lam 0 j - s * R.coef nu (-1) j := by
  rcases j with _ | ⟨a, i⟩
  · change s / (R.kA : ℝ) = 0 / (R.kA : ℝ) - s * ((-1) / (R.kA : ℝ))
    ring
  · change -(lam a i - s * nu a i) = -lam a i - s * -nu a i
    ring

theorem line_a_eq {Ψ : Type} [Fintype Ψ] {N : ℕ} (R : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) :
    (R.line t j).a = (R.line 1 j).a := by
  rcases j with _ | r
  · rfl
  · change (R.x t r).a = (R.x 1 r).a
    rw [R.x_deg, R.x_deg]

theorem combLine_line_a {Ψ : Type} [Fintype Ψ] {N : ℕ} (R : RootModel Ψ N) (t : ℝ)
    (m : Option (Ψ × Fin N) → ℤ) (x : R.K) :
    (combLine (R.line t) m).a x = ∑ j, m j * (R.line 1 j).a x := by
  simp only [GlobalTheory.CompanionTheory.Ar.Top.combLine, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [line_a_eq R t j]

theorem FinBounds.mul_nat {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {I : Type} [Fintype I] {w : I → Ω} {a₁ a' aτ aσ : K → ℤ} {τ σ : Ω}
    {q m₁ m₂ : ℕ} {u : MRing ι} {p : ℕ} [Fact p.Prime] {e a b : ℝ}
    (h : FinBounds y w a₁ a' aτ aσ τ σ q m₁ m₂ u p e a b) (t : ℕ) :
    FinBounds y w a₁ a' aτ aσ τ σ (q * t) (m₁ * t) (m₂ * t) u p e a b := by
  unfold GlobalTheory.CompanionTheory.Ar.Small.FinBounds at h ⊢
  intro z hz hu
  obtain ⟨r₁, r', rτ, rσ, E, φ, h1, h2, h3, h4, heq, rest⟩ := h z hz hu
  refine ⟨r₁, r', rτ, rσ, E, φ, h1, h2, h3, h4, ?_, rest⟩
  rw [pow_mul, pow_mul, pow_mul, pow_mul, heq, mul_pow, mul_pow]

theorem combLine_h_eq_exp {Ψ : Type} [Fintype Ψ] {N : ℕ} (R : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ)
    (q : ℕ) (m : Option (Ψ × Fin N) → ℤ) (hm : ∀ j, (m j : ℝ) = q * R.coef lam s j)
    (z : (Σ k, R.ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (combLine (R.line t) m).h z = Real.exp (q * R.weight t lam s z) := by
  have hpos : ∀ j, 0 < (R.line t j).h z := fun j => (R.line t j).pos z hz
  simp only [GlobalTheory.CompanionTheory.Ar.Top.combLine, GlobalTheory.CompanionTheory.Ar.Top.RootModel.weight]
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← Real.rpow_intCast, Real.rpow_def_of_pos (hpos j), hm j]
  congr 1
  ring

theorem hasInputs_of_data : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (R : RootModel Ψ N) (Λ : ℝ) (G : GenModel R Λ) (lam nu : Wt Ψ N) (n' n₀ : Option (Ψ × Fin N) → ℤ) (q₀ μ k : ℕ) (a₁ aτ aσ : R.K → ℤ) (τ σ ε : R.Ω) (u : MRing R.ι) (S : Finset ℕ) (e a b c : ℕ → ℝ) (A P R₀ cinf cc C s₀ : ℝ) (κ : (G.F →+* ℂ) → ℝ) (h₁ h' hτ hσ ρ : ((Σ k, R.ι k) → ℂ) → ℝ), 0 < q₀ → 0 < μ → (∀ j, (n' j : ℝ) = R.coef lam 0 j) → (∀ j, (n₀ j : ℝ) = q₀ * R.coef nu (-1) j) → (∀ x, ((8 * μ : ℕ) : ℤ) * a₁ x = ((8 * μ : ℕ) : ℤ) * (combLine (R.line 1) n').a x + ((3 * μ : ℕ) : ℤ) * aτ x + k * aσ x) → τ ≠ 0 → σ ≠ 0 → ε ≠ 0 → ε ∈ chartLatNm R.y (combLine (R.line 1) n₀).a 1 → IsFormOff (mCoordIdeal R.y) u → (∀ p ∈ S, p.Prime) → (∀ p, 0 ≤ c p) → (∀ p, p ∉ S → c p = 0) → (∀ p : ℕ, p.Prime → (((8 * μ : ℕ) : ℝ) * (e p + a p) + k * b p) * Real.log p ≤ ((8 * μ : ℕ) : ℝ) * c p) → (∀ (p : ℕ) [Fact p.Prime], FinBounds R.y G.w a₁ (combLine (R.line 1) n').a aτ aσ τ σ (8 * μ) (3 * μ) k u p (e p) (a p) (b p)) → (∀ sg, κ (NumberField.ComplexEmbedding.conjugate sg) = κ sg) → (∀ sg : G.F →+* ℂ, ∀ z ∈ mcPts (mCoordIdeal R.y), LiesOver R.y sg z → aeval z u ≠ 0 → 0 < h₁ z ∧ 0 < h' z ∧ 0 < hτ z ∧ 0 < hσ z ∧ h₁ z ^ (8 * μ) = h' z ^ (8 * μ) * hτ z ^ (3 * μ) * hσ z ^ k ∧ (∀ v : G.I → ℂ, (∀ i, HasVal R.y a₁ (G.w i) z (v i)) → v ≠ 0 ∧ Real.exp (-(A + 3 * ρ z) / 2) * h₁ z ≤ G.L.h fun x => v x.2) ∧ ValLe R.y aτ τ z (Real.exp (4 * (2 * P - ρ z) + R₀) * hτ z) ∧ ValLe R.y aσ σ z (Real.exp (κ sg) * hσ z)) → 0 ≤ C → 0 < s₀ → (∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ z ∈ mcPts (mCoordIdeal R.y), aeval z u ≠ 0 → ∀ x : ℂ, HasVal R.y (combLine (R.line 1) n₀).a ε z x → x ≠ 0 → s / q₀ * Real.log ‖x‖ + R.weight (scale s) (lam - s • nu) s z ≤ C * s + Real.log (h' z)) → ((8 * μ : ℕ) : ℝ) * (A / 2 + 3 * P) + ((3 * μ : ℕ) : ℝ) * R₀ + k * embMean κ ≤ ((8 * μ : ℕ) : ℝ) * cinf → ∑ p ∈ S, c p + cinf ≤ cc → G.HasInputs (fun s => lam - s • nu) cc := by
  intro Ψ _ N R Λ G lam nu n' n₀ q₀ μ k a₁ aτ aσ τ σ ε u S e a b c A P R₀ cinf cc C s₀ κ h₁ h' hτ hσ ρ
    hq₀ hμ hn' hn₀ hdeg hτ0 hσ0 hε0 hεint hu hS hc0 hcS hcge hfin hκ harch hC hs₀ hmain hcinf hcc
  have hq₀' : (0:ℝ) < q₀ := by exact_mod_cast hq₀
  have hμ' : (0:ℝ) < μ := by exact_mod_cast hμ
  have h8μ : (0:ℝ) < 8 * μ := by linarith
  obtain ⟨N₀, hN₀, hN₀1⟩ : ∃ N₀ : ℕ, (q₀:ℝ) / (8 * μ) / s₀ < N₀ ∧ 1 ≤ N₀ :=
    ⟨⌈(q₀:ℝ) / (8 * μ) / s₀⌉₊ + 1, by push_cast; linarith [Nat.le_ceil ((q₀:ℝ) / (8 * μ) / s₀)], by omega⟩
  refine ⟨C, hC, fun n => (q₀:ℝ) / (8 * μ) / ((n + N₀ : ℕ) : ℝ), ?_, ?_, ?_⟩
  · intro n
    have hpos : (0:ℝ) < ((n + N₀ : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n + N₀)
    exact div_pos (div_pos hq₀' h8μ) hpos
  · exact (tendsto_const_div_atTop_nhds_zero_nat ((q₀:ℝ) / (8 * μ))).comp (tendsto_add_atTop_nat N₀)
  intro n
  dsimp only
  have htN : N₀ ≤ n + N₀ := by omega
  generalize n + N₀ = t at htN ⊢
  have ht' : (0:ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have ht0 : (0:ℝ) ≤ t := ht'.le
  have hspos : 0 < (q₀:ℝ) / (8 * μ) / t := div_pos (div_pos hq₀' h8μ) ht'
  have hsle : (q₀:ℝ) / (8 * μ) / t ≤ s₀ := by
    rw [div_le_iff₀ ht']
    have h1 : (q₀:ℝ) / (8 * μ) / s₀ < t := lt_of_lt_of_le hN₀ (by exact_mod_cast htN)
    have h2 := (div_lt_iff₀ hs₀).mp h1
    linarith
  have hqs : ((8 * μ * t : ℕ) : ℝ) * ((q₀:ℝ) / (8 * μ) / t) = q₀ := by
    have hμne : (μ:ℝ) ≠ 0 := hμ'.ne'
    have htne : (t:ℝ) ≠ 0 := ht'.ne'
    push_cast
    field_simp
  have hm : ∀ j, ((((8 * μ * t : ℕ) : ℤ) * n' j - n₀ j : ℤ) : ℝ) =
      ((8 * μ * t : ℕ) : ℝ) * R.coef (lam - ((q₀:ℝ) / (8 * μ) / t) • nu) ((q₀:ℝ) / (8 * μ) / t) j := by
    intro j
    rw [coef_sub_smul, ← hn' j]
    have h0 := hn₀ j
    have hqs' := hqs
    push_cast at h0 hqs' ⊢
    linear_combination (-1:ℝ) * h0 + R.coef nu (-1) j * hqs'
  refine ⟨8 * μ * t, fun j => ((8 * μ * t : ℕ) : ℤ) * n' j - n₀ j,
    Nat.mul_pos (Nat.mul_pos (by norm_num) hμ) (by omega), hm, ⟨?_⟩⟩
  refine GlobalTheory.CompanionTheory.Ar.Small.SectionInputs.mk a₁ (combLine (R.line 1) n').a aτ aσ (combLine (R.line 1) n₀).a τ σ ε
    (3 * μ * t) (k * t) 1 u S e a b c A P R₀ κ cinf G.L_deg ?_ ?_ (by ring) hτ0 hσ0 hε0 hεint hu hS hc0 hcS ?_
    ?_ hκ ?_ ?_ hcc
  · intro x
    have h0 := hdeg x
    push_cast at h0 ⊢
    linear_combination (t:ℤ) * h0
  · intro x
    rw [combLine_line_a R 1 n' x, combLine_line_a R 1 n₀ x, combLine_line_a R _ _ x,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    push_cast
    ring
  · intro p hp
    calc _ = (t:ℝ) * ((((8 * μ : ℕ) : ℝ) * (e p + a p) + k * b p) * Real.log p) := by push_cast; ring
      _ ≤ (t:ℝ) * (((8 * μ : ℕ) : ℝ) * c p) := mul_le_mul_of_nonneg_left (hcge p hp) ht0
      _ = _ := by push_cast; ring
  · intro p _
    exact (hfin p).mul_nat t
  · intro sg
    unfold GlobalTheory.CompanionTheory.Ar.Small.ArchBounds
    intro z hz hlies hu'
    obtain ⟨p1, p2, p3, p4, hpow, hv, hτv, hσv⟩ := harch sg z hz hlies hu'
    refine ⟨h₁ z, h' z, hτ z, hσ z, ρ z, p1, p2, p3, p4, ?_, hv, hτv, hσv, ?_⟩
    · rw [pow_mul (h₁ z) (8 * μ) t, pow_mul (h' z) (8 * μ) t, pow_mul (hτ z) (3 * μ) t, pow_mul (hσ z) k t,
        hpow, mul_pow, mul_pow]
    · intro x hx
      by_cases hx0 : x = 0
      · rw [hx0, norm_zero, pow_one, zero_mul]
        positivity
      · have hM := combLine_h_eq_exp R (scale ((q₀:ℝ) / (8 * μ) / t)) (lam - ((q₀:ℝ) / (8 * μ) / t) • nu)
          ((q₀:ℝ) / (8 * μ) / t) (8 * μ * t) _ hm z hz.1
        have hmn := hmain _ hspos hsle z hz hu' x hx hx0
        have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
        have hq0 : (0:ℝ) ≤ ((8 * μ * t : ℕ) : ℝ) := Nat.cast_nonneg _
        have hq1 : ((8 * μ * t : ℕ) : ℝ) * ((q₀:ℝ) / (8 * μ) / t / q₀) = 1 := by
          rw [← mul_div_assoc, hqs, div_self hq₀'.ne']
        have key := mul_le_mul_of_nonneg_left hmn hq0
        rw [mul_add, ← mul_assoc, hq1, one_mul, mul_add] at key
        have hexp : Real.exp (((8 * μ * t : ℕ) : ℝ) * Real.log (h' z)) = h' z ^ (8 * μ * t) := by
          rw [Real.exp_nat_mul, Real.exp_log p2]
        rw [hM, pow_one, ← hexp, ← Real.exp_add, ← Real.exp_log hxpos, ← Real.exp_add]
        exact Real.exp_le_exp.mpr key
  · calc _ = (t:ℝ) * (((8 * μ : ℕ) : ℝ) * (A / 2 + 3 * P) + ((3 * μ : ℕ) : ℝ) * R₀ + k * embMean κ) := by
          push_cast; ring
      _ ≤ (t:ℝ) * (((8 * μ : ℕ) : ℝ) * cinf) := mul_le_mul_of_nonneg_left hcinf ht0
      _ = _ := by push_cast; ring

end GlobalTheory.CompanionTheory.Ar.Small
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantHermitianMetricStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugation_invariant_hermitian_metric : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι), IsSmoothHerm A → ∃ B : HermLine ι, B.a = A.a ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → Real.log (B.h z) = (Real.log (A.h z) + Real.log (A.h fun p => starRingEnd ℂ (z p))) / 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.exists_conjInvariant_line_averaged | exact GlobalTheory.CompanionTheory.Ar.PB.exists_conjInvariant_line_averaged | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.exists_conjInvariant_line_averaged <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeOrthogonalSumStatement
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_degree_orthogonal_sum : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (I : Type) [Fintype I] (F : I → Submodule (𝓞 K) E.carrier), (∀ a b, a ≠ b → OrthAt E (F a) (F b)) → E.normDegree (⨆ a, F a) = ∑ a, E.normDegree (F a) ∧ E.rank (⨆ a, F a) = ∑ a, E.rank (F a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrthSum.normDegree_rank_iSup | exact GlobalTheory.CompanionTheory.Ar.OrthSum.normDegree_rank_iSup | (intros; apply GlobalTheory.CompanionTheory.Ar.OrthSum.normDegree_rank_iSup <;> assumption)
end

