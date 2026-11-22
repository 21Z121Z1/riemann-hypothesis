import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspCoordinateBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace CuspCoordinateBound

theorem coord_sq_le {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ) (hc : 0 < c)
    (hY : ∀ x : Fin g → ℝ, c * ∑ l, x l ^ 2 ≤ MCSchur.qf Y x) (β : Fin g → ℝ) (k : Fin g) :
    c * β k ^ 2 ≤ MCSchur.qf Y β := by
  have h1 : β k ^ 2 ≤ ∑ l, β l ^ 2 :=
    Finset.single_le_sum (f := fun l => β l ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ k)
  nlinarith [hY β]

theorem mulVec_sq_le {g : ℕ} (X : Matrix (Fin g) (Fin g) ℝ) (M : ℝ) (k : Fin g)
    (hX : ∀ l, |X k l| ≤ M) (β : Fin g → ℝ) :
    (X *ᵥ β) k ^ 2 ≤ g * M ^ 2 * ∑ l, β l ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => X k l) β
  have hrow : ∑ l, X k l ^ 2 ≤ g * M ^ 2 := by
    calc ∑ l, X k l ^ 2 ≤ ∑ _l : Fin g, M ^ 2 := Finset.sum_le_sum fun l _ => by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hX l) 2
      _ = g * M ^ 2 := by simp
  have hb : 0 ≤ ∑ l, β l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have he : (X *ᵥ β) k = ∑ l, X k l * β l := rfl
  rw [he]
  calc _ ≤ (∑ l, X k l ^ 2) * ∑ l, β l ^ 2 := hcs
    _ ≤ g * M ^ 2 * ∑ l, β l ^ 2 := mul_le_mul_of_nonneg_right hrow hb

end CuspCoordinateBound

theorem CuspCoordinateBound.proof (hImPos : ChartPeriodImPos.Statement)
    (hLow : ChartLowerBlockBound.Statement) (hPG : PeriodGramPosDef.Statement) :
    CuspCoordinateBound.Statement := by
  intro D T
  obtain ⟨M, hM, hMb⟩ := hLow D T
  have hc : 0 < D.c := D.c_pos
  set K : ℝ := 1 / D.c + 2 * M + 2 * D.g * M ^ 2 / D.c with hK
  have hK1 : 0 ≤ 1 / D.c := by positivity
  have hK2 : 0 ≤ 2 * (D.g : ℝ) * M ^ 2 / D.c := by positivity
  have hKpos : 0 < K := by positivity
  refine ⟨1 / K, by positivity, ?_⟩
  intro p hp hpU ℓ hℓ y i hi
  obtain ⟨hYpd, hYc⟩ := hImPos D p.1 hpU ℓ hℓ
  set τ := D.period p.1 ℓ with hτ
  set Y := τ.map Complex.im with hYdef
  set X := τ.map Complex.re with hXdef
  obtain ⟨-, hform⟩ := hPG D.g τ hYpd
  set α : Fin D.g → ℝ := fun k => y (Fin.castAdd D.g k) with hα
  set β : Fin D.g → ℝ := fun k => y (Fin.natAdd D.g k) with hβ
  have hA : 0 ≤ MCSchur.qf Y⁻¹ (α + X *ᵥ β) := MCCusp.qf_nonneg hYpd.inv.posSemidef _
  have hB : 0 ≤ MCSchur.qf Y β := MCCusp.qf_nonneg hYpd.posSemidef _
  suffices h : y i ^ 2 ≤ K * MCSchur.qf (periodGram τ) y by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hKpos]
    linarith
  rw [hform y]
  by_cases hig : i.val < D.g
  · set k : Fin D.g := ⟨i.val, hig⟩ with hkdef
    have hik : i = Fin.castAdd D.g k := Fin.ext rfl
    have hkr : T.r ≤ k.val := hi
    have hyk : y i = α k := congrArg y hik
    have hYkk : Y k k ≤ M :=
      calc Y k k = (τ k k).im := rfl
        _ ≤ |(τ k k).im| := le_abs_self _
        _ ≤ ‖τ k k‖ := Complex.abs_im_le_norm _
        _ ≤ M := hMb p hp ℓ k k hkr
    have hXk : ∀ l, |X k l| ≤ M := fun l =>
      (Complex.abs_re_le_norm _).trans (hMb p hp ℓ k l hkr)
    have hu : (α + X *ᵥ β) k ^ 2 ≤ M * MCSchur.qf Y⁻¹ (α + X *ᵥ β) := by
      have h1 := MCCusp.sq_le_inv_diag_mul_qf hYpd.inv (α + X *ᵥ β) k
      rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hYpd.isUnit)]
        at h1
      exact h1.trans (mul_le_mul_of_nonneg_right hYkk hA)
    have hw := CuspCoordinateBound.mulVec_sq_le X M k hXk β
    have hsplit : α k = (α + X *ᵥ β) k - (X *ᵥ β) k := by simp
    have hw2 : (X *ᵥ β) k ^ 2 ≤ D.g * M ^ 2 / D.c * MCSchur.qf Y β := by
      refine hw.trans ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      have h0 : 0 ≤ (D.g : ℝ) * M ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left (hYc β) h0]
    rw [hyk, hsplit]
    have hab : ((α + X *ᵥ β) k - (X *ᵥ β) k) ^ 2 ≤
        2 * (α + X *ᵥ β) k ^ 2 + 2 * (X *ᵥ β) k ^ 2 := by
      nlinarith [sq_nonneg ((α + X *ᵥ β) k + (X *ᵥ β) k)]
    have hid : K * (MCSchur.qf Y⁻¹ (α + X *ᵥ β) + MCSchur.qf Y β) =
        2 * M * MCSchur.qf Y⁻¹ (α + X *ᵥ β) + 2 * (D.g * M ^ 2 / D.c) * MCSchur.qf Y β +
          (1 / D.c * MCSchur.qf Y⁻¹ (α + X *ᵥ β) + 1 / D.c * MCSchur.qf Y β +
            2 * D.g * M ^ 2 / D.c * MCSchur.qf Y⁻¹ (α + X *ᵥ β) + 2 * M * MCSchur.qf Y β) := by
      rw [hK]; ring
    have hM2 : 0 ≤ 2 * M := by positivity
    rw [hid]
    nlinarith [mul_nonneg hK1 hA, mul_nonneg hK1 hB, mul_nonneg hK2 hA, mul_nonneg hM2 hB]
  · set k : Fin D.g := ⟨i.val - D.g, by omega⟩ with hkdef
    have hik : i = Fin.natAdd D.g k := Fin.ext (by simp [hkdef]; omega)
    have hyk : y i = β k := congrArg y hik
    have h1 := CuspCoordinateBound.coord_sq_le Y D.c hc hYc β k
    have h2 : β k ^ 2 ≤ 1 / D.c * MCSchur.qf Y β := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
      linarith
    have hid : K * (MCSchur.qf Y⁻¹ (α + X *ᵥ β) + MCSchur.qf Y β) =
        1 / D.c * MCSchur.qf Y β + (K * MCSchur.qf Y⁻¹ (α + X *ᵥ β) +
          (2 * M + 2 * D.g * M ^ 2 / D.c) * MCSchur.qf Y β) := by
      rw [hK]; ring
    have hM2 : 0 ≤ 2 * M + 2 * D.g * M ^ 2 / D.c := by positivity
    rw [hyk, hid]
    nlinarith [mul_nonneg hKpos.le hA, mul_nonneg hM2 hB]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem CuspLattice.proof (h1 : CuspShortVectors.Statement) (h2 : CuspLeadingMinima.Statement)
    (h3 : CuspCovolume.Statement) : CuspLattice.Statement := by
  intro D T
  obtain ⟨c₁, hc₁, H1⟩ := h1 D T
  obtain ⟨c₂, hc₂, H3⟩ := h3 D T
  exact ⟨c₁, c₂, hc₁, hc₂, fun p hp hu ℓ hℓ =>
    ⟨H1 p hp hu ℓ hℓ, h2 D T p hp hu ℓ hℓ, fun k v hv hli => H3 p hp hu ℓ hℓ k v hv hli⟩⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspLeadingMinima
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace CuspLeadingMinima

theorem single_mem_leadingLattice {g r : ℕ} (h : r ≤ g) (j : Fin r) :
    Pi.single (Fin.castLE h j) (1 : ℂ) ∈ leadingLattice g r := by
  refine ⟨Pi.single (Fin.castLE h j) 1, fun k hk => ?_, ?_⟩
  · have hne : k ≠ Fin.castLE h j := by
      intro e
      have := j.isLt
      rw [e] at hk
      simp at hk
      omega
    simp [hne]
  · ext k
    by_cases e : k = Fin.castLE h j
    · subst e; simp [intVecC]
    · simp [intVecC, e]

theorem single_linearIndependent {g r : ℕ} (h : r ≤ g) :
    LinearIndependent ℤ (fun j : Fin r => (Pi.single (Fin.castLE h j) (1 : ℂ) : Fin g → ℂ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have := congrFun hc (Fin.castLE h i)
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Pi.single_apply,
    (Fin.castLE_injective h).eq_iff] at this
  simpa using this

theorem hermValue_single {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (k : ι) :
    hermValue A (Pi.single k (1 : ℂ)) = A k k := by
  rw [MCSchur.hermValue_eq_qf]
  have hre : (fun l => ((Pi.single k (1 : ℂ) : ι → ℂ) l).re) = Pi.single k (1 : ℝ) := by
    ext l
    by_cases e : l = k
    · subst e; simp
    · simp [e]
  have him : (fun l => ((Pi.single k (1 : ℂ) : ι → ℂ) l).im) = 0 := by
    ext l
    by_cases e : l = k
    · subst e; simp
    · simp [e]
  rw [hre, him]
  simp [MCSchur.qf, mulVec_single]

end CuspLeadingMinima

theorem CuspLeadingMinima.proof (hImPos : ChartPeriodImPos.Statement) :
    CuspLeadingMinima.Statement := by
  intro D T p _ hp ℓ hℓ
  obtain ⟨hpd, hge⟩ := hImPos D p.1 hp ℓ hℓ
  set Y := (D.period p.1 ℓ).map Complex.im
  refine ⟨fun j => (Pi.single (Fin.castLE T.r_le j) (1 : ℂ) : Fin D.g → ℂ),
    fun j => CuspLeadingMinima.single_mem_leadingLattice T.r_le j,
    CuspLeadingMinima.single_linearIndependent T.r_le, fun j => ?_⟩
  set k := Fin.castLE T.r_le j
  have hc := D.c_pos
  have hdiag : Y⁻¹ k k ≤ 1 / D.c := by
    refine MCCusp.inv_diag_le hpd k hc fun x => ?_
    have h1 : x k ^ 2 ≤ ∑ l, x l ^ 2 :=
      Finset.single_le_sum (f := fun l => x l ^ 2) (fun l _ => sq_nonneg (x l))
        (Finset.mem_univ k)
    calc D.c * x k ^ 2 ≤ D.c * ∑ l, x l ^ 2 := mul_le_mul_of_nonneg_left h1 hc.le
      _ ≤ _ := hge x
  unfold metricLength
  rw [CuspLeadingMinima.hermValue_single]
  calc Real.sqrt (Y⁻¹ k k) ≤ Real.sqrt (1 / D.c) := Real.sqrt_le_sqrt hdiag
    _ = D.c ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hc.le, one_div, Real.inv_rpow hc.le]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspShortVectors
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace CuspShortVectors

theorem intVec_eq {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a n : Fin g → ℤ) :
    intVecC a + τ *ᵥ intVecC n =
      (fun k => ((a k : ℝ) : ℂ)) + τ *ᵥ fun k => ((n k : ℝ) : ℂ) := by
  unfold intVecC
  simp

theorem one_le_sq_of_ne_zero {m : ℤ} (hm : m ≠ 0) : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
  have h1 : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
  have h2 : (1 : ℤ) ≤ m ^ 2 := by nlinarith [sq_abs m]
  exact_mod_cast h2

theorem value_ge {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (hY : (τ.map Complex.im).PosDef)
    {c M : ℝ} (hM : 0 < M)
    (hcY : ∀ x : Fin g → ℝ, c * ∑ k, x k ^ 2 ≤ MCSchur.qf (τ.map Complex.im) x)
    (hPH : PeriodHermValue.Statement) (r : ℕ)
    (hdiag : ∀ k : Fin g, r ≤ k.val → (τ.map Complex.im) k k ≤ M) (a n : Fin g → ℤ)
    (h : n ≠ 0 ∨ ∃ k : Fin g, r ≤ k.val ∧ a k ≠ 0) :
    min c (1 / M) ≤ hermValue (τ.map Complex.im)⁻¹ (intVecC a + τ *ᵥ intVecC n) := by
  have hu : IsUnit (τ.map Complex.im).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit
  rw [intVec_eq, hPH g τ hu]
  have h1 := MCCusp.qf_nonneg hY.inv.posSemidef
    ((fun k => (a k : ℝ)) + τ.map Complex.re *ᵥ fun k => (n k : ℝ))
  have h2 := MCCusp.qf_nonneg hY.posSemidef fun k => (n k : ℝ)
  by_cases hn : n = 0
  · rcases h with h | ⟨k, hk, hak⟩
    · exact absurd hn h
    have hβ : (fun k => (n k : ℝ)) = 0 := by funext k; simp [hn]
    rw [hβ, mulVec_zero, add_zero]
    have hq0 : MCSchur.qf (τ.map Complex.im) 0 = 0 := by simp [MCSchur.qf]
    rw [hq0, add_zero]
    have hsq := MCCusp.sq_le_inv_diag_mul_qf hY.inv (fun k => (a k : ℝ)) k
    rw [Matrix.nonsing_inv_nonsing_inv _ hu] at hsq
    have ha := one_le_sq_of_ne_zero hak
    have hpos : 0 < (τ.map Complex.im) k k := hY.diag_pos
    have hle := hdiag k hk
    have hq := MCCusp.qf_nonneg hY.inv.posSemidef fun k => (a k : ℝ)
    have hM' : 1 / M ≤ MCSchur.qf (τ.map Complex.im)⁻¹ fun k => (a k : ℝ) := by
      rw [div_le_iff₀ hM]
      nlinarith
    exact (min_le_right _ _).trans hM'
  · obtain ⟨k, hk⟩ := Function.ne_iff.mp hn
    have hb := one_le_sq_of_ne_zero hk
    have hs := hcY fun k => (n k : ℝ)
    have hsum : ((n k : ℤ) : ℝ) ^ 2 ≤ ∑ j, ((n j : ℤ) : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun j => ((n j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ k)
    have hc : c ≤ MCSchur.qf (τ.map Complex.im) fun k => (n k : ℝ) := by
      rcases le_or_gt c 0 with hc0 | hc0
      · linarith
      · nlinarith
    linarith [min_le_left c (1 / M)]

end CuspShortVectors

theorem CuspShortVectors.proof (hImPos : ChartPeriodImPos.Statement)
    (hLow : ChartLowerBlockBound.Statement) (hPH : PeriodHermValue.Statement) :
    CuspShortVectors.Statement := by
  intro D T
  obtain ⟨M, hM, hMb⟩ := hLow D T
  refine ⟨Real.sqrt (min D.c (1 / M)), Real.sqrt_pos.mpr (lt_min D.c_pos (by positivity)), ?_⟩
  intro p hp hpU ℓ hℓ a n h
  obtain ⟨hY, hcY⟩ := hImPos D p.1 hpU ℓ hℓ
  unfold metricLength
  apply Real.sqrt_le_sqrt
  refine CuspShortVectors.value_ge _ hY hM hcY hPH T.r ?_ a n h
  intro k hk
  exact (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans (hMb p hp ℓ k k hk))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PGramPivotProduct
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace GramPivotProduct

theorem castLE_succ_eq (d : ℕ) :
    (Fin.castLE (Nat.le_succ d) : Fin d → Fin (d + 1)) = Fin.castSucc := by
  funext i
  rfl

theorem pivot_submatrix (hLL : LeadMinorLeading.Statement) {d : ℕ}
    (S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) {i : ℕ} (hi : i < d) :
    pivot (S.submatrix Fin.castSucc Fin.castSucc) i = pivot S i := by
  have h := hLL (d + 1) S d (Nat.le_succ d)
  rw [castLE_succ_eq] at h
  simp only [pivot, h (i + 1) (Nat.succ_le_of_lt hi), h i hi.le]

theorem pivot_pos (hLB : LeadMinorBasic.Statement) {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosDef) {i : ℕ} (hi : i < d) : 0 < pivot S i := by
  obtain ⟨-, -, h⟩ := hLB d S
  exact div_pos (h hS (i + 1) (Nat.succ_le_of_lt hi)) (h hS i hi.le)

theorem intGram_transpose {d k : ℕ} {S : Matrix (Fin d) (Fin d) ℝ} (hS : Sᵀ = S)
    (N : Matrix (Fin d) (Fin k) ℤ) : (intGram S N)ᵀ = intGram S N := by
  simp only [intGram, transpose_mul, transpose_transpose, hS, Matrix.mul_assoc]

theorem one_le_sq_of_ne_zero {n : ℤ} (hn : n ≠ 0) : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h : (1 : ℤ) ≤ |n| ^ 2 := one_le_pow₀ (Int.one_le_abs hn)
  rw [sq_abs] at h
  exact_mod_cast h

theorem main (hLL : LeadMinorLeading.Statement) (hLB : LeadMinorBasic.Statement)
    (hPL : PivotLast.Statement) (hU : UnimodularLast.Statement) (hSD : SchurDetBound.Statement)
    (hQ : IntGramQf.Statement) (hUni : IntGramUnimodular.Statement)
    (hDrop : IntGramDropLast.Statement) (hSub : IntGramSubLast.Statement) :
    GramPivotProduct.Statement := by
  intro d
  induction d with
  | zero =>
    intro S hS k N hN
    cases k with
    | zero => exact ⟨∅, by simp, by simp [Matrix.det_isEmpty]⟩
    | succ k =>
      exfalso
      have h0 := hN (Pi.single 0 1) (funext fun i => i.elim0)
      have := congrFun h0 0
      simp at this
  | succ d ih =>
    intro S hS k N hN
    set S' := S.submatrix Fin.castSucc Fin.castSucc with hS'
    have hS'pd : S'.PosDef := hS.submatrix (Fin.castSucc_injective d)
    by_cases hrow : ∀ j, N (Fin.last d) j = 0
    · obtain ⟨P, hP, hprod⟩ := ih S' hS'pd k (N.submatrix Fin.castSucc id) (by
        intro c hc
        apply hN c
        funext i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simp [mulVec, dotProduct, hrow]
        · exact congrFun hc i)
      refine ⟨P, fun i hi => Nat.lt_succ_of_lt (hP i hi), ?_⟩
      rw [hDrop d k S N hrow]
      calc ∏ i ∈ P, pivot S i = ∏ i ∈ P, pivot S' i :=
            Finset.prod_congr rfl fun i hi => (pivot_submatrix hLL S (hP i hi)).symm
        _ ≤ _ := hprod
    · simp only [not_forall] at hrow
      obtain ⟨j0, hj0⟩ := hrow
      cases k with
      | zero => exact j0.elim0
      | succ k =>
        set ρ : Fin (k + 1) → ℤ := fun j => N (Fin.last d) j with hρ
        have hρ0 : ρ ≠ 0 := fun h => hj0 (congrFun h j0)
        obtain ⟨U, hUdet, hUc, hUl⟩ := hU k ρ hρ0
        set M := N * U with hM
        have hMlast : ∀ j, M (Fin.last d) j = (ρ ᵥ* U) j := fun j => rfl
        set N' : Matrix (Fin d) (Fin k) ℤ := M.submatrix Fin.castSucc Fin.castSucc with hN'
        have hN'ind : ∀ c : Fin k → ℤ, N' *ᵥ c = 0 → c = 0 := by
          intro c hc
          have hMc : M *ᵥ Fin.snoc (α := fun _ => ℤ) c 0 = 0 := by
            funext i
            refine Fin.lastCases ?_ (fun i => ?_) i
            · simp [mulVec, dotProduct, Fin.sum_univ_castSucc, hMlast, hUc]
            · have := congrFun hc i
              simpa [mulVec, dotProduct, Fin.sum_univ_castSucc, hN'] using this
          have hUc0 : U *ᵥ Fin.snoc (α := fun _ => ℤ) c 0 = 0 :=
            hN _ (by rw [mulVec_mulVec]; exact hMc)
          have hsnoc : (Fin.snoc (α := fun _ => ℤ) c 0 : Fin (k + 1) → ℤ) = 0 := by
            have := congrArg (fun v => U⁻¹ *ᵥ v) hUc0
            simpa [mulVec_mulVec, nonsing_inv_mul U hUdet] using this
          funext j
          have := congrFun hsnoc (Fin.castSucc j)
          simpa using this
        obtain ⟨P', hP', hprod'⟩ := ih S' hS'pd k N' hN'ind
        set G := intGram S M with hG
        have hsub : G.submatrix Fin.castSucc Fin.castSucc = intGram S' N' :=
          hSub d k S M (fun j => by rw [hMlast]; exact hUc j)
        have hprodpos : 0 < ∏ i ∈ P', pivot S' i :=
          Finset.prod_pos fun i hi => pivot_pos hLB S' hS'pd (hP' i hi)
        have hG'pos : 0 < (G.submatrix Fin.castSucc Fin.castSucc).det := by
          rw [hsub]
          exact lt_of_lt_of_le hprodpos hprod'
        have hSt : Sᵀ = S := MCCusp.transpose_eq_of_posSemidef hS.posSemidef
        have hGt : Gᵀ = G := intGram_transpose hSt M
        have hpd : 0 < pivot S d := pivot_pos hLB S hS (Nat.lt_succ_self d)
        have hlow : ∀ v : Fin (k + 1) → ℝ, v (Fin.last k) = 1 → pivot S d ≤ MCSchur.qf G v := by
          intro v hv
          rw [hG, hQ]
          have hxl : (M.map (Int.cast : ℤ → ℝ) *ᵥ v) (Fin.last d) =
              ((ρ ᵥ* U) (Fin.last k) : ℝ) := by
            simp [mulVec, dotProduct, Fin.sum_univ_castSucc, hMlast, hUc, hv]
          have h1 : (1 : ℝ) ≤ (M.map (Int.cast : ℤ → ℝ) *ᵥ v) (Fin.last d) ^ 2 := by
            rw [hxl]
            exact one_le_sq_of_ne_zero hUl
          calc pivot S d = 1 * pivot S d := (one_mul _).symm
            _ ≤ (M.map (Int.cast : ℤ → ℝ) *ᵥ v) (Fin.last d) ^ 2 * pivot S d :=
                mul_le_mul_of_nonneg_right h1 hpd.le
            _ ≤ MCSchur.qf S (M.map (Int.cast : ℤ → ℝ) *ᵥ v) := hPL d S hS _
        have hsd := hSD k G hGt hG'pos (pivot S d) hlow
        refine ⟨insert d P', ?_, ?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact Nat.lt_succ_self _
          · exact Nat.lt_succ_of_lt (hP' i hi)
        · have hdP : d ∉ P' := fun h => lt_irrefl d (hP' d h)
          rw [Finset.prod_insert hdP, ← hUni (d + 1) (k + 1) S N U hUdet]
          calc pivot S d * ∏ i ∈ P', pivot S i = pivot S d * ∏ i ∈ P', pivot S' i := by
                rw [Finset.prod_congr rfl fun i hi => (pivot_submatrix hLL S (hP' i hi)).symm]
            _ ≤ pivot S d * (G.submatrix Fin.castSucc Fin.castSucc).det := by
                rw [hsub]
                exact mul_le_mul_of_nonneg_left hprod' hpd.le
            _ ≤ G.det := hsd

end GramPivotProduct

theorem GramPivotProduct.proof (hLL : LeadMinorLeading.Statement)
    (hLB : LeadMinorBasic.Statement) (hPL : PivotLast.Statement) (hU : UnimodularLast.Statement)
    (hSD : SchurDetBound.Statement) (hQ : IntGramQf.Statement)
    (hUni : IntGramUnimodular.Statement) (hDrop : IntGramDropLast.Statement)
    (hSub : IntGramSubLast.Statement) : GramPivotProduct.Statement :=
  GramPivotProduct.main hLL hLB hPL hU hSD hQ hUni hDrop hSub

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PIntGramDropLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem IntGramDropLast.proof : IntGramDropLast.Statement := by
  intro d k S N hN
  ext i j
  simp only [intGram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.submatrix_apply, id, Fin.sum_univ_castSucc, hN, Int.cast_zero, zero_mul, mul_zero,
    add_zero]

end

end GroundTheory.Heights₂.Heights
end

