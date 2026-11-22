import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPeriodGramPosDef
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PeriodGramPosDef

theorem hermPair_symm {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : Aᵀ = A) (v w : ι → ℂ) :
    hermPair A v w = hermPair A w v := by
  simp only [hermPair, dotProduct, mulVec, Matrix.map_apply, Complex.re_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hkl : A l k = A k l := by rw [← transpose_apply A k l, hA]
  rw [hkl]
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  ring

theorem hermPair_sum_right {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ)
    (v : ι → ℂ) (w : κ → ι → ℂ) (x : κ → ℝ) :
    hermPair A v (∑ j, (x j : ℂ) • w j) = ∑ j, x j * hermPair A v (w j) := by
  simp only [hermPair]
  rw [mulVec_sum, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

theorem hermPair_sum_left {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ)
    (v : κ → ι → ℂ) (w : ι → ℂ) (x : κ → ℝ) :
    hermPair A (∑ i, (x i : ℂ) • v i) w = ∑ i, x i * hermPair A (v i) w := by
  simp only [hermPair]
  rw [star_sum, sum_dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_smul, Complex.star_def, Complex.conj_ofReal, smul_dotProduct, smul_eq_mul,
    Complex.re_ofReal_mul]

theorem qf_gram {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι ι ℝ) (b : κ → ι → ℂ)
    (x : κ → ℝ) :
    MCSchur.qf (Matrix.of fun i j => hermPair A (b i) (b j)) x =
      hermValue A (∑ i, (x i : ℂ) • b i) := by
  rw [hermValue, hermPair_sum_left]
  simp only [hermPair_sum_right, MCSchur.qf, dotProduct, mulVec, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sum_periodBasis {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fin (g + g) → ℝ) :
    ∑ i, (x i : ℂ) • periodBasis τ i =
      (fun k => (x (Fin.castAdd g k) : ℂ)) + τ *ᵥ fun k => (x (Fin.natAdd g k) : ℂ) := by
  rw [Fin.sum_univ_add]
  simp only [periodBasis, Fin.append_left, Fin.append_right, ← mulVec_smul, ← mulVec_sum]
  congr 1
  · funext l
    simp [Finset.sum_apply, Pi.single_apply]
  · congr 1
    funext l
    simp [Finset.sum_apply, Pi.single_apply]

end PeriodGramPosDef

open PeriodGramPosDef in

theorem PeriodGramPosDef.proof (hPH : PeriodHermValue.Statement) : PeriodGramPosDef.Statement := by
  intro g τ hY
  have hu : IsUnit (τ.map Complex.im).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit
  have hform : ∀ x : Fin (g + g) → ℝ,
      MCSchur.qf (periodGram τ) x =
        MCSchur.qf (τ.map Complex.im)⁻¹
            ((fun k => x (Fin.castAdd g k)) + τ.map Complex.re *ᵥ fun k => x (Fin.natAdd g k)) +
          MCSchur.qf (τ.map Complex.im) (fun k => x (Fin.natAdd g k)) := by
    intro x
    rw [periodGram, qf_gram, sum_periodBasis]
    exact hPH g τ hu _ _
  refine ⟨?_, hform⟩
  have hYi := hY.inv
  have hsym : ((τ.map Complex.im)⁻¹)ᵀ = (τ.map Complex.im)⁻¹ :=
    MCCusp.transpose_eq_of_posSemidef hYi.posSemidef
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp only [transpose_apply, periodGram, Matrix.of_apply]
    exact hermPair_symm hsym _ _
  · have e : star x ⬝ᵥ (periodGram τ *ᵥ x) = MCSchur.qf (periodGram τ) x := by
      simp [MCSchur.qf]
    rw [e, hform]
    have h1 := MCCusp.qf_nonneg hYi.posSemidef
      ((fun k => x (Fin.castAdd g k)) + τ.map Complex.re *ᵥ fun k => x (Fin.natAdd g k))
    by_cases hβ : (fun k => x (Fin.natAdd g k)) = 0
    · have hα : (fun k => x (Fin.castAdd g k)) ≠ 0 := by
        intro hα
        apply hx
        funext i
        refine Fin.addCases (fun k => ?_) (fun k => ?_) i
        · exact congrFun hα k
        · exact congrFun hβ k
      have h2 : 0 < MCSchur.qf (τ.map Complex.im)⁻¹ (fun k => x (Fin.castAdd g k)) := by
        have := hYi.dotProduct_mulVec_pos hα
        simpa [MCSchur.qf] using this
      rw [hβ, mulVec_zero, add_zero]
      rw [hβ, mulVec_zero, add_zero] at h1
      have h3 : MCSchur.qf (τ.map Complex.im) 0 = 0 := by simp [MCSchur.qf]
      rw [h3]
      linarith
    · have h2 : 0 < MCSchur.qf (τ.map Complex.im) (fun k => x (Fin.natAdd g k)) := by
        have := hY.dotProduct_mulVec_pos hβ
        simpa [MCSchur.qf] using this
      linarith

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPeriodHermValue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PeriodHermValue

theorem re_eq {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (α β : Fin g → ℝ) :
    (fun k => (((fun k => (α k : ℂ)) + τ *ᵥ fun k => (β k : ℂ)) k).re) =
      α + τ.map Complex.re *ᵥ β := by
  ext k
  simp [mulVec, dotProduct, Complex.re_sum, Complex.mul_re]

theorem im_eq {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (α β : Fin g → ℝ) :
    (fun k => (((fun k => (α k : ℂ)) + τ *ᵥ fun k => (β k : ℂ)) k).im) =
      τ.map Complex.im *ᵥ β := by
  ext k
  simp [mulVec, dotProduct, Complex.im_sum, Complex.mul_im]

theorem qf_inv_mulVec {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (hY : IsUnit Y.det)
    (β : Fin g → ℝ) : MCSchur.qf Y⁻¹ (Y *ᵥ β) = MCSchur.qf Y β := by
  unfold MCSchur.qf
  rw [mulVec_mulVec, nonsing_inv_mul Y hY, one_mulVec, dotProduct_comm]

end PeriodHermValue

theorem PeriodHermValue.proof : PeriodHermValue.Statement := by
  intro g τ hY α β
  rw [MCSchur.hermValue_eq_qf, PeriodHermValue.re_eq, PeriodHermValue.im_eq,
    PeriodHermValue.qf_inv_mulVec _ hY]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPeriodLatticeCovolume
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PeriodLatticeCovolume

theorem hermPair_comb {ι : Type*} [Fintype ι] {m : ℕ} (A : Matrix ι ι ℝ) (b : Fin m → ι → ℂ)
    (x y : Fin m → ℝ) :
    hermPair A (∑ a, (x a : ℂ) • b a) (∑ c, (y c : ℂ) • b c) =
      ∑ a, ∑ c, x a * y c * hermPair A (b a) (b c) := by
  unfold hermPair
  simp only [star_sum, star_smul, Complex.star_def, Complex.conj_ofReal, mulVec_sum,
    mulVec_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Complex.re_sum, Complex.re_ofReal_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem sum_periodBasis {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a n : Fin g → ℤ) :
    ∑ i, ((Fin.append a n i : ℤ) : ℂ) • periodBasis τ i = intVecC a + τ *ᵥ intVecC n := by
  rw [Fin.sum_univ_add]
  simp only [periodBasis, Fin.append_left, Fin.append_right]
  congr 1
  · ext l
    simp [intVecC, Finset.sum_apply, Pi.single_apply]
  · have hs : ∀ x, ((n x : ℤ) : ℂ) • (τ *ᵥ Pi.single x (1 : ℂ)) =
        τ *ᵥ (((n x : ℤ) : ℂ) • Pi.single x (1 : ℂ)) := fun x => (mulVec_smul _ _ _).symm
    simp only [hs]
    rw [← mulVec_sum]
    congr 1
    ext l
    simp [intVecC, Finset.sum_apply, Pi.single_apply]

end PeriodLatticeCovolume

open PeriodLatticeCovolume in

theorem PeriodLatticeCovolume.proof : PeriodLatticeCovolume.Statement := by
  intro g τ k v hv hind
  choose a n han using hv
  let N : Matrix (Fin (g + g)) (Fin k) ℤ := fun i j => Fin.append (a j) (n j) i
  have hN : ∀ j, v j = ∑ i, (N i j : ℂ) • periodBasis τ i := fun j => by
    rw [han j]
    exact (sum_periodBasis τ (a j) (n j)).symm
  refine ⟨N, hN, ?_, ?_⟩
  · intro c hc
    rw [Fintype.linearIndependent_iff] at hind
    funext j
    refine hind c ?_ j
    have : ∀ j, c j • v j = ∑ i, ((c j : ℂ) * (N i j : ℂ)) • periodBasis τ i := fun j => by
      rw [hN j, ← Int.cast_smul_eq_zsmul ℂ, Finset.smul_sum]
      simp only [smul_smul]
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_smul]
    have hi := congrFun hc i
    simp only [mulVec, dotProduct, Pi.zero_apply] at hi
    have : ∑ j, (c j : ℂ) * (N i j : ℂ) = ((∑ j, N i j * c j : ℤ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [this, hi]
    simp
  · unfold covolume
    congr 2
    ext j l
    rw [Matrix.of_apply, hN j, hN l]
    have h1 : ∀ j, ∑ i, (N i j : ℂ) • periodBasis τ i
        = ∑ i, (((N i j : ℝ)) : ℂ) • periodBasis τ i := fun j => by
      simp
    rw [h1 j, h1 l, hermPair_comb]
    simp only [intGram, mul_apply, transpose_apply, map_apply, periodGram, Matrix.of_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
    ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPivotBounds
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PivotBounds

theorem qf_submatrix_castLE {d m : ℕ} (h : m ≤ d) (S : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin m → ℝ) :
    MCSchur.qf (S.submatrix (Fin.castLE h) (Fin.castLE h)) x =
      MCSchur.qf S (Function.extend (Fin.castLE h) x 0) := by
  have hinj : Function.Injective (Fin.castLE h) := Fin.castLE_injective h
  set y := Function.extend (Fin.castLE h) x 0 with hy
  have hyc : ∀ a, y (Fin.castLE h a) = x a := fun a => hinj.extend_apply x 0 a
  have hy0 : ∀ b ∉ Set.range (Fin.castLE h), y b = 0 := by
    intro b hb
    rw [hy, Function.extend_apply' _ _ _ (by rintro ⟨a, rfl⟩; exact hb ⟨a, rfl⟩)]
    rfl
  unfold MCSchur.qf
  simp only [dotProduct, mulVec]
  refine Fintype.sum_of_injective _ hinj _ _ (fun b hb => by rw [hy0 b hb, zero_mul]) ?_
  intro a
  rw [hyc]
  congr 1
  refine Fintype.sum_of_injective _ hinj _ _ (fun b hb => by rw [hy0 b hb, mul_zero]) ?_
  intro b
  rw [hyc]
  rfl

end PivotBounds

theorem PivotBounds.proof (hLL : LeadMinorLeading.Statement) (hLB : LeadMinorBasic.Statement)
    (hPI : PivotInvDiag.Statement) (hPL : PivotLast.Statement) : PivotBounds.Statement := by
  intro d S hS i
  have h : (i : ℕ) + 1 ≤ d := i.isLt
  set L := S.submatrix (Fin.castLE h) (Fin.castLE h) with hLdef
  have hL : L.PosDef := hS.submatrix (Fin.castLE_injective h)
  have hpiv : pivot L i = pivot S i := by
    unfold pivot
    rw [hLL d S _ h _ le_rfl, hLL d S _ h _ (Nat.le_succ _)]
  have hlast : Fin.castLE h (Fin.last (i : ℕ)) = i := Fin.ext rfl
  refine ⟨?_, ?_⟩
  · have h1 := hPL i L hL (Pi.single (Fin.last (i : ℕ)) 1)
    rw [hpiv] at h1
    have hq : MCSchur.qf L (Pi.single (Fin.last (i : ℕ)) 1) = S i i := by
      unfold MCSchur.qf
      rw [mulVec_single_one, single_one_dotProduct]
      simp [hLdef, hlast]
    simpa [hq] using h1
  · intro ε hε hy
    have hx : ∀ x : Fin ((i : ℕ) + 1) → ℝ, ε * x (Fin.last (i : ℕ)) ^ 2 ≤ MCSchur.qf L x := by
      intro x
      have := hy (Function.extend (Fin.castLE h) x 0)
      have he := (Fin.castLE_injective h).extend_apply x (0 : Fin d → ℝ) (Fin.last (i : ℕ))
      rw [hlast] at he
      rwa [he, ← PivotBounds.qf_submatrix_castLE] at this
    have hinv := MCCusp.inv_diag_le hL (Fin.last (i : ℕ)) hε hx
    have hone := hPI i L hL
    have hpos : 0 < L⁻¹ (Fin.last (i : ℕ)) (Fin.last (i : ℕ)) := hL.inv.diag_pos
    rw [hpiv] at hone
    set a := L⁻¹ (Fin.last (i : ℕ)) (Fin.last (i : ℕ))
    have hεa : ε * a ≤ 1 := by
      rw [le_div_iff₀ hε] at hinv
      linarith
    have hp : 0 < pivot S i := by
      by_contra hc
      have hc' := not_lt.mp hc
      nlinarith
    nlinarith

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPivotLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem PivotLast.proof (hPI : PivotInvDiag.Statement) : PivotLast.Statement := by
  intro d S hS x
  have h1 := MCCusp.sq_le_inv_diag_mul_qf hS x (Fin.last d)
  have h2 := hPI d S hS
  have hpos : 0 < S⁻¹ (Fin.last d) (Fin.last d) := hS.inv.diag_pos
  have hp : 0 < pivot S d := by
    by_contra hc
    push_neg at hc
    have := mul_nonpos_of_nonneg_of_nonpos hpos.le hc
    linarith
  calc x (Fin.last d) ^ 2 * pivot S d
      ≤ (S⁻¹ (Fin.last d) (Fin.last d) * MCSchur.qf S x) * pivot S d :=
        mul_le_mul_of_nonneg_right h1 hp.le
    _ = MCSchur.qf S x * (S⁻¹ (Fin.last d) (Fin.last d) * pivot S d) := by ring
    _ = MCSchur.qf S x := by rw [h2, mul_one]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPivotProductBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PivotProductBound

theorem pivot_pos (hLB : LeadMinorBasic.Statement) {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosDef) {i : ℕ} (hi : i < d) : 0 < pivot S i :=
  div_pos ((hLB d S).2.2 hS (i + 1) hi) ((hLB d S).2.2 hS i hi.le)

theorem prod_range_pivot (hLB : LeadMinorBasic.Statement) {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosDef) : ∀ r, r ≤ d → ∏ i ∈ Finset.range r, pivot S i = leadMinor S r := by
  intro r
  induction r with
  | zero => intro _; simp [(hLB d S).1]
  | succ n ih =>
    intro hn
    rw [Finset.prod_range_succ, ih (Nat.le_of_succ_le hn), pivot,
      mul_div_cancel₀ _ ((hLB d S).2.2 hS n (Nat.le_of_succ_le hn)).ne']

end PivotProductBound

open PivotProductBound in

theorem PivotProductBound.proof (hLB : LeadMinorBasic.Statement) : PivotProductBound.Statement := by
  intro d r S hS hrd α ε hε hα hεp P hP
  have hpos : ∀ i ∈ P, 0 < pivot S i := fun i hi => pivot_pos hLB hS (hP i hi)
  set m := max 1 α with hm
  set c := min 1 ε with hc
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm1
  have hc0 : 0 < c := lt_min one_pos hε
  have hc1 : c ≤ 1 := min_le_left _ _
  set A := P.filter (· < r) with hA
  set B := P.filter (fun i => ¬ i < r) with hB
  have hAr : A ⊆ Finset.range r := by
    intro i hi
    rw [Finset.mem_filter] at hi
    exact Finset.mem_range.2 hi.2

  have hQpos : ∀ i ∈ Finset.range r \ A, 0 < pivot S i := fun i hi =>
    pivot_pos hLB hS (lt_of_lt_of_le (Finset.mem_range.1 (Finset.mem_sdiff.1 hi).1) hrd)
  have hQ : ∏ i ∈ Finset.range r \ A, pivot S i ≤ m ^ r := by
    calc ∏ i ∈ Finset.range r \ A, pivot S i ≤ ∏ _i ∈ Finset.range r \ A, m :=
          Finset.prod_le_prod (fun i hi => (hQpos i hi).le) (fun i hi =>
            (hα i (Finset.mem_range.1 (Finset.mem_sdiff.1 hi).1)).trans (le_max_right _ _))
      _ = m ^ (Finset.range r \ A).card := Finset.prod_const _
      _ ≤ m ^ r := pow_le_pow_right₀ hm1
          ((Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_range r).le)
  have hL : leadMinor S r = (∏ i ∈ Finset.range r \ A, pivot S i) * ∏ i ∈ A, pivot S i := by
    rw [Finset.prod_sdiff hAr, prod_range_pivot hLB hS r hrd]
  have hApos : 0 < ∏ i ∈ A, pivot S i :=
    Finset.prod_pos fun i hi => hpos i (Finset.mem_filter.1 hi).1

  have h1 : m⁻¹ ^ r * leadMinor S r ≤ ∏ i ∈ A, pivot S i := by
    rw [hL, ← mul_assoc]
    have : m⁻¹ ^ r * ∏ i ∈ Finset.range r \ A, pivot S i ≤ 1 := by
      rw [inv_pow]
      exact inv_mul_le_one_of_le₀ hQ (pow_nonneg hm0.le r)
    calc m⁻¹ ^ r * (∏ i ∈ Finset.range r \ A, pivot S i) * ∏ i ∈ A, pivot S i
        ≤ 1 * ∏ i ∈ A, pivot S i := mul_le_mul_of_nonneg_right this hApos.le
      _ = _ := one_mul _

  have h2 : c ^ d ≤ ∏ i ∈ B, pivot S i := by
    have hBd : B.card ≤ d := by
      calc B.card ≤ (Finset.range d).card := Finset.card_le_card (fun i hi =>
            Finset.mem_range.2 (hP i (Finset.mem_filter.1 hi).1))
        _ = d := Finset.card_range d
    calc c ^ d ≤ c ^ B.card := pow_le_pow_of_le_one hc0.le hc1 hBd
      _ = ∏ _i ∈ B, c := (Finset.prod_const _).symm
      _ ≤ ∏ i ∈ B, pivot S i := Finset.prod_le_prod (fun _ _ => hc0.le) (fun i hi => by
          rw [Finset.mem_filter] at hi
          exact (min_le_right _ _).trans (hεp i (not_lt.1 hi.2) (hP i hi.1)))
  rw [← Finset.prod_filter_mul_prod_filter_not P (· < r), mul_assoc, mul_comm]
  exact mul_le_mul h1 h2 (pow_nonneg hc0.le d) hApos.le

end

end GroundTheory.Heights₂.Heights
end

