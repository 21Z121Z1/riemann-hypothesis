import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0003
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0004

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LocalA
section
noncomputable section

open Matrix Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section LogL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma lcA_exp_strict :
    HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)) 0 := by
  first
  | exact hasStrictFDerivAt_exp_zero
  | exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ)
  | (rw [ContinuousLinearEquiv.coe_refl]; exact hasStrictFDerivAt_exp_zero)
  | (rw [ContinuousLinearEquiv.coe_refl]; exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ))

lemma exists_local_matrix_log : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ (∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (ℓ k) = k) ∧
      (∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ℓ (NormedSpace.exp Y) = Y) := by
  have hf := lcA_exp_strict (n := n)
  refine ⟨hf.localInverse _ _ _, ?_, ?_, hf.eventually_left_inverse⟩
  · have h1 := hf.localInverse_continuousAt.tendsto
    have h2 := hf.localInverse_apply_image
    rw [NormedSpace.exp_zero] at h1 h2
    rwa [h2] at h1
  · have h := hf.eventually_right_inverse
    rwa [NormedSpace.exp_zero] at h

lemma continuous_matrix_exp_alt :
    Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  first
  | exact NormedSpace.exp_continuous
  | exact NormedSpace.exp_continuous (𝕂 := ℂ)
  | exact exp_continuous

end LogL

lemma lcA_exists_log : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ (∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (ℓ k) = k) ∧
      (∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ℓ (NormedSpace.exp Y) = Y) := by
  first
  | exact exists_local_matrix_log
  | exact exists_local_matrix_log (n := n)

lemma lcA_exists_klog (ε : Fin n → Bool) : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ ∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ),
      k ∈ Kset ε → inK ε (ℓ k) ∧ NormedSpace.exp (ℓ k) = k := by
  obtain ⟨L, hL1, hL2, hL3⟩ := lcA_exists_log (n := n)
  refine ⟨L, hL1, ?_⟩
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hA : Tendsto (fun k => (L k)ᴴ) (𝓝 1) (𝓝 0) := by
    have h := hL1.star
    rw [star_zero] at h
    exact h
  have hB : Tendsto (fun k => -(L k)) (𝓝 1) (𝓝 0) := by
    have h := hL1.neg
    rw [neg_zero] at h
    exact h
  have hC : Tendsto (fun k => Jm ε * L k * Jm ε) (𝓝 1) (𝓝 0) := by
    have h := (hL1.const_mul (Jm ε)).mul_const (Jm ε)
    rw [mul_zero, zero_mul] at h
    exact h
  filter_upwards [hL2, hA.eventually hL3, hB.eventually hL3, hC.eventually hL3] with k h2 hA' hB' hC' hk
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Jm ε = Jm ε * k := hk
  have hkk : kᴴ * k = 1 := by
    have h := hk'.1
    rw [Matrix.mem_unitaryGroup_iff'] at h
    exact h
  have e1 : NormedSpace.exp ((L k)ᴴ) = kᴴ := by rw [Matrix.exp_conjTranspose, h2]
  have e2 : NormedSpace.exp (-(L k)) = kᴴ := by
    rw [Matrix.exp_neg, h2]
    exact Matrix.inv_eq_left_inv hkk
  have hstar : (L k)ᴴ = -(L k) := by
    rw [← hA', e1, ← e2, hB']
  have e3 : NormedSpace.exp (Jm ε * L k * Jm ε) = NormedSpace.exp (L k) := by
    have h := Matrix.exp_conj (Jm ε) (L k) hJu
    rw [hJinv] at h
    rw [h, h2, mul_assoc, hk'.2, ← mul_assoc, hJJ, one_mul]
  have e4 : Jm ε * L k * Jm ε = L k := by
    rw [← hC', e3, h2]
  have hcomm : L k * Jm ε = Jm ε * L k := by
    calc L k * Jm ε = Jm ε * L k * Jm ε * Jm ε := by rw [e4]
      _ = Jm ε * L k := by rw [mul_assoc, hJJ, mul_one]
  refine ⟨⟨?_, hcomm⟩, h2⟩
  show (L k)ᴴ * Jm ε + Jm ε * L k = 0
  rw [hstar, neg_mul, ← hcomm]
  first
  | exact neg_add_cancel _
  | simp

open scoped Matrix.Norms.L2Operator in
lemma lcA_polarL_continuousOn (ε : Fin n → Bool) :
    ContinuousOn (PolarDecomposition.polar_L (n := n)) {g | inUJ ε g} := by
  have h : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => CFC.log (gᴴ * g)) {g | inUJ ε g} := by
    refine CFC.continuousOn_log.comp (by fun_prop) ?_
    intro g hg
    obtain ⟨hsa, hu, -⟩ := PolarDecomposition.polar_isSelfAdjoint_isUnit_spectrum_pos hg
    exact ⟨hsa, hu⟩
  exact h.const_smul (1 / 2 : ℝ)

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private lemma tele_range (D : ℕ → ℂ) (hD : ∀ l, D l ≠ 0) (m : ℕ → ℤ) (N : ℕ) :
    ∏ i ∈ range N, (∏ l ∈ range (i + 1), D l) ^ (-(m i - m (i + 1))) =
      (∏ l ∈ range N, D l ^ (-m l)) * (∏ l ∈ range N, D l) ^ m N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ (fun i => (∏ l ∈ range (i + 1), D l) ^ (-(m i - m (i + 1)))) N, ih]
    simp only [Finset.prod_range_succ]
    have hP : (∏ l ∈ range N, D l) ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => hD l
    have hPd : (∏ l ∈ range N, D l) * D N ≠ 0 := mul_ne_zero hP (hD N)
    have h1 : ((∏ l ∈ range N, D l) * D N) ^ (-(m N - m (N + 1))) =
        ((∏ l ∈ range N, D l) * D N) ^ (-m N) * ((∏ l ∈ range N, D l) * D N) ^ (m (N + 1)) := by
      rw [← zpow_add₀ hPd]
      congr 1
      ring
    have h2 : ((∏ l ∈ range N, D l) * D N) ^ (-m N) =
        (∏ l ∈ range N, D l) ^ (-m N) * D N ^ (-m N) := mul_zpow _ _ _
    have h3 : (∏ l ∈ range N, D l) ^ m N * (∏ l ∈ range N, D l) ^ (-m N) = 1 := by
      rw [← zpow_add₀ hP, add_neg_cancel, zpow_zero]
    rw [h1, h2]
    linear_combination ((∏ l ∈ range N, D l ^ (-m l)) * D N ^ (-m N) *
      ((∏ l ∈ range N, D l) * D N) ^ m (N + 1)) * h3

private lemma filter_prod_eq_range (d : Fin n → ℂ) (k : ℕ) (hk : k ≤ n) :
    ∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < k), d l =
      ∏ j ∈ range k, (if h : j < n then d ⟨j, h⟩ else 1) := by
  have hr : range k = (range n).filter (fun j => j < k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor <;> intro h <;> omega
  rw [hr]
  simp only [Finset.prod_filter]
  rw [Finset.prod_range]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [l.2]

private lemma tele_fin (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) (μ : Fin n → ℤ) :
    ∏ i : Fin n, (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), d l) ^ (-(μ i - muNext μ i)) =
      ∏ l, d l ^ (-μ l) := by
  set D : ℕ → ℂ := fun j => if h : j < n then d ⟨j, h⟩ else 1 with hDdef
  set m : ℕ → ℤ := fun j => if h : j < n then μ ⟨j, h⟩ else 0 with hmdef
  have hD : ∀ l, D l ≠ 0 := by
    intro l
    simp only [hDdef]
    split_ifs
    · exact hd _
    · exact one_ne_zero
  have h1 : ∀ i : Fin n, (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), d l) ^
      (-(μ i - muNext μ i)) = (∏ l ∈ range ((i : ℕ) + 1), D l) ^ (-(m i - m ((i : ℕ) + 1))) := by
    intro i
    rw [filter_prod_eq_range d _ (by have := i.2; omega)]
    congr 1
    all_goals first | rfl | simp [hmdef, muNext, i.2]
  rw [Finset.prod_congr rfl (fun i _ => h1 i),
    Fin.prod_univ_eq_prod_range (fun i => (∏ l ∈ range (i + 1), D l) ^ (-(m i - m (i + 1)))) n,
    tele_range D hD m n]
  have hmn : m n = 0 := by simp [hmdef]
  rw [hmn, zpow_zero, mul_one, Finset.prod_range (fun l => D l ^ (-m l))]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [hDdef, hmdef, l.2]

private lemma lead_differentiable_lemma (i : ℕ) :
    Differentiable ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => lead i z) := by
  have hent : ∀ a b : Fin n, Differentiable ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => z a b) := by
    intro a b
    let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun M => M a b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap L).differentiable
  unfold lead
  split_ifs with h
  · simp only [Matrix.det_apply', Matrix.submatrix_apply]
    fun_prop
  · exact differentiable_const _

theorem isOpen_omega : IsOpen (OmegaSet n) := by
  have : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun (lead_differentiable_lemma _).continuous continuous_const

theorem posSet_subset_omega : posSet n ⊆ OmegaSet n := by
  intro x hx i h
  have := (lead_posDef hx ((i : ℕ) + 1) (by have := i.2; omega)).1
  rw [h] at this
  simp at this

theorem phiM_differentiableOn (μ : Fin n → ℤ) : DifferentiableOn ℂ (PhiM μ) (OmegaSet n) := by
  intro z hz
  have hz' : ∀ i : Fin n, lead ((i : ℕ) + 1) z ≠ 0 := hz
  have hL : ∀ i : ℕ, Differentiable ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => lead i z) :=
    fun i => lead_differentiable_lemma i
  have hq : DifferentiableAt ℂ (PhiM μ) z := by
    unfold PhiM
    fun_prop (disch := exact Or.inl (hz' _))
  exact hq.differentiableWithinAt

theorem phiM_tri_mul (μ : Fin n → ℤ) {c z c' : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c) (hc' : IsUpperTri c')
    (hcd : ∀ l, c l l ≠ 0) (hcd' : ∀ l, c' l l ≠ 0) (hz : z ∈ OmegaSet n) :
    c * z * c' ∈ OmegaSet n ∧
      PhiM μ (c * z * c') = (∏ l, (c l l * c' l l) ^ (-μ l)) * PhiM μ z := by
  have hd : ∀ l, c l l * c' l l ≠ 0 := fun l => mul_ne_zero (hcd l) (hcd' l)
  have hlead : ∀ i : Fin n, lead ((i : ℕ) + 1) (c * z * c') =
      (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), c l l * c' l l) * lead ((i : ℕ) + 1) z :=
    fun i => lead_tri_mul hc hc' _ i.isLt
  have hP : ∀ i : Fin n,
      (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), c l l * c' l l) ≠ 0 :=
    fun i => prod_ne_zero_iff.mpr fun l _ => hd l
  refine ⟨fun i => by rw [hlead i]; exact mul_ne_zero (hP i) (hz i), ?_⟩
  have hterm : ∀ i : Fin n, lead ((i : ℕ) + 1) (c * z * c') ^ (-(μ i - muNext μ i)) =
      (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), c l l * c' l l) ^ (-(μ i - muNext μ i)) *
        lead ((i : ℕ) + 1) z ^ (-(μ i - muNext μ i)) := fun i => by rw [hlead i, mul_zpow]
  unfold PhiM
  rw [prod_congr rfl fun i _ => hterm i, prod_mul_distrib,
    tele_fin (fun l => c l l * c' l l) hd μ]

theorem phiM_posDef (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    0 < (PhiM μ x).re ∧ (PhiM μ x).im = 0 := by
  have hpos : ∀ i : Fin n, 0 < (lead ((i : ℕ) + 1) x).re :=
    fun i => (lead_posDef hx _ (by have := i.2; omega)).1
  have hr : ∀ i : Fin n, lead ((i : ℕ) + 1) x = ((lead ((i : ℕ) + 1) x).re : ℂ) := by
    intro i
    apply Complex.ext
    · simp
    · simp [(lead_posDef hx ((i : ℕ) + 1) (by have := i.2; omega)).2]
  have hP : PhiM μ x = ((∏ i : Fin n, (lead ((i : ℕ) + 1) x).re ^ (-(μ i - muNext μ i)) : ℝ) : ℂ) := by
    unfold PhiM
    push_cast
    exact Finset.prod_congr rfl fun i _ => by rw [← hr i]
  rw [hP, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨Finset.prod_pos fun i _ => zpow_pos (hpos i) _, rfl⟩

theorem phiM_one (μ : Fin n → ℤ) : PhiM μ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold PhiM
  have h1 : ∀ i : Fin n, lead ((i : ℕ) + 1) (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    intro i
    unfold lead
    rw [dif_pos (by have := i.2; omega), Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one]
  simp [h1]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

