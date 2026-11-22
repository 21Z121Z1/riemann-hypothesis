import Formalism.YangianSpanCharacter.Bundle0001

-- bundled from Formalism.YangianSpanCharacter.YangianRTTProofs.RttRelation
section
namespace Formalism.YangianSpanCharacter.P

open Matrix Formalism.YangianSpanCharacter.T

set_option linter.unusedSimpArgs false in
theorem rttRelation : Formalism.YangianSpanCharacter.T.RTT := by
  intro R A _ _ _ p c ci Y Y' hW
  obtain ⟨hcc, hcc', hpc⟩ := hW
  have hpc2 : ∀ x : A, p * (c * x) = c * (p * x) + c * x := fun x => by
    rw [← mul_assoc, hpc, add_mul, mul_assoc]
  have hpci : p * ci = ci * p - ci := by
    have h := congrArg (fun x => ci * x * ci) hpc
    simp only [mul_add, add_mul, ← mul_assoc, hcc', one_mul] at h
    simp only [mul_assoc, hcc, mul_one] at h
    rw [h]; abel
  have hpci2 : ∀ x : A, p * (ci * x) = ci * (p * x) - ci * x := fun x => by
    rw [← mul_assoc, hpci, sub_mul, mul_assoc]
  have hcc2 : ∀ x : A, c * (ci * x) = x := fun x => by rw [← mul_assoc, hcc, one_mul]
  have hcc2' : ∀ x : A, ci * (c * x) = x := fun x => by rw [← mul_assoc, hcc', one_mul]
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, T1, T2, Pf, Tm,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  all_goals
    simp only [Algebra.algebraMap_eq_smul_one, mul_add, add_mul, mul_sub, sub_mul, neg_mul,
      mul_neg, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc, smul_add, smul_sub,
      smul_neg, smul_smul, hpc, hpc2, hpci, hpci2, hcc, hcc', hcc2, hcc2', neg_neg, sub_smul]
  all_goals module

end Formalism.YangianSpanCharacter.P
end

-- bundled from Formalism.YangianSpanCharacter.YangianRTTProofs.SpanCharacterIdentity
section
namespace Formalism.YangianSpanCharacter.P

open Finset

theorem gamma_ratio_identity : Formalism.YangianSpanCharacter.E.GGRatio := by
  intro g hg k
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi1 : i ≠ 0 := by
    have := (Finset.mem_Ico.mp hi).1; omega
  have hgi : 1 < g ^ i := one_lt_pow₀ hg hi1
  have h0 : g ^ i ≠ 0 := by positivity
  have h1 : g ^ i - 1 ≠ 0 := by linarith
  have h2 : 1 - (g ^ i)⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : g ^ i = 1 := by rw [eq_comm, inv_eq_one] at h; exact h
    linarith
  field_simp

private lemma weier {ι : Type} (s : Finset ι) (a : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ a i)
    (h1 : ∀ i ∈ s, a i ≤ 1) : 1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have haj0 := h0 j (Finset.mem_insert_self j s)
    have haj1 := h1 j (Finset.mem_insert_self j s)
    have hS : 0 ≤ ∑ i ∈ s, a i :=
      Finset.sum_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have := mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr haj1)
    nlinarith

private lemma geom_le (g : ℝ) (hg : 3 ≤ g) (k : ℕ) :
    ∑ i ∈ Finset.Ico 1 k, (g ^ i)⁻¹ ≤ 1 / (g - 1) := by
  have hr0 : 0 < g⁻¹ := by positivity
  have hr1 : g⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  simp_rw [← inv_pow]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Finset.Ico_eq_empty_of_le (Nat.zero_le 1), Finset.sum_empty]
    exact div_nonneg zero_le_one (by linarith)
  · have hm := geom_sum_Ico_mul g⁻¹ (show 1 ≤ k from hk)
    have hS : (∑ i ∈ Finset.Ico 1 k, g⁻¹ ^ i) * (1 - g⁻¹) ≤ g⁻¹ := by
      have : 0 ≤ g⁻¹ ^ k := by positivity
      nlinarith
    have hpos : 0 < 1 - g⁻¹ := by linarith
    have he : 1 / (g - 1) = g⁻¹ / (1 - g⁻¹) := by
      have : g ≠ 0 := by linarith
      have : g - 1 ≠ 0 := by linarith
      field_simp
    rw [he, le_div_iff₀ hpos]
    exact hS

theorem gamma_product_identity : Formalism.YangianSpanCharacter.E.GGProd := by
  intro g hg k
  have hg0 : 0 < g := by linarith
  rw [Finset.prod_inv_distrib]
  have hW := weier (Finset.Ico 1 k) (fun i => (g ^ i)⁻¹)
    (fun i _ => by positivity)
    (fun i hi => by
      have hi1 : i ≠ 0 := by
        have := (Finset.mem_Ico.mp hi).1; omega
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith)))
  have hG := geom_le g hg k
  have hq : g / (g + 3) ≤ 1 - 1 / (g - 1) := by
    have h1 : 0 < g - 1 := by linarith
    have h3 : 0 < g + 3 := by linarith
    rw [div_le_iff₀ h3, sub_mul, div_mul_eq_mul_div, one_mul, le_sub_iff_add_le,
      ← le_sub_iff_add_le', div_le_iff₀ h1]
    nlinarith
  have hP : g / (g + 3) ≤ ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹) := by
    have hW' : 1 - ∑ i ∈ Finset.Ico 1 k, (g ^ i)⁻¹ ≤ ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹) := hW
    linarith
  have hPpos : 0 < ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹) :=
    lt_of_lt_of_le (by positivity) hP
  rw [inv_le_comm₀ hPpos (by positivity)]
  have : (1 + 3 / g)⁻¹ = g / (g + 3) := by
    field_simp
  rw [this]; exact hP

private lemma rep_eq {K V : Type} [Field K] [AddCommGroup V] [Module K V] (n : ℕ)
    (f f' : Fin n → V) (hli : LinearIndependent K (Sum.elim f f')) (p q p' q' : Fin n → K)
    (h : ∑ i, (p i • f i + q i • f' i) = ∑ i, (p' i • f i + q' i • f' i)) :
    ∀ i, p i = p' i ∧ q i = q' i := by
  have key := (Fintype.linearIndependent_iffₛ.mp hli) (Sum.elim p q) (Sum.elim p' q')
    (by simpa [Fintype.sum_sum_type, Finset.sum_add_distrib] using h)
  exact fun i => ⟨key (Sum.inl i), key (Sum.inr i)⟩

end Formalism.YangianSpanCharacter.P
end

-- bundled from Formalism.YangianSpanCharacter.YangianRTTProofs.TransposeSymplecticShift
section
namespace Formalism.YangianSpanCharacter.P

open Matrix

theorem transposeSymplecticShift : Formalism.YangianSpanCharacter.T.TJT := by
  intro R A _ _ _ p c ci Y h
  obtain ⟨h1, h2, h3⟩ := h
  have hpci : p * ci = ci * p - ci := by
    have : ci * (p * c) * ci = ci * (c * p + c) * ci := by rw [h3]
    have e1 : ci * (p * c) * ci = ci * p := by
      rw [mul_assoc, mul_assoc, h1, mul_one]
    have e2 : ci * (c * p + c) * ci = p * ci + ci := by
      rw [mul_add, add_mul, ← mul_assoc ci c p, h2, one_mul, one_mul]
    rw [e1, e2] at this
    rw [this]; abel
  have hc : ∀ x : A, algebraMap R A Y * x = x * algebraMap R A Y := fun x => Algebra.commutes Y x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.Tm, Formalism.YangianSpanCharacter.T.J, map_add, add_mul, mul_add]
  all_goals first
    | exact h1
    | exact h2
    | (rw [hpci, hc ci]; abel)

theorem planeWaveIntertwining : Formalism.YangianSpanCharacter.T.PlaneWave := by
  intro R A _ _ _ p c ci f s Y hfc hfci hpf
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two]
  · have key : c * f * algebraMap R A s = algebraMap R A s * f * c := by
      rw [← hfc, mul_assoc, ← Algebra.commutes, ← mul_assoc]
      exact congrArg (· * c) (Algebra.commutes s f).symm
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.YangianSpanCharacter.T.Tm, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two, hfc, hfci] <;>
      simp only [mul_add, add_mul, mul_neg, neg_mul, hpf, key, Algebra.commutes] <;>
      first | noncomm_ring | abel

theorem unipotentSymplectic : Formalism.YangianSpanCharacter.T.UJU := by
  intro R A _ _ _ s
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]

theorem isWeylTripleShiftModel : Formalism.YangianSpanCharacter.T.WeylModel := by
  refine ⟨?_, ?_, ?_⟩
  · refine LinearMap.ext fun f => funext fun n => ?_
    simp [Formalism.YangianSpanCharacter.T.cM, Formalism.YangianSpanCharacter.T.ciM, LinearMap.funLeft_apply]
  · refine LinearMap.ext fun f => funext fun n => ?_
    simp [Formalism.YangianSpanCharacter.T.cM, Formalism.YangianSpanCharacter.T.ciM, LinearMap.funLeft_apply]
  · refine LinearMap.ext fun f => funext fun n => ?_
    simp [Formalism.YangianSpanCharacter.T.cM, Formalism.YangianSpanCharacter.T.pM, LinearMap.funLeft_apply]
    ring

end Formalism.YangianSpanCharacter.P
end

