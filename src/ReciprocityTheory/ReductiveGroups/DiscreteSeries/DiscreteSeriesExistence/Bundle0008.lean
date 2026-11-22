import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0003
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0013
import Formalism.HermitianCurvature.StatementB

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroCayleyA
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

section CayleyAux

variable {n : ℕ}

def szcMk (τ : Fin n → Fin n) (d o : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (if j = i then d i else 0) + (if j = τ i then o i else 0)

theorem szcMk_mul_apply (τ : Fin n → Fin n) (d o : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) : (szcMk τ d o * M) i j = d i * M i j + o i * M (τ i) j := by
  rw [Matrix.mul_apply]
  simp only [szcMk, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem szcMk_mul (τ : Fin n → Fin n) (hτ : ∀ i, τ (τ i) = i) (d o d' o' : Fin n → ℂ) :
    szcMk τ d o * szcMk τ d' o' =
      szcMk τ (fun i => d i * d' i + o i * o' (τ i)) (fun i => d i * o' i + o i * d' (τ i)) := by
  ext i j
  rw [szcMk_mul_apply]
  simp only [szcMk, hτ]
  split_ifs <;> ring

theorem szcMk_conjTranspose (τ : Fin n → Fin n) (hτ : ∀ i, τ (τ i) = i) (d o : Fin n → ℂ) :
    (szcMk τ d o)ᴴ = szcMk τ (fun i => star (d i)) (fun i => star (o (τ i))) := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  simp only [szcMk]
  have key : (i = τ j) ↔ (j = τ i) := ⟨fun h => by rw [h, hτ], fun h => by rw [h, hτ]⟩
  by_cases h1 : j = i
  · subst h1
    by_cases h : j = τ j
    · simp [← h]
    · simp [h]
  · by_cases h2 : j = τ i
    · subst h2
      simp [hτ, h1, Ne.symm h1]
    · have h3 : ¬ i = τ j := fun h => h2 (key.mp h)
      simp [h1, Ne.symm h1, h2, h3]

theorem szcMk_zero (τ : Fin n → Fin n) (d : Fin n → ℂ) : szcMk τ d 0 = Matrix.diagonal d := by
  ext i j
  simp only [szcMk, Matrix.diagonal_apply, Pi.zero_apply, ite_self, add_zero]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

end CayleyAux

section Cayley48

def szcTau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if i.val < r ∨ r + k < i.val then ⟨2 * r + k - i.val, by omega⟩ else i

theorem szcTau_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (szcTau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := by
  unfold szcTau; split_ifs <;> rfl

theorem szc_tau_pos {k r : ℕ} {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) :
    (szcTau k r i).val = 2 * r + k - i.val := by
  rw [szcTau_val, if_pos h]

theorem szc_tau_neg {k r : ℕ} {i : Fin (2 * r + k + 1)} (h : ¬ (i.val < r ∨ r + k < i.val)) :
    szcTau k r i = i := by
  unfold szcTau; rw [if_neg h]

theorem szcTau_tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : szcTau k r (szcTau k r i) = i := by
  have := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · apply Fin.ext
    have h' : (szcTau k r i).val < r ∨ r + k < (szcTau k r i).val := by rw [szc_tau_pos h]; omega
    rw [szc_tau_pos h', szc_tau_pos h]
    omega
  · rw [szc_tau_neg h, szc_tau_neg h]

def szcS : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)

theorem szcS_sq : szcS * szcS = 1 / 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2 : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (1 / 2 : ℝ) := by nlinarith [h]
  unfold szcS
  rw [← Complex.ofReal_mul, h2]
  push_cast
  ring

theorem szcS_star : star szcS = szcS := by
  unfold szcS
  rw [Complex.star_def]
  exact Complex.conj_ofReal _

def szcC (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then szcS else if r + k < i.val then -szcS else 1

def szcO (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r ∨ r + k < i.val then szcS else 0

def szcHD (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r ∨ r + k < i.val then 0 else if i.val = r + k then -1 else 1

def szcHO (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r ∨ r + k < i.val then 1 else 0

def szcD (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r + k then 1 else -1

theorem szcO_tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : szcO k r (szcTau k r i) = szcO k r i := by
  have := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · unfold szcO; rw [szc_tau_pos h]; split_ifs <;> first | rfl | omega
  · rw [szc_tau_neg h]

theorem szcHO_tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : szcHO k r (szcTau k r i) = szcHO k r i := by
  have := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · unfold szcHO; rw [szc_tau_pos h]; split_ifs <;> first | rfl | omega
  · rw [szc_tau_neg h]

theorem szcHD_tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : szcHD k r (szcTau k r i) = szcHD k r i := by
  have := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · unfold szcHD; rw [szc_tau_pos h]; split_ifs <;> first | rfl | omega
  · rw [szc_tau_neg h]

theorem szcC_tau (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    szcC k r (szcTau k r i) = if i.val < r then -szcS else if r + k < i.val then szcS else 1 := by
  have := i.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · unfold szcC; rw [szc_tau_pos h]; split_ifs <;> first | rfl | omega
  · rw [szc_tau_neg h]; unfold szcC; split_ifs <;> first | rfl | omega

theorem szc_Hpk (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r = szcMk (szcTau k r) (szcHD k r) (szcHO k r) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  by_cases h : i.val < r ∨ r + k < i.val
  · have ht := szc_tau_pos h
    simp only [Formalism.QuantumDeterminants.Hpk, szcMk, szcHD, szcHO, Fin.ext_iff, ht]
    split_ifs <;> first | omega | norm_num
  · have ht := szc_tau_neg h
    simp only [Formalism.QuantumDeterminants.Hpk, szcMk, szcHD, szcHO, ht, Fin.ext_iff]
    split_ifs <;> first | omega | norm_num

theorem szc_CC (k r : ℕ) :
    szcMk (szcTau k r) (szcC k r) (szcO k r) * szcMk (szcTau k r) (szcC k r) (szcO k r) = 1 := by
  rw [szcMk_mul _ (szcTau_tau k r), ← Matrix.diagonal_one, ← szcMk_zero (szcTau k r)]
  congr 1
  · funext i
    have := i.isLt
    simp only [szcO_tau]
    unfold szcC szcO
    split_ifs <;> first | omega | ring1 | linear_combination 2 * szcS_sq
  · funext i
    have := i.isLt
    simp only [szcC_tau, Pi.zero_apply]
    unfold szcC szcO
    split_ifs <;> first | omega | ring1

theorem szc_Cstar (k r : ℕ) :
    (szcMk (szcTau k r) (szcC k r) (szcO k r))ᴴ = szcMk (szcTau k r) (szcC k r) (szcO k r) := by
  rw [szcMk_conjTranspose _ (szcTau_tau k r)]
  congr 1
  · funext i; unfold szcC; split_ifs <;> simp [szcS_star]
  · funext i; simp only [szcO_tau]; unfold szcO; split_ifs <;> simp [szcS_star]

theorem szc_CHC (k r : ℕ) :
    szcMk (szcTau k r) (szcC k r) (szcO k r) * Formalism.QuantumDeterminants.Hpk k r *
      szcMk (szcTau k r) (szcC k r) (szcO k r) = Matrix.diagonal (szcD k r) := by
  rw [szc_Hpk, szcMk_mul _ (szcTau_tau k r), szcMk_mul _ (szcTau_tau k r), ← szcMk_zero (szcTau k r)]
  congr 1
  · funext i
    have := i.isLt
    simp only [szcO_tau, szcHO_tau, szcHD_tau]
    unfold szcC szcO szcHD szcHO szcD
    split_ifs <;> first | omega | ring1 | linear_combination 2 * szcS_sq |
      linear_combination (-2) * szcS_sq
  · funext i
    have := i.isLt
    simp only [szcHO_tau, szcHD_tau, szcC_tau, Pi.zero_apply]
    unfold szcC szcO szcHD szcHO
    split_ifs <;> first | omega | ring1

def szcEqvF (k r : ℕ) (hk : 1 ≤ k) :
    {i : Fin (2 * r + k + 1) // Formalism.MainNotions.CayleySignature.eps48 k r i = false} ≃ Fin (r + 1) where
  toFun i := ⟨(i.1.val - k) / 2, by have := i.1.isLt; omega⟩
  invFun b := ⟨⟨k + 2 * b.val, by have := b.isLt; omega⟩, by
    have hb : ¬ (k + 2 * b.val < k - 1) := by omega
    have hb2 : ¬ ((k + 2 * b.val - (k - 1)) % 2 = 0) := by omega
    simp [Formalism.MainNotions.CayleySignature.eps48, hb, hb2]⟩
  left_inv i := by
    obtain ⟨i, hi⟩ := i
    have hlt := i.isLt
    have h1 : ¬ (i.val < k - 1) := by
      intro h1; simp [Formalism.MainNotions.CayleySignature.eps48, h1] at hi
    have h2 : ¬ ((i.val - (k - 1)) % 2 = 0) := by
      intro h2; simp [Formalism.MainNotions.CayleySignature.eps48, h1, h2] at hi
    apply Subtype.ext
    apply Fin.ext
    show k + 2 * ((i.val - k) / 2) = i.val
    omega
  right_inv b := by
    apply Fin.ext
    show (k + 2 * b.val - k) / 2 = b.val
    omega

def szcEqvT (k r : ℕ) : {j : Fin (2 * r + k + 1) // r + k ≤ j.val} ≃ Fin (r + 1) where
  toFun j := ⟨j.1.val - (r + k), by have := j.1.isLt; omega⟩
  invFun b := ⟨⟨r + k + b.val, by have := b.isLt; omega⟩, by show r + k ≤ r + k + b.val; omega⟩
  left_inv j := by
    obtain ⟨j, hj⟩ := j
    apply Subtype.ext
    apply Fin.ext
    show r + k + (j.val - (r + k)) = j.val
    omega
  right_inv b := by
    apply Fin.ext
    show r + k + b.val - (r + k) = b.val
    omega

theorem szc_exists_perm (k r : ℕ) (hk : 1 ≤ k) :
    ∃ π : Fin (2 * r + k + 1) ≃ Fin (2 * r + k + 1),
      ∀ i, (Formalism.MainNotions.CayleySignature.eps48 k r i = false ↔ r + k ≤ (π i).val) := by
  classical
  let e : {i : Fin (2 * r + k + 1) // Formalism.MainNotions.CayleySignature.eps48 k r i = false} ≃
      {j : Fin (2 * r + k + 1) // r + k ≤ j.val} := (szcEqvF k r hk).trans (szcEqvT k r).symm
  have hc : Fintype.card {i : Fin (2 * r + k + 1) // ¬ Formalism.MainNotions.CayleySignature.eps48 k r i = false} =
      Fintype.card {j : Fin (2 * r + k + 1) // ¬ r + k ≤ j.val} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_congr e]
  obtain ⟨f⟩ := Fintype.card_eq.mp hc
  refine ⟨Equiv.subtypeCongr e f, fun i => ?_⟩
  by_cases h : Formalism.MainNotions.CayleySignature.eps48 k r i = false
  · have hx : Equiv.subtypeCongr e f i = (e ⟨i, h⟩ : Fin (2 * r + k + 1)) := by
      simp [Equiv.subtypeCongr, h]
    rw [hx]
    exact ⟨fun _ => (e ⟨i, h⟩).2, fun _ => h⟩
  · have hx : Equiv.subtypeCongr e f i = (f ⟨i, h⟩ : Fin (2 * r + k + 1)) := by
      simp [Equiv.subtypeCongr, h]
    rw [hx]
    exact ⟨fun h' => absurd h' h, fun h' => absurd h' (f ⟨i, h⟩).2⟩

end Cayley48

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroTopA
section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def sztJd (ε : Fin n → Bool) : Fin n → ℂ := fun a => if ε a then 1 else -1

theorem szt_Jm_eq (ε : Fin n → Bool) : Jm ε = Matrix.diagonal (sztJd ε) := rfl

theorem szt_jd_sq (ε : Fin n → Bool) (a : Fin n) : sztJd ε a * sztJd ε a = 1 := by
  unfold sztJd
  split_ifs <;> norm_num

theorem szt_lead_Jconj (ε : Fin n → Bool) (z : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) :
    S7.lead i (Jm ε * z * Jm ε) = S7.lead i z := by
  unfold S7.lead
  split_ifs with h
  · have hsub : (Jm ε * z * Jm ε).submatrix (Fin.castLE h) (Fin.castLE h) =
        Matrix.diagonal (sztJd ε ∘ Fin.castLE h) * z.submatrix (Fin.castLE h) (Fin.castLE h) *
          Matrix.diagonal (sztJd ε ∘ Fin.castLE h) := by
      rw [szt_Jm_eq]
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Function.comp_apply]
    rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hA : (∏ a, (sztJd ε ∘ Fin.castLE h) a) * (∏ a, (sztJd ε ∘ Fin.castLE h) a) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun a _ => szt_jd_sq ε _
    calc (∏ a, (sztJd ε ∘ Fin.castLE h) a) * (z.submatrix (Fin.castLE h) (Fin.castLE h)).det *
          (∏ a, (sztJd ε ∘ Fin.castLE h) a)
        = ((∏ a, (sztJd ε ∘ Fin.castLE h) a) * (∏ a, (sztJd ε ∘ Fin.castLE h) a)) *
            (z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by ring
      _ = (z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by rw [hA, one_mul]
  · rfl

theorem szt_phiM_Jconj (ε : Fin n → Bool) (μ : Fin n → ℤ) (z : Matrix (Fin n) (Fin n) ℂ) :
    S7.PhiM μ (Jm ε * z * Jm ε) = S7.PhiM μ z := by
  unfold S7.PhiM
  simp only [szt_lead_Jconj]

theorem szt_phiM_inv_conj {ε : Fin n → Bool} (μ : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X)
    (k : S7.KG ε) :
    S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k)⁻¹ =
      S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k) := by
  obtain ⟨hY, hE⟩ := S7.inP_conj k⁻¹ hX
  simp only [inv_inv] at hY hE
  rw [← hE, Matrix.inv_eq_left_inv (PolarDecomposition.polar_exp_neg_mul _), ← S7.inP_JXJ hY,
    PolarDecomposition.polar_exp_Jconj, szt_phiM_Jconj]

section Cayley

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem szt_unitary (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) : Pᴴ * P = 1 ∧ P * Pᴴ = 1 := by
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  refine ⟨?_, ?_⟩
  · have := (Matrix.mem_unitaryGroup_iff' (A := P)).mp hPu
    simpa [Matrix.star_eq_conjTranspose] using this
  · have := (Matrix.mem_unitaryGroup_iff (A := P)).mp hPu
    simpa [Matrix.star_eq_conjTranspose] using this

theorem szt_conj_mem (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : P * g * P⁻¹ ∈ UJset ε := by
  rw [← mir_UJset_eq]
  obtain ⟨e1, e2⟩ := szt_unitary hP
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv e1
  have hc : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  rw [hinv]
  calc (P * g * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (P * g * Pᴴ)
      = P * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * Pᴴ := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = P * Pᴴ * Formalism.REAL.Jm ε * (P * Pᴴ) := by
        rw [hc, hg', ← hc]; simp [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [e2]; simp

theorem szt_hs_conj (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    S7.hs (P * g * P⁻¹) = S7.hs g := by
  obtain ⟨e1, -⟩ := szt_unitary hP
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv e1
  have h := S7.decA_hs_conj (K := Pᴴ) (by rw [Matrix.conjTranspose_conjTranspose]; exact e1) g
  rw [Matrix.conjTranspose_conjTranspose] at h
  rw [hinv]
  exact h

end Cayley

theorem szt_gN_eq {k r : ℕ} (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.FourierDecayAlt.B.gN g = Real.sqrt (S7.hs g) := by
  unfold Formalism.FourierDecayAlt.B.gN S7.hs
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact Complex.normSq_eq_norm_sq _

end ReciprocityTheory.ChartRestriction.DS
end
end

