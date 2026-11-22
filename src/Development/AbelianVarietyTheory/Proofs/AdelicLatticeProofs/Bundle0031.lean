import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HermitianLogTraceSqFirstVariationBound
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEnergyMin
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.EnergyMin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem energy_nonneg {H A : Matrix ι ι ℂ} (h : IsLog H A) : 0 ≤ (Matrix.trace (H * H)).re := by
  obtain ⟨U, d, -, hH, -⟩ := h
  have hh : Hᴴ = H := by
    rw [hH]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose, Matrix.mul_assoc]
    congr 3
    funext i
    simp
  have h1 := (Matrix.posSemidef_conjTranspose_mul_self H).trace_nonneg
  rw [hh] at h1
  exact (Complex.le_def.mp h1).1

omit [Fintype ι] [DecidableEq ι] in

theorem isCompact_box (C : ℝ) : IsCompact {x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C} := by
  have h : IsCompact (Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : ι => Metric.closedBall (0 : ℂ) C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have e : {x : ι → ι → ℂ | ∀ i j, ‖x i j‖ ≤ C} =
      Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : ι => Metric.closedBall (0 : ℂ) C := by
    ext x
    simp [Set.mem_pi]
  rw [← e] at h
  exact h

theorem exists_det_one (P : Matrix ι ι ℂ) (hP : IsUnit P.det) :
    ∃ Q : Matrix ι ι ℂ, Q.det = 1 ∧ ∀ x : Matrix ι ι ℂ, Q * x * Q⁻¹ = P * x * P⁻¹ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨P, Matrix.det_isEmpty, fun _ => rfl⟩
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq P.det (Fintype.card_pos (α := ι))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow Fintype.card_ne_zero] at hc
    exact hP.ne_zero hc.symm
  refine ⟨c⁻¹ • P, ?_, fun x => ?_⟩
  · rw [Matrix.det_smul, ← hc, ← mul_pow, inv_mul_cancel₀ hc0, one_pow]
  · have : (c⁻¹ • P)⁻¹ = c • P⁻¹ := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
        Matrix.mul_nonsing_inv _ hP]
    rw [this, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]

theorem inv_eq_adj {P : Matrix ι ι ℂ} (hP : P.det = 1) : P⁻¹ = P.adjugate := by
  rw [Matrix.inv_def, hP]
  simp

end GlobalTheory.ClassFin.EnergyMin

open GlobalTheory.ClassFin.EnergyMin in

theorem GlobalTheory.ClassFin.exists_energy_min : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), (∀ s, IsUnit (g s).det) → Submodule.span ℂ (Set.range g) = ⊤ → ∃ (P : Matrix ι ι ℂ) (H : σ → Matrix ι ι ℂ), IsUnit P.det ∧ (∀ s, IsLog (H s) ((P * g s * P⁻¹)ᴴ * (P * g s * P⁻¹))) ∧ ∀ (P' : Matrix ι ι ℂ) (H' : σ → Matrix ι ι ℂ), IsUnit P'.det → (∀ s, IsLog (H' s) ((P' * g s * P'⁻¹)ᴴ * (P' * g s * P'⁻¹))) → ∑ s, (Matrix.trace (H s * H s)).re ≤ ∑ s, (Matrix.trace (H' s * H' s)).re := by
  intro ι _ _ σ _ g hg hspan
  choose H₀ hH₀ using fun s => GlobalTheory.T.exists_isHermitianLogOfPosDef_gram ι (g s) (hg s)
  let En : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) → ℝ := fun p => ∑ s, (Matrix.trace (p.2 s * p.2 s)).re
  have hEn : Continuous En := by
    refine continuous_finset_sum _ fun s _ => Complex.continuous_re.comp ?_
    have h : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.2 s :=
      (continuous_apply s).comp continuous_snd
    exact (h.matrix_mul h).matrix_trace
  let E₀ : ℝ := En (1, H₀)
  let Z : Set (Matrix ι ι ℂ × (σ → Matrix ι ι ℂ)) := {p | p.1.det = 1 ∧
    (∀ s, IsLog (p.2 s) ((p.1 * g s * p.1.adjugate)ᴴ * (p.1 * g s * p.1.adjugate))) ∧ En p ≤ E₀}
  have hZc : IsClosed Z := by
    refine IsClosed.inter (isClosed_eq continuous_fst.matrix_det continuous_const)
      (IsClosed.inter ?_ (isClosed_le hEn continuous_const))
    have : IsClosed (⋂ s, {p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) |
        IsLog (p.2 s) ((p.1 * g s * p.1.adjugate)ᴴ * (p.1 * g s * p.1.adjugate))}) := by
      refine isClosed_iInter fun s => ?_
      have h : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.2 s :=
        (continuous_apply s).comp continuous_snd
      have h2 : Continuous fun p : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ) => p.1 * g s * p.1.adjugate :=
        (continuous_fst.matrix_mul continuous_const).matrix_mul continuous_fst.matrix_adjugate
      exact (GlobalTheory.T.isClosed_isHermitianLogOfPosDef ι).preimage (h.prodMk (h2.matrix_conjTranspose.matrix_mul h2))
    rw [← Set.setOf_forall] at this
    exact this
  obtain ⟨C, hC⟩ := GlobalTheory.T.matrix_entries_bounded_of_hermitian_log_trace_sq_le ι E₀
  obtain ⟨C', hC'⟩ := GlobalTheory.T.entries_bounded_of_conj_spanning_bounded' ι σ g hspan C
  have hK : IsCompact ({x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C'} ×ˢ
      (Set.pi Set.univ fun _ : σ => {x : Matrix ι ι ℂ | ∀ i j, ‖x i j‖ ≤ C})) :=
    (isCompact_box C').prod (isCompact_univ_pi fun _ => isCompact_box C)
  have hZ : IsCompact Z := by
    refine hK.of_isClosed_subset hZc ?_
    rintro ⟨P, H⟩ ⟨hd, hl, hE⟩
    have hb : ∀ s i j, ‖(P * g s * P.adjugate) i j‖ ≤ C ∧ ‖H s i j‖ ≤ C := by
      intro s
      refine hC _ _ (hl s) (le_trans ?_ hE)
      exact Finset.single_le_sum (f := fun s => (Matrix.trace (H s * H s)).re)
        (fun t _ => energy_nonneg (hl t)) (Finset.mem_univ s)
    refine ⟨hC' P hd fun s i j => ?_, fun s _ i j => (hb s i j).2⟩
    rw [inv_eq_adj hd]
    exact (hb s i j).1
  have h0 : ((1, H₀) : Matrix ι ι ℂ × (σ → Matrix ι ι ℂ)) ∈ Z := by
    refine ⟨Matrix.det_one, fun s => ?_, le_rfl⟩
    simpa using hH₀ s
  obtain ⟨⟨P, H⟩, ⟨hd, hl, hE⟩, hmin⟩ := hZ.exists_isMinOn ⟨_, h0⟩ hEn.continuousOn
  have hd' : P.det = 1 := hd
  refine ⟨P, H, by rw [hd']; exact isUnit_one, fun s => by rw [inv_eq_adj hd']; exact hl s, ?_⟩
  intro P' H' hP' hl'
  obtain ⟨Q, hQ, hQx⟩ := exists_det_one P' hP'
  change En (P, H) ≤ En (Q, H')
  by_cases hle : En (Q, H') ≤ E₀
  · refine hmin (a := (Q, H')) ⟨hQ, fun s => ?_, hle⟩
    have := hl' s
    rw [← hQx, inv_eq_adj hQ] at this
    exact this
  · exact hE.trans (not_le.mp hle).le
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsHermiteReducedLatticeBasis
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.HermiteReduction

theorem exists_lt_two_mul {S : Type} [Nonempty S] (f : S → ℝ) (c : ℝ) (hc : 0 < c) (hf : ∀ s, c ≤ f s) :
    ∃ s, ∀ t, f s < 2 * f t := by
  have hbdd : BddBelow (Set.range f) := ⟨c, by rintro _ ⟨s, rfl⟩; exact hf s⟩
  have hm : c ≤ ⨅ s, f s := le_ciInf hf
  have hlt : ⨅ s, f s < 2 * ⨅ s, f s := by linarith
  obtain ⟨s, hs⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨s, fun t => hs.trans_le (by linarith [ciInf_le hbdd t])⟩

noncomputable def gramMinor {N : ℕ} (x : Matrix (Fin N) (Fin N) ℝ) (j : Fin (N + 1)) : ℝ :=
  ((xᵀ * x).submatrix (Fin.castLE (Nat.lt_succ_iff.mp j.2)) (Fin.castLE (Nat.lt_succ_iff.mp j.2))).det

theorem prod_castLE_succ {N : ℕ} (f : Fin N → ℝ) (p q : Fin N) (hq : (q : ℕ) = p + 1) (h : (q : ℕ) ≤ N) :
    ∏ i : Fin q, f (Fin.castLE h i) = (∏ l ∈ Finset.univ.filter (· < p), f l) * f p := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq'⟩ := q
  simp only at hq h ⊢
  subst hq
  rw [Fin.prod_univ_castSucc]
  congr 1
  refine Finset.prod_bij (fun i _ => Fin.castLE h i.castSucc) ?_ ?_ ?_ ?_
  · intro i _
    simp [Fin.lt_def]
  · intro i _ j _ hij
    exact Fin.ext (by simpa using congrArg Fin.val hij)
  · intro l hl
    have hl' : (l : ℕ) < p := by simpa [Fin.lt_def] using hl
    exact ⟨⟨l, hl'⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro i _
    rfl

theorem mul_upper {N : ℕ} (n m : Matrix (Fin N) (Fin N) ℝ) (hn1 : ∀ i, n i i = 1) (hn0 : ∀ i j, j < i → n i j = 0)
    (hm1 : ∀ i, m i i = 1) (hm0 : ∀ i j, j < i → m i j = 0) :
    (∀ i, (n * m) i i = 1) ∧ ∀ i j, j < i → (n * m) i j = 0 := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hn1, hm1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hn0 i l h, zero_mul]
      · rw [hm0 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hn0 i l h, zero_mul]
    · rw [hm0 l j (lt_of_lt_of_le hij h), mul_zero]

theorem le_of_swap {N : ℕ} (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ)
    (hk : kᵀ * k = 1) (ha : ∀ i, 0 < a i) (hn1 : ∀ i, n i i = 1) (hn0 : ∀ i j, j < i → n i j = 0)
    (hν : ∀ i j, i < j → |n i j| ≤ 1 / 2) (p q : Fin N) (hq : (q : ℕ) = p + 1)
    (hlt : ∏ j, gramMinor (k * diagonal a * n) j <
      2 * ∏ j, gramMinor ((k * diagonal a * n).submatrix id (Equiv.swap p q)) j) : a p ≤ 2 * a q := by
  set g := k * diagonal a * n with hg
  have hpq : p < q := by rw [Fin.lt_def]; omega
  have hqN : (q : ℕ) ≤ N := q.2.le
  obtain ⟨h1, h2⟩ := GlobalTheory.T.gram_minor_swap_adjacent_columns N k a n g (g.submatrix id (Equiv.swap p q)) p q hk hn1 hn0 hq rfl rfl
  have hG : ∀ j : Fin (N + 1),
      gramMinor g j = ∏ i : Fin j, a (Fin.castLE (Nat.lt_succ_iff.mp j.2) i) ^ 2 :=
    fun j => GlobalTheory.T.det_leading_minor_gram_iwasawa N k a n hk hn1 hn0 j _
  let qq : Fin (N + 1) := ⟨q, Nat.lt_succ_of_le hqN⟩
  have hpos : ∀ j, 0 < gramMinor g j := fun j => by
    rw [hG]
    exact Finset.prod_pos fun i _ => pow_pos (ha _) 2
  have hrest : ∏ j ∈ Finset.univ.erase qq, gramMinor (g.submatrix id (Equiv.swap p q)) j =
      ∏ j ∈ Finset.univ.erase qq, gramMinor g j := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hne : (j : ℕ) ≠ q := fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h)
    exact h1 j (Nat.lt_succ_iff.mp j.2) hne
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ qq),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ qq), hrest] at hlt
  have hR : 0 < ∏ j ∈ Finset.univ.erase qq, gramMinor g j := Finset.prod_pos fun j _ => hpos j
  have hlt' : gramMinor g qq < 2 * gramMinor (g.submatrix id (Equiv.swap p q)) qq := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith [mul_le_mul_of_nonneg_right hc' hR.le]
  have eG : gramMinor g qq = (∏ l ∈ Finset.univ.filter (· < p), a l ^ 2) * a p ^ 2 := by
    rw [hG]
    exact prod_castLE_succ (fun i => a i ^ 2) p q hq _
  have eG' : gramMinor (g.submatrix id (Equiv.swap p q)) qq =
      (∏ l ∈ Finset.univ.filter (· < p), a l ^ 2) * (a q ^ 2 + n p q ^ 2 * a p ^ 2) := h2 hqN
  rw [eG, eG'] at hlt'
  have hP : 0 < ∏ l ∈ Finset.univ.filter (· < p), a l ^ 2 :=
    Finset.prod_pos fun l _ => pow_pos (ha l) 2
  have hn : n p q ^ 2 ≤ 1 / 4 := by
    have h3 := abs_le.mp (hν p q hpq)
    nlinarith [h3.1, h3.2]
  have key : a p ^ 2 < 2 * (a q ^ 2 + n p q ^ 2 * a p ^ 2) := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith [mul_le_mul_of_nonneg_left hc' hP.le]
  have hap := ha p
  have haq := ha q
  by_contra hc
  have hc' := not_le.mp hc
  nlinarith [mul_lt_mul'' hc' hc' (by positivity) (by positivity),
    mul_le_mul_of_nonneg_right hn (sq_nonneg (a p))]

theorem exists_reduced : ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ (γ : Matrix (Fin N) (Fin N) ℤ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), (γ.det = 1 ∨ γ.det = -1) ∧ kᵀ * k = 1 ∧ (∀ i, 0 < a i) ∧ (∀ i, n i i = 1) ∧ (∀ i j, j < i → n i j = 0) ∧ (∀ i j, i < j → |n i j| ≤ 1 / 2) ∧ (∀ p q : Fin N, (q : ℕ) = p + 1 → a p ≤ 2 * a q) ∧ g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by
  intro N g hg
  obtain ⟨c, hc, hcb⟩ := GlobalTheory.T.gram_leading_minor_lower_bound_integral N g hg
  let S := {γ : Matrix (Fin N) (Fin N) ℤ // γ.det = 1 ∨ γ.det = -1}
  have : Nonempty S := ⟨⟨1, Or.inl Matrix.det_one⟩⟩
  have hdet0 : ∀ γ : S, γ.1.det ≠ 0 := fun γ => by
    rcases γ.2 with h | h <;> rw [h] <;> norm_num
  have hbound : ∀ γ : S, c ^ (N + 1) ≤ ∏ j, gramMinor (g * γ.1.map (Int.cast : ℤ → ℝ)) j := by
    intro γ
    calc c ^ (N + 1) = ∏ _j : Fin (N + 1), c := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hc.le)
          (fun j _ => hcb γ.1 (hdet0 γ) j (Nat.lt_succ_iff.mp j.2))
  obtain ⟨γ0, hγ0⟩ := exists_lt_two_mul
    (fun γ : S => ∏ j, gramMinor (g * γ.1.map (Int.cast : ℤ → ℝ)) j) (c ^ (N + 1)) (pow_pos hc _) hbound
  have hgd : (g * γ0.1.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    rw [Matrix.det_mul]
    refine mul_ne_zero hg ?_
    rw [← Int.cast_det]
    exact_mod_cast hdet0 γ0
  obtain ⟨k, a, n, hk, ha, hn1, hn0, hgk⟩ := GlobalTheory.T.iwasawa_decomposition_real_matrix N _ hgd
  obtain ⟨ν, hν1, hν0, hνb⟩ := GlobalTheory.T.unipotent_upper_size_reduction N n hn1 hn0
  have hνR1 : ∀ i, ν.map (Int.cast : ℤ → ℝ) i i = 1 := fun i => by simp [hν1]
  have hνR0 : ∀ i j, j < i → ν.map (Int.cast : ℤ → ℝ) i j = 0 := fun i j h => by simp [hν0 i j h]
  obtain ⟨hn'1, hn'0⟩ := mul_upper n _ hn1 hn0 hνR1 hνR0
  have hνdet : ν.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j h => hν0 i j h)]
    simp [hν1]
  have hγdet : (γ0.1 * ν).det = 1 ∨ (γ0.1 * ν).det = -1 := by
    rw [Matrix.det_mul, hνdet, mul_one]
    exact γ0.2
  have hmap : (γ0.1 * ν).map (Int.cast : ℤ → ℝ) =
      γ0.1.map (Int.cast : ℤ → ℝ) * ν.map (Int.cast : ℤ → ℝ) :=
    Matrix.map_mul (f := Int.castRingHom ℝ)
  have heq : g * (γ0.1 * ν).map (Int.cast : ℤ → ℝ) =
      k * diagonal a * (n * ν.map (Int.cast : ℤ → ℝ)) := by
    rw [hmap, ← Matrix.mul_assoc, hgk, Matrix.mul_assoc (k * diagonal a)]
  have hΦ : ∏ j, gramMinor (k * diagonal a * (n * ν.map (Int.cast : ℤ → ℝ))) j =
      ∏ j, gramMinor (g * γ0.1.map (Int.cast : ℤ → ℝ)) j := by
    rw [hgk]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold gramMinor
    rw [GlobalTheory.T.det_leading_minor_gram_iwasawa N k a _ hk hn'1 hn'0 j _, GlobalTheory.T.det_leading_minor_gram_iwasawa N k a n hk hn1 hn0 j _]
  refine ⟨γ0.1 * ν, k, a, n * ν.map (Int.cast : ℤ → ℝ), hγdet, hk, ha, hn'1, hn'0, hνb,
    fun p q hq => ?_, heq⟩
  have hpq : p ≠ q := fun h => by rw [h] at hq; omega
  let γ' : S := ⟨(γ0.1 * ν).submatrix id (Equiv.swap p q), by
    rw [Matrix.det_permute', Equiv.Perm.sign_swap hpq]
    rcases hγdet with h | h <;> simp [h]⟩
  have hsw : g * γ'.1.map (Int.cast : ℤ → ℝ) =
      (k * diagonal a * (n * ν.map (Int.cast : ℤ → ℝ))).submatrix id (Equiv.swap p q) := by
    rw [← heq]
    ext i j
    rfl
  refine le_of_swap k a _ hk ha hn'1 hn'0 hνb p q hq ?_
  rw [hΦ, ← hsw]
  exact hγ0 γ'

end GlobalTheory.ClassFin.HermiteReduction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInfiniteAdeleTensorEquivMixedSpaceStatement
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_infiniteAdele_tensor_equiv_mixedSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E); ∃ θ : InfiniteAdeleRing F ⊗[F] E ≃+* mixedSpace E, (∀ x : E, θ (1 ⊗ₜ[F] x) = mixedEmbedding E x) ∧ Continuous θ.symm ∧ ∀ u : (mixedSpace E)ˣ, (∀ w, ((u : mixedSpace E).2 w).im = 0) → ∃ a : (InfiniteAdeleRing F)ˣ, θ ((a : InfiniteAdeleRing F) ⊗ₜ[F] 1) = u := by
  first | exact @GlobalTheory.InfAdeleMixed.exists_equiv_mixedSpace | exact GlobalTheory.InfAdeleMixed.exists_equiv_mixedSpace | (intros; apply GlobalTheory.InfAdeleMixed.exists_equiv_mixedSpace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormaliseMeanSquareOfCocompactStatement
section
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalise_meanSquare_of_cocompact' : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x : G, ∃ g ∈ Γ, g + x ∈ K) → ∀ f : G → ℂ, Continuous f → f ≠ 0 → (∀ g ∈ Γ, ∀ w, ‖f (g + w)‖ = ‖f w‖) → (∃ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1) ∧ ∃ c : ℂ, ∀ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∫ w in 𝓕, ‖c * f w‖ ^ 2 ∂μ = 1 := by
  first | exact @GlobalTheory.exists_normalise_meanSquare_of_cocompact | exact GlobalTheory.exists_normalise_meanSquare_of_cocompact | (intros; apply GlobalTheory.exists_normalise_meanSquare_of_cocompact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsQuasiReflectionProdMulVecEqStatement
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quasiReflection_prod_mulVec_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ x z : Fin n → E, hermE c G x x ≠ 0 → hermE c G z z = hermE c G x x → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1 ∧ p.1 ∈ Submodule.span E {x, z}) ∧ (l.map fun p => refl c G p.1 p.2).prod *ᵥ z = x := by
  first | exact @GlobalTheory.UnRep.exists_refl_prod_mulVec_eq | exact GlobalTheory.UnRep.exists_refl_prod_mulVec_eq | (intros; apply GlobalTheory.UnRep.exists_refl_prod_mulVec_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatOfForallComplexRingEquivFixedStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rat_of_forall_complex_ringEquiv_fixed : ∀ z : ℂ, (∀ σ : ℂ ≃+* ℂ, σ z = z) → ∃ q : ℚ, z = q := by
  first | exact @GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed | exact GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed | (intros; apply GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTwoPlacesOverOfIsSquareLocalStatement
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_two_places_over_of_isSquare_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ v : HeightOneSpectrum (𝓞 F), IsSquare (algebraMap F (v.adicCompletion F) δ) → ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 F) = v ∧ w'.under (𝓞 F) = v := by
  first | exact @GlobalTheory.QNorm.two_places_of_isSquare | exact GlobalTheory.QNorm.two_places_of_isSquare | (intros; apply GlobalTheory.QNorm.two_places_of_isSquare <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinrankSUnitsNumberFieldAddOneStatement
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_sUnitsNumberField_add_one : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), Module.finrank ℤ (Additive (sUnits F S)) + 1 = S.card + Fintype.card (InfinitePlace F) := by
  first | exact @GlobalTheory.QNorm.sUnits_rank | exact GlobalTheory.QNorm.sUnits_rank | (intros; apply GlobalTheory.QNorm.sUnits_rank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HermitianLogTraceSqFirstVariationBoundStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_log_trace_sq_first_variation_bound : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H A : Matrix ι ι ℂ), IsLog H A → ∃ C δ : ℝ, 0 < δ ∧ ∀ Y H' : Matrix ι ι ℂ, (∀ i j, ‖Y i j‖ ≤ δ) → IsLog H' (A + Y) → (Matrix.trace (H' * H')).re ≤ (Matrix.trace (H * H)).re + 2 * (Matrix.trace (H * A⁻¹ * Y)).re + C * ∑ i, ∑ j, ‖Y i j‖ ^ 2 := by
  first | exact @GlobalTheory.ClassFin.LogSqVar.first_variation | exact GlobalTheory.ClassFin.LogSqVar.first_variation | (intros; apply GlobalTheory.ClassFin.LogSqVar.first_variation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90BaseChangeStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert90_baseChange' : ∀ (F E K : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] (τ : E ≃ₐ[F] E) (m : ℕ), orderOf τ = m → ∀ x : K ⊗[F] E, ∏ i ∈ Finset.range m, (Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E))^[i] x = 1 → ∃ z : (K ⊗[F] E)ˣ, x * Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E) z = z := by
  first | exact @GlobalTheory.CNorm.hilbert90_baseChange | exact GlobalTheory.CNorm.hilbert90_baseChange | (intros; apply GlobalTheory.CNorm.hilbert90_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdeleCongruenceUnitCriterion
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors Topology

namespace GlobalTheory.IdeleCharLevel

variable (K : Type) [Field K] [NumberField K]

theorem exists_level (U : Set (FiniteAdeleRing (𝓞 K) K)) (hU : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K)) :
    ∃ M : ℕ, M ≠ 0 ∧ ∀ a : FiniteAdeleRing (𝓞 K) K,
      (∀ P : HeightOneSpectrum (𝓞 K), Valued.v (a P) ≤ P.intValuation (M : 𝓞 K)) → a ∈ U := by
  obtain ⟨M, hM, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele K U hU
  refine ⟨M, hM.ne', fun a ha => ?_⟩
  have hM0 : (M : K) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hM1 : (M : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have := h (algebraMap K (FiniteAdeleRing (𝓞 K) K) (M : K)⁻¹ * a) fun P => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) (M : K)⁻¹) P * a P) ≤ 1
    rw [map_mul, FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
      ← map_natCast (algebraMap (𝓞 K) K), HeightOneSpectrum.valuation_of_algebraMap]
    have h0 : P.intValuation (M : 𝓞 K) ≠ 0 := P.intValuation_ne_zero _ hM1
    rw [inv_mul_le_iff₀ (zero_lt_iff.mpr h0), mul_one]
    exact ha P
  rwa [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap K (FiniteAdeleRing (𝓞 K) K)) M,
    ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul] at this

end GlobalTheory.IdeleCharLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexFormulaNormsInvolution
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem two_mul_index_sqs_mul_relIndex_norm_involution :
    ∀ (A : Type) [CommGroup A] (σ : A →* A) (ε : A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → ε ≠ 1 → ε ^ 2 = 1 → σ ε = ε → (∀ a : A, a ^ 2 = 1 → a = 1 ∨ a = ε) → 2 * (sqs (⊤ : Subgroup A)).index * (MonoidHom.id A * σ).range.relIndex (σ.eqLocus (MonoidHom.id A)) = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) ^ 2 := by
  intro A _ σ ε h1 h2 h3 h4 h5 h6
  have hn := GlobalTheory.T.relIndex_norm_mul_relIndex_sqs_ker' A σ h1 h2
  have hs := GlobalTheory.T.two_mul_index_sqs_eq_relIndex_fixed_mul_relIndex_ker A σ ε h1 h2 h3 h4 h5 h6
  rw [hs, sq, mul_assoc, mul_comm ((sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker), hn]

end GlobalTheory.QNorm
end

