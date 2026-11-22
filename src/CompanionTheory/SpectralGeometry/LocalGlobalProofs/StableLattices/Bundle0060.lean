import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0059
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.Fub2
import Formalism.RealPlaceAnalysis.Bundle0004
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0225
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0437

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EigenvalueGapExists
section
open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo

namespace GlobalTheory.CompanionTheory.UGeoGap

theorem exists_gap_of_mem_Icc_top :
    ∀ (n : ℕ) (l : Fin n → ℝ) (L : ℝ), 0 < L → (∀ i, 0 ≤ l i ∧ l i ≤ L) → (∃ i, l i = L) →
      ∃ r : ℕ, r < n ∧ ∀ i, l i < r * (L / (n + 1)) ∨ (r + 1) * (L / (n + 1)) ≤ l i := by
  intro n l L hL _ hex
  obtain ⟨i₀, hi₀⟩ := hex
  by_contra hcon
  push Not at hcon
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hδpos : 0 < L / (n + 1) := div_pos hL hn
  choose f hf using fun r : Fin n => hcon r r.2
  have hinj : Function.Injective f := by
    intro r s hrs
    have h1 := hf r
    have h2 := hf s
    rw [hrs] at h1
    have a1 : ((r : ℕ) : ℝ) < (s : ℕ) + 1 :=
      lt_of_mul_lt_mul_right (lt_of_le_of_lt h1.1 h2.2) hδpos.le
    have a2 : ((s : ℕ) : ℝ) < (r : ℕ) + 1 :=
      lt_of_mul_lt_mul_right (lt_of_le_of_lt h2.1 h1.2) hδpos.le
    have b1 : (r : ℕ) < (s : ℕ) + 1 := by exact_mod_cast a1
    have b2 : (s : ℕ) < (r : ℕ) + 1 := by exact_mod_cast a2
    exact Fin.ext (by omega)
  obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.mp hinj) i₀
  have h1 := (hf r).2
  rw [hr, hi₀] at h1
  have hr1 : ((r : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast r.2
  have h2 : (((r : ℕ) : ℝ) + 1) * (L / (n + 1)) ≤ n * (L / (n + 1)) :=
    mul_le_mul_of_nonneg_right hr1 hδpos.le
  have h3 : (n : ℝ) * (L / (n + 1)) < (n + 1) * (L / (n + 1)) :=
    mul_lt_mul_of_pos_right (by linarith) hδpos
  have h4 : ((n : ℝ) + 1) * (L / (n + 1)) = L := by
    field_simp
  linarith

end GlobalTheory.CompanionTheory.UGeoGap
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsGradedMatrixEigenBound
section
open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo

noncomputable section

namespace GlobalTheory.CompanionTheory.UGeo.SpecGrad

variable {n : ℕ}

theorem aeval_intertwine {R : Type*} [Ring R] [Algebra ℝ R] {X A B : R} (h : X * A = B * X)
    (p : Polynomial ℝ) : X * Polynomial.aeval A p = Polynomial.aeval B p * X := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, mul_add, add_mul, hp, hq]
  | monomial k a =>
    have hk : X * A ^ k = B ^ k * X := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, h, ← mul_assoc, ← pow_succ]
    simp only [Polynomial.aeval_monomial]
    rw [← mul_assoc, ← Algebra.commutes, mul_assoc, hk, mul_assoc]

def cj (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  U * diagonal (fun i => (d i : ℂ)) * Uᴴ

variable {U : Matrix (Fin n) (Fin n) ℂ}

theorem cj_mul (h1 : Uᴴ * U = 1) (d e : Fin n → ℝ) : cj U d * cj U e = cj U (fun i => d i * e i) := by
  have hd : diagonal (fun i => (d i : ℂ)) * diagonal (fun i => (e i : ℂ))
      = diagonal (fun i => ((d i * e i : ℝ) : ℂ)) := by
    rw [diagonal_mul_diagonal]; simp
  simp only [cj]
  calc _ = U * diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) * diagonal (fun i => (e i : ℂ)) * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.mul_one, Matrix.mul_assoc U, hd]

theorem cj_conj (d : Fin n → ℝ) : (cj U d)ᴴ = cj U d := by
  have h : (diagonal fun i => (d i : ℂ))ᴴ = diagonal fun i => (d i : ℂ) := by
    rw [diagonal_conjTranspose]; congr 1; funext i; simp
  rw [cj, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, h, Matrix.mul_assoc]

theorem cj_one (h2 : U * Uᴴ = 1) : cj U (fun _ => 1) = 1 := by
  simp [cj, h2]

theorem cj_add (d e : Fin n → ℝ) : cj U (fun i => d i + e i) = cj U d + cj U e := by
  rw [cj, cj, cj, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
  congr 3; funext i; push_cast; rfl

theorem cj_smul (c : ℝ) (d : Fin n → ℝ) : cj U (fun i => c * d i) = (c : ℂ) • cj U d := by
  have h : (diagonal fun i => ((c * d i : ℝ) : ℂ)) = (c : ℂ) • diagonal fun i => (d i : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [diagonal_apply_ne _ hij]
  rw [cj, cj, h, Matrix.mul_smul, Matrix.smul_mul]

theorem cj_neg (d : Fin n → ℝ) : cj U (fun i => - d i) = - cj U d := by
  have := cj_smul (U := U) (-1) d
  simpa using this

theorem algebraMap_eq (a : ℝ) : algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) a = (a : ℂ) • 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.algebraMap_matrix_apply]
  · simp [Matrix.algebraMap_matrix_apply, hij]

theorem cj_aeval (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1) (d : Fin n → ℝ) (p : Polynomial ℝ) :
    Polynomial.aeval (cj U d) p = cj U (fun i => p.eval (d i)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq, cj_add]
  | monomial k a =>
    have hk : cj U d ^ k = cj U (fun i => d i ^ k) := by
      induction k with
      | zero => simp only [pow_zero]; exact (cj_one h2).symm
      | succ k ih => rw [pow_succ, ih, cj_mul h1]; simp only [pow_succ]
    rw [Polynomial.aeval_monomial, hk, algebraMap_eq, smul_mul_assoc, one_mul, ← cj_smul]
    simp only [Polynomial.eval_monomial]

theorem cj_eq_zero (h1 : Uᴴ * U = 1) {d : Fin n → ℝ} (h : cj U d = 0) (i : Fin n) : d i = 0 := by
  have e : diagonal (fun i => (d i : ℂ)) = Uᴴ * cj U d * U := by
    simp only [cj]
    calc _ = (Uᴴ * U) * diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) := by rw [h1]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h] at e
  have := congrFun (congrFun e i) i
  simpa using this

theorem nsq_eq_dot (v : Fin n → ℂ) : ((nsq v : ℝ) : ℂ) = star v ⬝ᵥ v := by
  simp only [nsq, dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast; rfl

theorem nsq_eq_of_gram {M N : Matrix (Fin n) (Fin n) ℂ} (h : Mᴴ * M = Nᴴ * N) (y : Fin n → ℂ) :
    nsq (M *ᵥ y) = nsq (N *ᵥ y) := by
  have key : ∀ M : Matrix (Fin n) (Fin n) ℂ, ((nsq (M *ᵥ y) : ℝ) : ℂ) = star y ⬝ᵥ ((Mᴴ * M) *ᵥ y) := by
    intro M
    rw [nsq_eq_dot, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
  exact Complex.ofReal_injective (by rw [key, key, h])

theorem nsq_cj (h1 : Uᴴ * U = 1) (d : Fin n → ℝ) (y : Fin n → ℂ) :
    nsq (cj U d *ᵥ y) = ∑ i, d i ^ 2 * ‖(Uᴴ *ᵥ y) i‖ ^ 2 := by
  have hU : ∀ w : Fin n → ℂ, nsq (U *ᵥ w) = nsq w := fun w => by
    have := nsq_eq_of_gram (M := U) (N := 1) (by simp [h1]) w
    simpa using this
  have e : cj U d *ᵥ y = U *ᵥ (diagonal (fun i => (d i : ℂ)) *ᵥ (Uᴴ *ᵥ y)) := by
    simp only [cj, mulVec_mulVec, Matrix.mul_assoc]
  rw [e, hU]
  simp only [nsq, mulVec_diagonal, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem core {J G H : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (hHG : H * G = 1) (hGH : G * H = 1)
    (hJc : Jᴴ = J) (hHJ : H = J * Gᴴ * J) (hT : (Hᴴ * H).IsHermitian) (f : ℝ → ℝ) (α β : ℝ)
    (hf : ∀ l : ℝ, 0 < l → (f l = -1 ∨ f l = 0 ∨ f l = 1) ∧ f l⁻¹ = - f l)
    (hα : ∀ i, f (hT.eigenvalues i) = -1 → α ≤ hT.eigenvalues i)
    (hβ : ∀ i, f (hT.eigenvalues i) = 0 → β⁻¹ ≤ hT.eigenvalues i)
    (hne : ∃ i, f (hT.eigenvalues i) ≠ 0) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, Aᴴ = A ∧ A * A * A = A ∧ A ≠ 0 ∧ J * A = -A * J ∧
      ∀ y : Fin n → ℂ, α * nsq (Pm A *ᵥ y) + β⁻¹ * nsq (Pz A *ᵥ y) ≤ nsq (H *ᵥ y) := by
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix (Fin n) (Fin n) ℂ, U = (hT.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) :=
    ⟨_, rfl⟩
  have h1 : Uᴴ * U = 1 := by
    rw [hUdef]; exact Matrix.mem_unitaryGroup_iff'.1 hT.eigenvectorUnitary.2
  have h2 : U * Uᴴ = 1 := by
    rw [hUdef]; exact Matrix.mem_unitaryGroup_iff.1 hT.eigenvectorUnitary.2
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin n → ℝ, lam = hT.eigenvalues := ⟨_, rfl⟩
  rw [← hlam] at hα hβ hne
  have hTc : Hᴴ * H = cj U lam := by
    have := hT.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, ← hUdef, ← hlam, Matrix.star_eq_conjTranspose] at this
    exact this
  have hTG : (Hᴴ * H) * (G * Gᴴ) = 1 := by
    calc _ = Hᴴ * (H * G) * Gᴴ := by simp only [Matrix.mul_assoc]
      _ = (G * H)ᴴ := by rw [hHG, Matrix.mul_one, conjTranspose_mul]
      _ = 1 := by rw [hGH, conjTranspose_one]
  have hnn : ∀ i, 0 ≤ lam i := fun i => by
    rw [hlam]
    open scoped ComplexOrder in
    exact (Matrix.posSemidef_conjTranspose_mul_self H).eigenvalues_nonneg i
  have hn0 : ∀ i, lam i ≠ 0 := fun i h0 => by
    have hd := congrArg Matrix.det hTG
    rw [Matrix.det_mul, hT.det_eq_prod_eigenvalues, ← hlam, Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])] at hd
    simp at hd
  have hpos : ∀ i, 0 < lam i := fun i => lt_of_le_of_ne (hnn i) (hn0 i).symm
  have hinv : cj U (fun i => (lam i)⁻¹) = G * Gᴴ := by
    have e : cj U (fun i => (lam i)⁻¹) * (Hᴴ * H) = 1 := by
      rw [hTc, cj_mul h1, ← cj_one (U := U) h2]
      congr 1; funext i; exact inv_mul_cancel₀ (hn0 i)
    calc _ = cj U (fun i => (lam i)⁻¹) * ((Hᴴ * H) * (G * Gᴴ)) := by rw [hTG, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]
  have hHc : Hᴴ = J * G * J := by
    rw [hHJ]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hJc, Matrix.mul_assoc]
  have hJT : J * (Hᴴ * H) = (G * Gᴴ) * J := by
    rw [hHc, hHJ]
    calc _ = (J * J) * G * (J * J) * Gᴴ * J := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hJ, Matrix.one_mul, Matrix.mul_one]

  let S : Finset ℝ := Finset.univ.image lam ∪ Finset.univ.image (fun i => (lam i)⁻¹)
  let p : Polynomial ℝ := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Function.injective_id.injOn) hx
  have hp1 : ∀ i, p.eval (lam i) = f (lam i) := fun i =>
    hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hp2 : ∀ i, p.eval (lam i)⁻¹ = - f (lam i) := fun i => by
    rw [hp _ (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun i => (lam i)⁻¹) (Finset.mem_univ i)))]
    exact (hf _ (hpos i)).2
  obtain ⟨a, ha⟩ : ∃ a : Fin n → ℝ, a = fun i => f (lam i) := ⟨_, rfl⟩
  have ha3 : ∀ i, a i = -1 ∨ a i = 0 ∨ a i = 1 := fun i => by
    rw [ha]; exact (hf _ (hpos i)).1
  have hA : Polynomial.aeval (Hᴴ * H) p = cj U a := by
    rw [hTc, cj_aeval h1 h2, ha]; congr 1; funext i; exact hp1 i
  have hAi : Polynomial.aeval (G * Gᴴ) p = - cj U a := by
    rw [← hinv, cj_aeval h1 h2, ← cj_neg, ha]; congr 1; funext i; exact hp2 i
  have hPm : Pm (cj U a) = cj U (fun i => (1 / 2 : ℝ) * (a i * a i + - a i)) := by
    rw [cj_smul, cj_add, cj_neg, ← cj_mul h1, ← sub_eq_add_neg]
    simp only [Pm]
    congr 1
    push_cast; rfl
  have hPz : Pz (cj U a) = cj U (fun i => 1 + - (a i * a i)) := by
    rw [cj_add, cj_neg, ← cj_mul h1, cj_one h2, ← sub_eq_add_neg]
    rfl
  refine ⟨cj U a, cj_conj a, ?_, ?_, ?_, ?_⟩
  · rw [cj_mul h1, cj_mul h1]
    congr 1; funext i
    rcases ha3 i with h | h | h <;> rw [h] <;> norm_num
  · intro h0
    obtain ⟨i, hi⟩ := hne
    exact hi (by have := cj_eq_zero h1 h0 i; rwa [ha] at this)
  · have := aeval_intertwine hJT p
    rwa [hA, hAi] at this
  · intro y
    have hH : nsq (H *ᵥ y) = nsq (cj U (fun i => Real.sqrt (lam i)) *ᵥ y) := by
      refine nsq_eq_of_gram ?_ y
      rw [cj_conj, cj_mul h1, hTc]
      congr 1; funext i; exact (Real.mul_self_sqrt (hnn i)).symm
    rw [hPm, hPz, hH, nsq_cj h1, nsq_cj h1, nsq_cj h1, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hc : 0 ≤ ‖(Uᴴ *ᵥ y) i‖ ^ 2 := by positivity
    rw [Real.sq_sqrt (hnn i)]
    have hfa : a i = f (lam i) := by rw [ha]
    rcases ha3 i with h | h | h
    · have h' := hα i (by rw [← hfa, h])
      rw [h]
      nlinarith
    · have h' := hβ i (by rw [← hfa, h])
      rw [h]
      nlinarith
    · rw [h]
      have := hpos i
      have h3 : 0 ≤ lam i * ‖(Uᴴ *ᵥ y) i‖ ^ 2 := by positivity
      nlinarith

end GlobalTheory.CompanionTheory.UGeo.SpecGrad

open GlobalTheory.CompanionTheory.UGeo.SpecGrad in

theorem GlobalTheory.CompanionTheory.UGeo.SpecGrad.grading_of_spectral :
    ∀ (n : ℕ) (ε : Fin n → Bool) (g : S7.UJ ε) (hT : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).IsHermitian) (f : ℝ → ℝ) (α β : ℝ), (∀ l : ℝ, 0 < l → (f l = -1 ∨ f l = 0 ∨ f l = 1) ∧ f l⁻¹ = - f l) → (∀ i, f (hT.eigenvalues i) = -1 → α ≤ hT.eigenvalues i) → (∀ i, f (hT.eigenvalues i) = 0 → β⁻¹ ≤ hT.eigenvalues i) → (∃ i, f (hT.eigenvalues i) ≠ 0) → ∃ A' : Matrix (Fin n) (Fin n) ℂ, IsGrad ε A' ∧ ∀ y : Fin n → ℂ, α * nsq (Pm A' *ᵥ y) + β⁻¹ * nsq (Pz A' *ᵥ y) ≤ nsq (S7.toM g⁻¹ *ᵥ y) := by
  intro n ε g hT f α β hf hα hβ hne
  have hHG : S7.toM g⁻¹ * S7.toM g = 1 := by
    show ((g⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val * ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)).val = 1
    simp
  have hGH : S7.toM g * S7.toM g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)).val * ((g⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val = 1
    simp
  obtain ⟨A, hc, h3, h0, hJ, hy⟩ := core (J := Formalism.REAL.Jm ε) (Formalism.REAL.Jm_mul_self ε) hHG hGH
    (Formalism.REAL.Jm_conjTranspose ε) (S7.toM_inv ε g) hT f α β hf hα hβ hne
  refine ⟨A, ⟨?_, hc, h3, h0⟩, hy⟩
  show Aᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * A = 0
  rw [hc, hJ, Matrix.neg_mul, add_neg_cancel]
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteNetOfGradedProjections
section
open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo

namespace GlobalTheory.CompanionTheory.UGeo.GradNet

variable {n : ℕ}

theorem norm_entry_sq_le_hs (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖M i j‖ ^ 2 ≤ Formalism.REAL.hs M := by
  unfold Formalism.REAL.hs
  calc ‖M i j‖ ^ 2 ≤ ∑ b, ‖M i b‖ ^ 2 :=
        Finset.single_le_sum (f := fun b => ‖M i b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ a, ∑ b, ‖M a b‖ ^ 2 :=
        Finset.single_le_sum (f := fun a => ∑ b, ‖M a b‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem norm_entry_le {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.hs M ≤ n) (i j : Fin n) :
    ‖M i j‖ ≤ (n : ℝ) + 1 := by
  have h1 := (norm_entry_sq_le_hs M i j).trans h
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_contra hc
  push_neg at hc
  nlinarith

theorem hs_le_quarter {M : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i j, ‖M i j‖ < 1 / (2 * ((n : ℝ) + 1))) : Formalism.REAL.hs M ≤ 1 / 4 := by
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : Formalism.REAL.hs M ≤ ∑ _a : Fin n, ∑ _b : Fin n, (1 / (2 * ((n : ℝ) + 1))) ^ 2 := by
    unfold Formalism.REAL.hs
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      pow_le_pow_left₀ (norm_nonneg _) (h a b).le 2
  have e : ∑ _a : Fin n, ∑ _b : Fin n, (1 / (2 * ((n : ℝ) + 1))) ^ 2
      = ((n : ℝ) * (1 / (2 * ((n : ℝ) + 1)))) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have h2 : (n : ℝ) * (1 / (2 * ((n : ℝ) + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have h3 : 0 ≤ (n : ℝ) * (1 / (2 * ((n : ℝ) + 1))) := by positivity
  rw [e] at h1
  nlinarith

theorem exists_net (n : ℕ) (ε : Fin n → Bool) :
    ∃ (m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ), (∀ j, IsGrad ε (A j)) ∧
      ∀ A' : Matrix (Fin n) (Fin n) ℂ, IsGrad ε A' →
        ∃ j, Formalism.REAL.hs (Pm (A j) - Pm A') ≤ 1 / 4 ∧ Formalism.REAL.hs (Pp (A j) - Pp A') ≤ 1 / 4 := by
  classical
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  let f : Matrix (Fin n) (Fin n) ℂ → (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) :=
    fun A => (fun i j => Pm A i j, fun i j => Pp A i j)
  have hb : Bornology.IsBounded (f '' {A | IsGrad ε A}) := by
    refine (Metric.isBounded_closedBall
      (x := (0 : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ))) (r := (n : ℝ) + 1)).subset ?_
    rintro _ ⟨A, hA, rfl⟩
    have hA' : IsGrad ε A := hA
    have hm := hs_proj_le (Pm_conj hA') (Pm_idem hA')
    have hp := hs_proj_le (Pp_conj hA') (Pp_idem hA')
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    refine max_le ?_ ?_
    · exact (pi_norm_le_iff_of_nonneg hn).2 fun i =>
        (pi_norm_le_iff_of_nonneg hn).2 fun j => norm_entry_le hm i j
    · exact (pi_norm_le_iff_of_nonneg hn).2 fun i =>
        (pi_norm_le_iff_of_nonneg hn).2 fun j => norm_entry_le hp i j
  have hr : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  obtain ⟨t, hts, htf, hcov⟩ := Metric.finite_approx_of_totallyBounded
    ((Bornology.IsBounded.isCompact_closure hb).totallyBounded.subset subset_closure) _ hr
  have hch : ∀ y : t, ∃ A, IsGrad ε A ∧ f A = y := fun y => by
    obtain ⟨A, hA, e⟩ := hts y.2
    exact ⟨A, hA, e⟩
  choose a ha hfa using hch
  haveI : Fintype t := htf.fintype
  let e := Fintype.equivFin t
  refine ⟨Fintype.card t, fun j => a (e.symm j), fun j => ha _, fun A' hA' => ?_⟩
  have hmem : f A' ∈ ⋃ y ∈ t, Metric.ball y (1 / (2 * ((n : ℝ) + 1))) := hcov ⟨A', hA', rfl⟩
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hmem
  obtain ⟨y, hy, hd⟩ := hmem
  have hd' : dist (f (a (e.symm (e ⟨y, hy⟩)))) (f A') < 1 / (2 * ((n : ℝ) + 1)) := by
    rw [Equiv.symm_apply_apply, hfa, dist_comm]
    exact hd
  rw [Prod.dist_eq, max_lt_iff] at hd'
  refine ⟨e ⟨y, hy⟩, hs_le_quarter fun i j => ?_, hs_le_quarter fun i j => ?_⟩
  · have h1 := (dist_le_pi_dist (f (a (e.symm (e ⟨y, hy⟩)))).1 (f A').1 i).trans_lt hd'.1
    have h2 := (dist_le_pi_dist _ _ j).trans_lt h1
    simpa [f, dist_eq_norm] using h2
  · have h1 := (dist_le_pi_dist (f (a (e.symm (e ⟨y, hy⟩)))).2 (f A').2 i).trans_lt hd'.2
    have h2 := (dist_le_pi_dist _ _ j).trans_lt h1
    simpa [f, dist_eq_norm] using h2

end GlobalTheory.CompanionTheory.UGeo.GradNet
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FubiniParabolicMultipleStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FubiniParabolicMultiple : CompanionTheory.RgExh.Dec.N.S.Fub2 := by
  first | exact @GlobalTheory.CompanionTheory.FubNM.fub2 | exact GlobalTheory.CompanionTheory.FubNM.fub2 | (intros; apply GlobalTheory.CompanionTheory.FubNM.fub2 <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ImportsExtraExtra
section

end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InverseGramEigenvaluesSumHs
section
open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo

namespace GlobalTheory.CompanionTheory.UGeo

open scoped ComplexOrder in

theorem specpos_inv_eigenvalues (n : ℕ) (ε : Fin n → Bool) (g : S7.UJ ε)
    (hT : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).IsHermitian) :
    (∀ i, 0 < hT.eigenvalues i) ∧ ∑ i, hT.eigenvalues i = Formalism.REAL.hs (S7.toM g) := by
  have hmul : S7.toM g * S7.toM g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      ((g⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = 1
    simp
  have hinj : Function.Injective (S7.toM g⁻¹).mulVec := by
    intro x y hxy
    have h := congrArg (S7.toM g).mulVec hxy
    simpa [Matrix.mulVec_mulVec, hmul] using h
  have hpd : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self _ hinj
  refine ⟨fun i => hpd.eigenvalues_pos i, ?_⟩
  have htr := hT.trace_eq_sum_eigenvalues
  have hre : ∑ i, hT.eigenvalues i = (Matrix.trace ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹)).re := by
    rw [htr]
    simp
  have hhs : Formalism.REAL.hs (S7.toM g⁻¹) = Formalism.REAL.hs (S7.toM g) := by
    rw [S7.toM_inv]
    show Formalism.REAL.hs (Formalism.REAL.Jm ε * (S7.toM g)ᴴ * Formalism.REAL.Jm ε) = _
    rw [hs_mul_J, hs_J_mul, hs_conjTranspose]
  rw [hre, ← hhs, ← hs_conjTranspose, hs_eq_trace, conjTranspose_conjTranspose]

end GlobalTheory.CompanionTheory.UGeo
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwasawaParabolicCompactFactorization
section
noncomputable section

open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo

namespace GlobalTheory.CompanionTheory.UGeo

theorem mem_KG_of_mem_maxK {n : ℕ} {ε : Fin n → Bool} {k : S7.UJ ε} (hk : k ∈ GlobalTheory.FlagMeas.maxK ε) :
    k ∈ S7.KG ε := by
  have h1 : (Formalism.MainNotions.S.uMat k)ᴴ * Formalism.MainNotions.S.uMat k = 1 := hk
  have h2 : Formalism.MainNotions.S.uMat k * (Formalism.MainNotions.S.uMat k)ᴴ = 1 := mul_eq_one_comm.1 h1
  have h3 : (Formalism.MainNotions.S.uMat k)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k = Formalism.REAL.Jm ε :=
    GlobalTheory.RealIwasawa.uMat_form k
  have h4 : Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k = Formalism.MainNotions.S.uMat k * Formalism.REAL.Jm ε := by
    calc Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k
        = (Formalism.MainNotions.S.uMat k * (Formalism.MainNotions.S.uMat k)ᴴ) * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k := by
          rw [h2, Matrix.one_mul]
      _ = Formalism.MainNotions.S.uMat k * ((Formalism.MainNotions.S.uMat k)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.MainNotions.S.uMat k * Formalism.REAL.Jm ε := by rw [h3]
  refine ⟨Unitary.mem_iff.2 ⟨h1, h2⟩, ?_⟩
  exact h4.symm

theorem exists_psub_mul_maxK {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsGrad ε A)
    (g : Formalism.REAL.UJ ε) : ∃ p : Formalism.REAL.UJ ε, p ∈ PSub ε A ∧ ∃ k ∈ GlobalTheory.FlagMeas.maxK ε, g = p * k := by
  obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact (isoFlag hA) g
  obtain ⟨m, hm, hu⟩ := GlobalTheory.RealIwasawa.exists_unip_mul_levi (isoFlag hA) _ hp
  exact ⟨g * k⁻¹, (psubEq n ε A hA _).2 ⟨_, hu, m, hm, by group⟩, k, hk, by group⟩

theorem iwasawa_psub : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A →
    ∀ g : S7.UJ ε, ∃ (x : PSub ε A) (k : S7.KG ε), g = (x : S7.UJ ε) * (k : S7.UJ ε) := by
  intro n ε A hA g
  obtain ⟨p, hp, k, hk, e⟩ := exists_psub_mul_maxK (A := A) hA g
  exact ⟨⟨p, hp⟩, ⟨k, mem_KG_of_mem_maxK hk⟩, e⟩

end GlobalTheory.CompanionTheory.UGeo
end
end

