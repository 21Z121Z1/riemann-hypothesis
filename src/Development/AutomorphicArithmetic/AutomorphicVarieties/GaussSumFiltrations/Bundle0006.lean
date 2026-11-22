import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsRatDetPos

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.NormSumFreeOrbitsLeInvPrime
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem freeOrbit_prime_dvd_card {p : ℕ} [Fact p.Prime] {α : Type} (σ : α → α) (F : Finset α)
    (hF : ∀ x ∈ F, σ x ∈ F) (hp : ∀ x ∈ F, σ^[p] x = x) (hfree : ∀ x ∈ F, σ x ≠ x) :
    p ∣ F.card := by
  classical
  let f : Function.End F := fun y => ⟨σ y, hF y y.2⟩
  have hf : ∀ (n : ℕ) (y : F), (((f ^ n) y : F) : α) = σ^[n] y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', Function.iterate_succ_apply', ← ih y]
      rfl
  have h1 : f ^ p ^ 1 = 1 := by
    funext y
    apply Subtype.ext
    rw [pow_one, hf]
    exact hp y y.2
  have h2 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := 1) h1
  have h3 : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨y, hy⟩
    exact hfree y y.2 (congrArg Subtype.val hy)
  rw [h3, Fintype.card_coe] at h2
  exact Nat.modEq_zero_iff_dvd.mp h2

theorem norm_prime_Qbar_eq (p : ℕ) [Fact p.Prime] : ‖(p : Qbar p)‖ = (p : ℝ)⁻¹ := by
  have h := PadicAlgCl.valuation_p p
  rw [← PadicAlgCl.valuation_coe, h]
  simp

theorem norm_sum_free_orbits_le : ∀ (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (α : Type) (σ : α → α) (s : Finset α) (Φ : α → ℂ), (∀ x ∈ s, σ x ∈ s) → (∀ x ∈ s, σ^[p] x = x) → (∀ x ∈ s, σ x ≠ x) → (∀ x ∈ s, Φ (σ x) = Φ x) → (∀ x ∈ s, ‖ι.symm (Φ x)‖ ≤ 1) → ‖ι.symm (∑ x ∈ s, Φ x)‖ ≤ (p : ℝ)⁻¹ := by
  intro p _ ι α σ s Φ hs hp hfree hinv hle
  classical
  have hna := PadicAlgCl.isNonarchimedean p
  have key : ∀ c ∈ s.image Φ,
      ‖ι.symm ((s.filter (fun x => Φ x = c)).card • c)‖ ≤ (p : ℝ)⁻¹ := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    have hd : p ∣ (s.filter (fun x => Φ x = Φ y)).card := by
      apply freeOrbit_prime_dvd_card σ
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hs x hx.1, (hinv x hx.1).trans hx.2⟩
      · intro x hx
        exact hp x (Finset.mem_filter.1 hx).1
      · intro x hx
        exact hfree x (Finset.mem_filter.1 hx).1
    obtain ⟨k, hk⟩ := hd
    rw [map_nsmul, nsmul_eq_mul, norm_mul, hk, Nat.cast_mul, norm_mul, norm_prime_Qbar_eq]
    have h1 : ‖((k : ℕ) : Qbar p)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ k
    have h2 := hle y hy
    calc (p : ℝ)⁻¹ * ‖((k : ℕ) : Qbar p)‖ * ‖ι.symm (Φ y)‖ ≤ (p : ℝ)⁻¹ * 1 * 1 := by gcongr
      _ = (p : ℝ)⁻¹ := by ring
  have hsum : ∑ x ∈ s, Φ x = ∑ c ∈ s.image Φ, (s.filter (fun x => Φ x = c)).card • c :=
    Finset.sum_comp (fun c => c) Φ
  rw [hsum, map_sum]
  generalize s.image Φ = T at key
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact (hna _ _).trans (max_le (key a (Finset.mem_insert_self a T))
      (ih fun c hc => key c (Finset.mem_insert_of_mem hc)))

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sum_free_orbits_le_inv_prime : ∀ (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (α : Type) (σ : α → α) (s : Finset α) (Φ : α → ℂ), (∀ x ∈ s, σ x ∈ s) → (∀ x ∈ s, σ^[p] x = x) → (∀ x ∈ s, σ x ≠ x) → (∀ x ∈ s, Φ (σ x) = Φ x) → (∀ x ∈ s, ‖ι.symm (Φ x)‖ ≤ 1) → ‖ι.symm (∑ x ∈ s, Φ x)‖ ≤ (p : ℝ)⁻¹ := by
  first | exact @GlobalTheory.HilbertThetaSeries.norm_sum_free_orbits_le | exact GlobalTheory.HilbertThetaSeries.norm_sum_free_orbits_le | (intros; apply GlobalTheory.HilbertThetaSeries.norm_sum_free_orbits_le <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.PoissonSummationGaussianConstantOnEvenBlocks
section
open Matrix Complex
open scoped Real

namespace GlobalTheory.HilbertThetaSeries

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dotProduct_transpose_mul_diagonal_mul_mulVec (P : Matrix ι ι ℝ) (t : ι → ℂ) (x : ι → ℝ) :
    (fun i => (x i : ℂ)) ⬝ᵥ ((P.map ofReal)ᵀ * diagonal t * P.map ofReal) *ᵥ (fun i => (x i : ℂ)) =
      ∑ j, t j * (((P *ᵥ x) j : ℝ) : ℂ) ^ 2 := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
    ← ofReal_mulVec_eq P x]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem siegelGaussIntegral_transpose_mul_diagonal_mul {P : Matrix ι ι ℝ} (hP : P.det ≠ 0)
    {t : ι → ℂ} (ht : ∀ i, 0 < (t i).im) :
    siegelGaussIntegral ((P.map ofReal)ᵀ * diagonal t * P.map ofReal) =
      (|P.det⁻¹| : ℝ) * ∏ i, (π / (-(π * I * t i))) ^ (1 / 2 : ℂ) := by
  have hb (i : ι) : 0 < (-(π * I * t i)).re := by simpa using mul_pos Real.pi_pos (ht i)
  have key := GaussianFourier.integral_cexp_neg_sum_mul_add hb fun _ => 0
  have hc := integral_comp_mulVec_of_det_ne_zero hP (f := fun y : ι → ℝ =>
    cexp (-∑ i, -(π * I * t i) * (y i : ℂ) ^ 2 + ∑ i, (0 : ℂ) * y i)) (by fun_prop)
  rw [key] at hc
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, Complex.exp_zero,
    mul_one] at hc
  rw [← hc, siegelGaussIntegral]
  congr 2 with x
  rw [dotProduct_transpose_mul_diagonal_mul_mulVec]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, zero_mul, Finset.sum_const_zero, add_zero]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem tsum_cexp_diagonal_gaussian {B : Matrix ι ι ℝ} (hB : B.det ≠ 0) (u : ι → ℝ) {z : ι → ℂ}
    (hz : ∀ i, 0 < (z i).im) :
    ∑' m : ι → ℤ, cexp (π * I * ∑ j, (-(z j)⁻¹) * (((B *ᵥ fun i => (m i : ℝ)) j + u j : ℝ) : ℂ) ^ 2) =
      ((|B.det| : ℝ) : ℂ)⁻¹ * (∏ j, (-I * z j) ^ (1 / 2 : ℂ)) *
        ∑' m : ι → ℤ, cexp (π * I * ∑ j, z j * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) *
          cexp (2 * π * I * ∑ j, (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j * u j : ℝ) : ℂ)) := by
  have hz0 (i : ι) : z i ≠ 0 := fun h0 => by simpa [h0] using hz i
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ht (i : ι) : 0 < (-(z i)⁻¹).im := by
    rw [neg_im, inv_im, neg_div, neg_neg]
    exact div_pos (hz i) (normSq_pos.2 (hz0 i))
  have ht0 (i : ι) : -(z i)⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero (hz0 i))
  have h := (isSiegel_diagonal_iff.2 ht).transpose_mul_mul hB
  have key := h.riemannTheta_eq_neg_inv (B⁻¹ *ᵥ u) 0
  rw [siegelGaussIntegral_transpose_mul_diagonal_mul hB ht, riemannTheta, riemannTheta] at key
  simp only [mulVec_zero, dotProduct_zero, mul_zero, Complex.exp_zero, mul_one,
    riemannThetaTerm_def] at key
  have hinv : ((B.map ofReal)ᵀ * diagonal (fun i => -(z i)⁻¹) * B.map ofReal)⁻¹ =
      ((B⁻¹ᵀ).map ofReal)ᵀ * diagonal (fun i => -z i) * (B⁻¹ᵀ).map ofReal := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_diagonal_of_ne_zero ht0,
      ← transpose_nonsing_inv, inv_map_ofReal hB, transpose_map, transpose_transpose,
      Matrix.mul_assoc]
    simp
  rw [hinv] at key
  have hc : ((|B.det⁻¹| : ℝ) : ℂ) * ∏ i, (π / -(π * I * -(z i)⁻¹)) ^ (1 / 2 : ℂ) =
      ((|B.det| : ℝ) : ℂ)⁻¹ * ∏ j, (-I * z j) ^ (1 / 2 : ℂ) := by
    rw [abs_inv, ofReal_inv]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    field_simp [hz0 i]
    simp
  rw [hc] at key
  refine (tsum_congr fun m => ?_).trans (key.trans (congrArg _ (tsum_congr fun m => ?_)))
  · have e := dotProduct_transpose_mul_diagonal_mul_mulVec B (fun i => -(z i)⁻¹)
      ((fun i => (m i : ℝ)) + B⁻¹ *ᵥ u)
    rw [mulVec_add, mulVec_mulVec, mul_nonsing_inv _ hB.isUnit, one_mulVec] at e
    simp only [Pi.add_apply, ofReal_add, ofReal_intCast] at e
    rw [e]
    simp only [Pi.zero_apply, ofReal_zero, add_zero, dotProduct, mul_zero, Finset.sum_const_zero,
      ofReal_add]
    congr 1
    ring
  · have e := dotProduct_transpose_mul_diagonal_mul_mulVec B⁻¹ᵀ (fun i => -z i)
      (fun i => (m i : ℝ))
    have e2 : (B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) ⬝ᵥ u = (fun i => (m i : ℝ)) ⬝ᵥ B⁻¹ *ᵥ u := by
      rw [mulVec_transpose, dotProduct_mulVec]
    simp only [ofReal_intCast] at e
    simp only [Pi.zero_apply, ofReal_zero, add_zero, zero_add]
    rw [neg_mulVec, dotProduct_neg, e, ← Complex.exp_add, ← ofReal_sum]
    change _ = cexp (_ + 2 * π * I * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) ⬝ᵥ u : ℝ) : ℂ))
    rw [e2]
    simp only [dotProduct, neg_mul, Finset.sum_neg_distrib, ofReal_sum, ofReal_mul, ofReal_intCast]
    congr 1
    ring

end General

theorem tsum_cexp_block_gaussian : ∀ (V κ : Type) [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ] (k : ℕ), Fintype.card κ = 2 * k → ∀ (B : Matrix (V × κ) (V × κ) ℝ), B.det ≠ 0 → ∀ (u : V × κ → ℝ) (z : V → ℂ), (∀ v, 0 < (z v).im) → ∑' m : V × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, (-(z j.1)⁻¹) * (((B *ᵥ fun i => (m i : ℝ)) j + u j : ℝ) : ℂ) ^ 2) = ((|B.det| : ℝ) : ℂ)⁻¹ * (∏ v, (-Complex.I * z v)) ^ k * ∑' m : V × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, z j.1 * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * ∑ j, (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j * u j : ℝ) : ℂ)) := by
  intro V κ _ _ _ _ k hk B hB u z hz
  rw [tsum_cexp_diagonal_gaussian hB u (z := fun j => z j.1) fun j => hz j.1]
  congr 2
  rw [Fintype.prod_prod_type, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [Finset.prod_const, Finset.card_univ, hk]
  rw [pow_mul, one_div, cpow_ofNat_inv_pow]

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poisson_summation_gaussian_constant_on_even_blocks : ∀ (V κ : Type) [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ] (k : ℕ), Fintype.card κ = 2 * k → ∀ (B : Matrix (V × κ) (V × κ) ℝ), B.det ≠ 0 → ∀ (u : V × κ → ℝ) (z : V → ℂ), (∀ v, 0 < (z v).im) → ∑' m : V × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, (-(z j.1)⁻¹) * (((B *ᵥ fun i => (m i : ℝ)) j + u j : ℝ) : ℂ) ^ 2) = ((|B.det| : ℝ) : ℂ)⁻¹ * (∏ v, (-Complex.I * z v)) ^ k * ∑' m : V × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, z j.1 * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * ∑ j, (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j * u j : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.HilbertThetaSeries.tsum_cexp_block_gaussian | exact GlobalTheory.HilbertThetaSeries.tsum_cexp_block_gaussian | (intros; apply GlobalTheory.HilbertThetaSeries.tsum_cexp_block_gaussian <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.QExpansionLinearCombination
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem hasQ_lin : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f g : Hn F → ℂ) (a b : F → ℂ) (c : ℂ), HasQ f a → HasQ g b → HasQ (f + g) (a + b) ∧ HasQ (c • f) (c • a) ∧ HasQ (f - g) (a - b) ∧ HasQ (fun _ : Hn F => c) (fun ξ => open Classical in if ξ = 0 then c else 0) := by
  intro F _ _ _ f g a b c hf hg
  obtain ⟨⟨D, hD, hfa⟩, hfs⟩ := hf
  obtain ⟨⟨E, hE, hgb⟩, hgs⟩ := hg
  have hez : ∀ z : Hn F, ez (0 : F) z = 1 := by
    intro z
    simp [ez, reAt]
  have scale : ∀ (ξ : F) (m k : ℕ), IsIntegral ℤ ((m : F) * ξ) →
      IsIntegral ℤ (((m * k : ℕ) : F) * ξ) ∧ IsIntegral ℤ (((k * m : ℕ) : F) * ξ) := by
    intro ξ m k h
    have e1 : ((m * k : ℕ) : F) * ξ = ((k : ℤ) : F) * ((m : F) * ξ) := by push_cast; ring
    have e2 : ((k * m : ℕ) : F) * ξ = ((k : ℤ) : F) * ((m : F) * ξ) := by push_cast; ring
    have hk : IsIntegral ℤ ((k : ℤ) : F) := isIntegral_algebraMap
    exact ⟨e1 ▸ hk.mul h, e2 ▸ hk.mul h⟩
  have both : ∀ ξ : F, a ξ ≠ 0 ∨ b ξ ≠ 0 →
      (ξ = 0 ∨ TP ξ) ∧ IsIntegral ℤ (((D * E : ℕ) : F) * ξ) := by
    intro ξ h
    rcases h with h | h
    · obtain ⟨h1, h2⟩ := hfa ξ h
      exact ⟨h1, (scale ξ D E h2).1⟩
    · obtain ⟨h1, h2⟩ := hgb ξ h
      exact ⟨h1, (scale ξ E D h2).2⟩
  have hDE : 0 < D * E := Nat.mul_pos hD hE
  refine ⟨⟨⟨D * E, hDE, ?_⟩, ?_⟩, ⟨⟨D, hD, ?_⟩, ?_⟩, ⟨⟨D * E, hDE, ?_⟩, ?_⟩, ⟨⟨1, one_pos, ?_⟩, ?_⟩⟩
  · intro ξ h
    apply both
    by_contra hc
    push_neg at hc
    apply h
    simp [hc.1, hc.2]
  · intro z
    simpa [Pi.add_apply, add_mul] using (hfs z).add (hgs z)
  · intro ξ h
    apply hfa
    intro h0
    apply h
    simp [h0]
  · intro z
    simpa [Pi.smul_apply, smul_eq_mul, mul_assoc] using (hfs z).mul_left c
  · intro ξ h
    apply both
    by_contra hc
    push_neg at hc
    apply h
    simp [hc.1, hc.2]
  · intro z
    simpa [Pi.sub_apply, sub_mul] using (hfs z).sub (hgs z)
  · intro ξ h
    have h0 : ξ = 0 := by
      by_contra hne
      apply h
      simp [hne]
    subst h0
    refine ⟨Or.inl rfl, ?_⟩
    simpa using (isIntegral_zero : IsIntegral ℤ (0 : F))
  · intro z
    have := hasSum_single (f := fun ξ : F => (open Classical in if ξ = 0 then c else 0) * ez ξ z) (0 : F) (by
      intro ξ hξ
      simp [hξ])
    convert this using 1
    simp [hez z]
end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansion_linear_combination : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f g : Hn F → ℂ) (a b : F → ℂ) (c : ℂ), HasQ f a → HasQ g b → HasQ (f + g) (a + b) ∧ HasQ (c • f) (c • a) ∧ HasQ (f - g) (a - b) ∧ HasQ (fun _ : Hn F => c) (fun ξ => open Classical in if ξ = 0 then c else 0) := by
  first | exact @GlobalTheory.HilbertThetaSeries.hasQ_lin | exact GlobalTheory.HilbertThetaSeries.hasQ_lin | (intros; apply GlobalTheory.HilbertThetaSeries.hasQ_lin <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.RationalGL2InfiniteFiniteFactor
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.RatPts

theorem pInf_algebraMap (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    TR.pInf F (algebraMap F (Ad F) x) = rhom x := by
  funext v
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal v) (WithAbs.toAbs _ x)

theorem pInf_ratGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ) = toInf γ := by
  ext i j v
  exact congrFun (pInf_algebraMap F (γ i j)) v

theorem ratGL_real_fin : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F),
    ratGL F 2 γ = TR.infGL F 2 (toInf γ) * finGL F 2 (toFin γ) ∧
      ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), ∃ τ : GL (Fin 2) F, Pos (toInf τ * h) := by
  intro F _ _ _ γ
  refine ⟨?_, fun h => ?_⟩
  · rw [← pInf_ratGL]
    exact (TR.infGL_mul_finGL (ratGL F 2 γ)).symm
  · obtain ⟨τ, hτ⟩ := GlobalTheory.WeakApproxGL.exists_rat_det_pos F 2 h
    refine ⟨τ, fun v => ?_⟩
    have e := hτ v
    rwa [MonoidHom.comp_apply, pInf_ratGL] at e

end GlobalTheory.HilbertThetaSeries.RatPts

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_GL2_infinite_finite_factor : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (γ : GL (Fin 2) F), ratGL F 2 γ = TR.infGL F 2 (toInf γ) * finGL F 2 (toFin γ) ∧ ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), ∃ τ : GL (Fin 2) F, Pos (toInf τ * h) := by
  first | exact @GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin | exact GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin | (intros; apply GlobalTheory.HilbertThetaSeries.RatPts.ratGL_real_fin <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.SlashAddSmulPow
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem slash_add_smul_pow : ∀ (F : Type) [Field F] [NumberField F] (k M : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (f g : Hn F → ℂ) (c : ℂ), sl0 k h (f + g) = sl0 k h f + sl0 k h g ∧ sl0 k h (c • f) = c • sl0 k h f ∧ sl0 (k * M) h (f ^ M) = sl0 k h f ^ M ∧ sl k h (f + g) = sl k h f + sl k h g ∧ sl k h (c • f) = c • sl k h f ∧ sl (k * M) h (f ^ M) = sl k h f ^ M := by
  intro F _ _ k M h f g c
  have h0a : sl0 k h (f + g) = sl0 k h f + sl0 k h g := by
    funext z; simp only [sl0, Pi.add_apply]; ring
  have h0s : sl0 k h (c • f) = c • sl0 k h f := by
    funext z; simp only [sl0, Pi.smul_apply, smul_eq_mul]; ring
  have h0p : sl0 (k * M) h (f ^ M) = sl0 k h f ^ M := by
    funext z; simp only [sl0, Pi.pow_apply]; rw [mul_pow, pow_mul]
  refine ⟨h0a, h0s, h0p, ?_, ?_, ?_⟩
  · funext z; simp only [sl, h0a, Pi.add_apply]; ring
  · funext z; simp only [sl, h0s, Pi.smul_apply, smul_eq_mul]; ring
  · funext z
    simp only [sl, h0p, Pi.pow_apply]
    rw [mul_pow]
    congr 1
    have hx : (0 : ℝ) ≤ ∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| :=
      Finset.prod_nonneg fun v _ => abs_nonneg _
    rw [← Complex.ofReal_pow, ← Real.rpow_mul_natCast hx]
    congr 2
    push_cast; ring

end GlobalTheory.HilbertThetaSeries
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSeriesTranslationTwistsCoefficients
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

open UpperHalfPlane hiding I

namespace GlobalTheory.HilbertThetaSeries

theorem reAt_eq_rhom {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    reAt v x = rhom x v := by
  unfold reAt
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]
  rfl

theorem reAt_mul {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x y : F) :
    reAt v (x * y) = reAt v x * reAt v y := by
  rw [reAt_eq_rhom, reAt_eq_rhom, reAt_eq_rhom, map_mul, Pi.mul_apply]

theorem sum_reAt_eq_trace {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    ∑ v, (reAt v x : ℂ) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  have key : ∑ v : InfinitePlace F, reAt v x = ∑ σ : F →+* ℝ, σ x := by
    refine Fintype.sum_bijective (fun v => InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))
      ⟨?_, ?_⟩ _ _ ?_
    · intro v w h
      have hvw : v.embedding = w.embedding := by
        ext y
        rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v),
          ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal w)]
        exact congrArg (fun f : F →+* ℝ => ((f y : ℝ) : ℂ)) h
      rw [← InfinitePlace.mk_embedding v, ← InfinitePlace.mk_embedding w, hvw]
    · intro φ
      have hψ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp φ) := by
        rw [ComplexEmbedding.isReal_iff]
        ext y
        simp
      refine ⟨InfinitePlace.mk (Complex.ofRealHom.comp φ), ?_⟩
      ext y
      apply Complex.ofReal_injective
      rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hψ]
      rfl
    · intro v
      exact reAt_eq_rhom v x
  rw [← Complex.ofReal_sum, key, ← trace_eq_sum_realEmbeddings, Complex.ofReal_ratCast]

theorem cmp_toInf_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : GL (Fin 2) F)
    (v : InfinitePlace F) (i j : Fin 2) :
    ((cmp v (toInf g) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = rhom ((g : Matrix (Fin 2) (Fin 2) F) i j) v := rfl

theorem denom_translate {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (b : F) (v : InfinitePlace F) (w : ℂ) :
    denom (cmp v (toInf (aff 1 b))) w = 1 := by
  simp [denom, cmp_toInf_apply, aff]

theorem coe_translate_smul {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (b : F) (v : InfinitePlace F) (w : ℍ) :
    ((cmp v (toInf (aff 1 b)) • w : ℍ) : ℂ) = (w : ℂ) + (reAt v b : ℂ) := by
  have e : ∀ i j, ((cmp v (toInf (aff 1 b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      rhom ((aff (1 : Fˣ) b : Matrix (Fin 2) (Fin 2) F) i j) v := fun i j => cmp_toInf_apply _ v i j
  have hdet : 0 < ((Matrix.GeneralLinearGroup.det (cmp v (toInf (aff 1 b)))) : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, e, e, e, e]
    simp [aff]
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet, denom_translate]
  simp only [UpperHalfPlane.num, e]
  simp [aff, reAt_eq_rhom]

theorem ez_translate {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (b ξ : F) (z : Hn F) :
    ez ξ (act (toInf (aff 1 b)) z) = et (b * ξ) * ez ξ z := by
  rw [mul_comm b ξ]
  have h := sum_reAt_eq_trace (ξ * b)
  simp only [ez, et, act, coe_translate_smul]
  rw [← Complex.exp_add, ← h]
  congr 1
  simp only [reAt_mul, Complex.ofReal_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem th_translate : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ]
    (G : Matrix κ κ ℤ) (k : ℕ) (b : F) (Φ : (κ → F) → ℂ),
    sl0 k (toInf (aff 1 b)) (th G Φ) = th G (fun x => Φ x * et (b * QF G x)) := by
  intro F _ _ _ κ _ _ G k b Φ
  funext z
  simp only [sl0, denom_translate, Finset.prod_const_one, inv_one, one_pow, one_mul, th]
  refine tsum_congr fun x => ?_
  rw [ez_translate]
  ring

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_translation_twists_coefficients : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (k : ℕ) (b : F) (Φ : (κ → F) → ℂ), sl0 k (toInf (aff 1 b)) (th G Φ) = th G (fun x => Φ x * et (b * QF G x)) := by
  first | exact @GlobalTheory.HilbertThetaSeries.th_translate | exact GlobalTheory.HilbertThetaSeries.th_translate | (intros; apply GlobalTheory.HilbertThetaSeries.th_translate <;> assumption)
end

