import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
section
open NumberField

namespace GlobalTheory

open NumberField in

theorem _root_.GlobalTheory.log_classNumber_le_log_abs_discr_div :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (f : ℕ),
      Module.finrank ℚ E = 2*f →
      Real.log (classNumber E) ≤ f*(Real.log |(discr E : ℝ)|/(2*f)) +
        2*f*Real.log (1 + f*(Real.log |(discr E : ℝ)|/(2*f))) := by
  intro E _ _ _ f hf
  have hdeg : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hf0 : (f : ℝ) ≠ 0 := by
    have : f ≠ 0 := by
      rintro rfl
      omega
    exact_mod_cast this
  have key : (f : ℝ) * (Real.log |(discr E : ℝ)| / (2 * f)) = Real.log √|(discr E : ℝ)| := by
    rw [Real.log_sqrt (abs_nonneg _)]
    field_simp
  rw [key]
  have hb := _root_.GlobalTheory.classNumber_le_of_finrank_eq_two_mul E hf
  have hpos : (0 : ℝ) < classNumber E := by exact_mod_cast classNumber_pos E
  have hs : 1 ≤ √|(discr E : ℝ)| := _root_.GlobalTheory.one_le_sqrt_abs_discr E
  have hL : 0 ≤ Real.log √|(discr E : ℝ)| := Real.log_nonneg hs
  calc Real.log (classNumber E)
      ≤ Real.log (√|(discr E : ℝ)| * (1 + Real.log √|(discr E : ℝ)|) ^ (2 * f)) :=
        Real.log_le_log hpos hb
    _ = Real.log √|(discr E : ℝ)| + ((2 * f : ℕ) : ℝ) * Real.log (1 + Real.log √|(discr E : ℝ)|) := by
        rw [Real.log_mul (by linarith) (pow_ne_zero _ (by linarith)), Real.log_pow]
    _ = Real.log √|(discr E : ℝ)| + 2 * f * Real.log (1 + Real.log √|(discr E : ℝ)|) := by
        push_cast
        ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MatrixInvEntriesBoundedStatement
section
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bound_inv_entries_of_bounded_entries : ∀ (R : Type) [NormedCommRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R] (n : ℕ) (G : Matrix (Fin n) (Fin n) R → ℝ), Continuous G → (∀ c, G c ≠ 0 → IsUnit c) → ∀ B ε : ℝ, 0 < ε → ∃ C : ℝ, (∀ c : Matrix (Fin n) (Fin n) R, (∀ i j, ‖c i j‖ ≤ B) → G c ≤ C) ∧ ∀ c : GL (Fin n) R, (∀ i j, ‖c.1 i j‖ ≤ B) → ε ≤ G c.1 → ∀ i j, ‖c⁻¹.1 i j‖ ≤ C := by
  first | exact @GlobalTheory.matrix_inv_entries_bounded | exact GlobalTheory.matrix_inv_entries_bounded | (intros; apply GlobalTheory.matrix_inv_entries_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableHeckeOperatorsExplicit
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

private theorem im_mul_pos' {q : ℕ} (hq : 0 < q) {z : ℂ} (hz : 0 < z.im) : 0 < ((q : ℂ) * z).im := by
  have : (0 : ℝ) < q := by exact_mod_cast hq
  simpa using mul_pos this hz

private theorem im_div_pos' {q : ℕ} (hq : 0 < q) {z : ℂ} (hz : 0 < z.im) (j : ℕ) :
    0 < ((z + j) / (q : ℂ)).im := by
  have : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Complex.div_natCast_im]
  simpa using div_pos hz this

theorem uOp_mdiff {q : ℕ} (hq : 0 < q) {f : ℍ → ℂ} (hf : MDiff f) : MDiff (uOp q f) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have h : DifferentiableOn ℂ (fun z : ℂ =>
      (q : ℂ)⁻¹ * ∑ j ∈ Finset.range q, (f ∘ ofComplex) ((z + j) / q)) {z : ℂ | 0 < z.im} := by
    refine DifferentiableOn.const_mul ?_ _
    refine DifferentiableOn.fun_sum fun j _ => ?_
    exact hf.comp (f := fun z : ℂ => (z + j) / (q : ℂ)) (by fun_prop) fun z hz => im_div_pos' hq hz j
  refine h.congr fun z hz => ?_
  simp only [Function.comp, uOp, ofComplex_apply_of_im_pos hz]

theorem vOp_mdiff {q : ℕ} (hq : 0 < q) {f : ℍ → ℂ} (hf : MDiff f) : MDiff (vOp q f) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have h : DifferentiableOn ℂ (fun z : ℂ => (f ∘ ofComplex) ((q : ℂ) * z)) {z : ℂ | 0 < z.im} :=
    hf.comp (f := fun z : ℂ => (q : ℂ) * z) (by fun_prop) fun z hz => im_mul_pos' hq hz
  refine h.congr fun z hz => ?_
  simp only [Function.comp, vOp, ofComplex_apply_of_im_pos hz]

theorem hecke_mdiff : ∀ (q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < q → MDiff f →
    MDiff (GlobalTheory.Hk.uOp q f) ∧ MDiff (GlobalTheory.Hk.vOp q f) ∧ MDiff (GlobalTheory.Hk.heckeT k q σ f) := by
  intro q k σ f hq hf
  refine ⟨uOp_mdiff hq hf, vOp_mdiff hq hf, ?_⟩
  have hs : MDiff (f ∣[k] σ) := by
    rw [ModularForm.SL_slash]
    exact MDifferentiable.slash hf k _
  exact (uOp_mdiff hq hf).add ((vOp_mdiff hq hs).const_smul _)

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemAdjoinDivOfFixedStatement
section
open scoped NNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_div_mem_adjoin_of_fixed : ∀ (R Ω : Type) [CommRing R] [Nontrivial R] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra.IsAlgebraic R Ω], Function.Injective (algebraMap R Ω) → ∀ (S : Set Ω) (x : Ω), (∀ g : Ω ≃ₐ[R] Ω, (∀ s ∈ S, g s = s) → g x = x) → ∃ b ∈ Algebra.adjoin R S, ∃ c ∈ Algebra.adjoin R S, c ≠ 0 ∧ x = b / c := by
  first | exact @GlobalTheory.mem_adjoin_div_of_fixed | exact GlobalTheory.mem_adjoin_div_of_fixed | (intros; apply GlobalTheory.mem_adjoin_div_of_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemMaximalPowOfJetsVanishStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maximal_pow_of_jets_vanish : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (Δ : ℕ → A →ₗ[k] k), 2 ≤ N → Δ 0 1 = 1 → (∀ l < N, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ p u * Δ (l - p) w)) → (∃ π : A, Δ 1 π = 1) →
 ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ 0 u = 0) ∧ ∀ f : A, (∀ l < N, Δ l f = 0) → f ∈ Q ^ N := by
  first | exact @GlobalTheory.mem_pow_of_jets_vanish | exact GlobalTheory.mem_pow_of_jets_vanish | (intros; apply GlobalTheory.mem_pow_of_jets_vanish <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemOfSumMulPowMemOfValuationZpowStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_mem_of_sum_mul_pow_mem_of_valuation_zpow : ∀ (Ω : Type) [Field Ω] (A : ValuationSubring Ω) (N : ℕ) (π ℓ : Ω) (c : ℕ → Ω), 0 < N → ℓ ≠ 0 → A.valuation ℓ < 1 → A.valuation π ^ N = A.valuation ℓ → (∀ i < N, c i ≠ 0 → ∃ k : ℤ, A.valuation (c i) = A.valuation ℓ ^ k) → (∑ i ∈ Finset.range N, c i * π ^ i) ∈ A → ∀ i < N, c i ∈ A := by
  first | exact @GlobalTheory.mem_of_sum_mul_pow_mem_of_valuation_zpow | exact GlobalTheory.mem_of_sum_mul_pow_mem_of_valuation_zpow | (intros; apply GlobalTheory.mem_of_sum_mul_pow_mem_of_valuation_zpow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSpanEigenOfBaseChangeEigenStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_eigen_of_baseChange_eigen' : ∀ (l : ℕ) [Fact l.Prime] (M S : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M) [Module.Free ℤ_[l] B]
  (g : S → Module.End ℤ_[l] M) (χ : S → ℤ_[l]), (∀ s, ∀ b ∈ B, g s b ∈ B) →
  ∀ x ∈ LinearMap.range (LinearMap.baseChange (PadicAlgCl l) B.subtype),
  (∀ s, LinearMap.baseChange (PadicAlgCl l) (g s) x = algebraMap ℤ_[l] (PadicAlgCl l) (χ s) • x) →
  x ∈ Submodule.span (PadicAlgCl l) {y | ∃ b ∈ B, (∀ s, g s b = χ s • b) ∧ y = (1 : PadicAlgCl l) ⊗ₜ[ℤ_[l]] b} := by
  first | exact @GlobalTheory.mem_span_eigen_of_baseChange_eigen | exact GlobalTheory.mem_span_eigen_of_baseChange_eigen | (intros; apply GlobalTheory.mem_span_eigen_of_baseChange_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTwInv
section
noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

variable {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]

def twInv (Γ : Subgroup G) (g : G) (A : E →ₗ[ℂ] E) : Submodule ℂ (G → E) :=
  GlobalTheory.TwistedInverseSubgroups.leftInvRightTwisted Γ g A

def cocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) : Submodule ℂ (Γ → E) where
  carrier := {z | ∀ γ δ : Γ, z (γ * δ) = ρ (δ : G) (z γ) + z δ}
  add_mem' := by
    intro z z' h h' γ δ
    simp only [Pi.add_apply, h γ δ, h' γ δ, map_add]
    abel
  zero_mem' := fun _ _ => by simp
  smul_mem' := by
    intro c z h γ δ
    simp only [Pi.smul_apply, h γ δ, map_smul, smul_add]

def extn (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G) : Submodule ℂ (G → E) where
  carrier := {u | (∀ γ ∈ Γ, ∀ x, u (γ * x) - u x = ρ x (u γ - u 1)) ∧ ∀ x, u (x * s) = ρ s (u x)}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun γ hγ x => ?_, fun x => by simp [h2, h2']⟩
    simp only [Pi.add_apply]
    rw [add_sub_add_comm, h1 γ hγ, h1' γ hγ, add_sub_add_comm, map_add]
  zero_mem' := ⟨fun _ _ _ => by simp, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨fun γ hγ x => ?_, fun x => by simp [h2]⟩
    simp only [Pi.smul_apply]
    rw [← smul_sub, h1 γ hγ, ← smul_sub, map_smul]

def relThree (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (t : G) : Submodule ℂ (G → E) where
  carrier := {Φ | Φ ∈ twInv Γ (t ^ 3) (ρ (t ^ 3)) ∧
    ∀ x, ρ (t ^ 2) (Φ x) + ρ t (Φ (x * t)) + Φ (x * t ^ 2) = 0}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨Submodule.add_mem _ h1 h1', fun x => ?_⟩
    simp only [Pi.add_apply, map_add]
    rw [← add_zero (0 : E)]
    nth_rewrite 1 [← h2 x]
    rw [← h2' x]
    abel
  zero_mem' := ⟨Submodule.zero_mem _, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨Submodule.smul_mem _ c h1, fun x => ?_⟩
    simp only [Pi.smul_apply, map_smul]
    rw [← smul_add, ← smul_add, h2, smul_zero]

end GlobalTheory.HeckeFamilyMatrices.CocBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitDistanceFixedSubfield
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

open Polynomial

theorem moves_fix_of_moves : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L] [Finite G], (∀ (g : G) (x : L), v (g • x) = v x) →
    ∀ (N : Subgroup G) (i : ℝ≥0), i < 1 → (∀ τ ∈ N, ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ i) →
    ∀ σ : G, Moves v ⊤ σ → Moves v (Fix L N) σ := by
  intro L _ v G _ _ _ hinv N i hi hN σ hσ r hr
  classical
  by_contra hcon
  push_neg at hcon
  haveI := Fintype.ofFinite G
  set n := Fintype.card N with hn_def
  have hn : n ≠ 0 := Fintype.card_ne_zero
  set t : ℝ≥0 := max i (r ^ ((n : ℝ)⁻¹)) with ht_def
  have ht1 : t < 1 := max_lt hi (NNReal.rpow_lt_one hr (by positivity))
  have hrt : r ≤ t ^ n := by
    calc r = (r ^ ((n : ℝ)⁻¹)) ^ n := (NNReal.rpow_inv_natCast_pow r hn).symm
      _ ≤ t ^ n := pow_le_pow_left₀ zero_le (le_max_right _ _) n
  obtain ⟨x, -, hx1, hxt⟩ := hσ t ht1

  have hfac : ∀ τ : N, v (x - σ • ((τ : G) • x)) = v (σ • x - x) := by
    intro τ
    have h1 : v (σ • x - σ • ((τ : G) • x)) < v (x - σ • x) := by
      rw [← smul_sub, hinv, Valuation.map_sub_swap, Valuation.map_sub_swap v x]
      exact lt_of_le_of_lt (le_trans (hN τ τ.2 x hx1) (le_max_left _ _)) hxt
    have h2 : x - σ • ((τ : G) • x) = (x - σ • x) + (σ • x - σ • ((τ : G) • x)) := by ring
    rw [h2, Valuation.map_add_eq_of_lt_left v h1, Valuation.map_sub_swap]

  set P : L[X] := ∏ τ : N, (X - C ((τ : G) • x)) with hP_def
  have hint : ∀ τ : N, (τ : G) • x ∈ v.integer := fun τ => by
    rw [Valuation.mem_integer_iff, hinv]; exact hx1
  set Q : (v.integer)[X] := ∏ τ : N, (X - C (⟨(τ : G) • x, hint τ⟩ : v.integer)) with hQ_def
  have hPQ : P = Q.map (v.integer.subtype) := by
    simp [hP_def, hQ_def, Polynomial.map_prod]
  have hcint : ∀ k, v (P.coeff k) ≤ 1 := by
    intro k
    rw [hPQ, coeff_map]
    exact (Q.coeff k).2
  have hcfix : ∀ k, P.coeff k ∈ Fix L N := by
    intro k m
    have hmap : P.map (MulSemiringAction.toRingHom G L (m : G)) = P := by
      rw [hP_def, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C, MulSemiringAction.toRingHom_apply, smul_smul]
      exact Fintype.prod_equiv (Equiv.mulLeft m) _ _ (fun τ => by simp)
    have := congrArg (fun p => p.coeff k) hmap
    have h' : (m : G) • P.coeff k = P.coeff k := by simpa [coeff_map] using this
    exact h'
  have hPx : P.eval x = 0 := by
    rw [hP_def, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)
  have hPσx : (P.map (MulSemiringAction.toRingHom G L σ)).eval x = ∏ τ : N, (x - σ • ((τ : G) • x)) := by
    simp [hP_def, Polynomial.map_prod, eval_prod]

  have hdiff : v ((P.map (MulSemiringAction.toRingHom G L σ) - P).eval x) ≤ r := by
    rw [eval_eq_sum, Polynomial.sum_def]
    apply Valuation.map_sum_le
    intro k _
    rw [map_mul, map_pow, coeff_sub, coeff_map, MulSemiringAction.toRingHom_apply]
    calc v (σ • P.coeff k - P.coeff k) * v x ^ k ≤ r * 1 :=
          mul_le_mul' (hcon _ (hcfix k) (hcint k)) (pow_le_one₀ zero_le hx1)
      _ = r := mul_one r
  rw [eval_sub, hPx, sub_zero, hPσx, map_prod] at hdiff
  simp only [hfac, Finset.prod_const, Finset.card_univ] at hdiff
  have := pow_lt_pow_left₀ hxt zero_le hn
  exact absurd (lt_of_le_of_lt (hdiff.trans hrt) this) (lt_irrefl _)

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastEqOneOfCoprime
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem valuation_nnreal_natCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (n : ℕ) : v (n : L) ≤ 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    push_cast
    exact le_trans (v.map_add _ _) (max_le ih (by simp))

theorem valuation_nnreal_intCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (z : ℤ) : v (z : L) ≤ 1 := by
  cases z with
  | ofNat n => simpa using valuation_nnreal_natCast_le_one v n
  | negSucc n =>
    rw [Int.cast_negSucc, Valuation.map_neg]
    exact_mod_cast valuation_nnreal_natCast_le_one v (n + 1)

theorem natCast_eq_one_of_coprime :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p l : ℕ), v (p : L) < 1 → Nat.Coprime l p → v (l : L) = 1 := by
  intro L _ v p l hp hlp
  refine le_antisymm (valuation_nnreal_natCast_le_one v l) ?_
  by_contra hlt
  push_neg at hlt
  have hb : ((Nat.gcd l p : ℕ) : ℤ) = (l : ℤ) * Nat.gcdA l p + (p : ℤ) * Nat.gcdB l p := Nat.gcd_eq_gcd_ab l p
  rw [hlp, Nat.cast_one] at hb
  have hL : (1 : L) = (l : L) * (Nat.gcdA l p : L) + (p : L) * (Nat.gcdB l p : L) := by
    have := congrArg (fun z : ℤ => (z : L)) hb
    push_cast at this
    exact this
  have h1 : v (1 : L) < 1 := by
    rw [hL]
    refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
    · rw [v.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (valuation_nnreal_intCast_le_one v (Nat.gcdA l p))) hlt
    · rw [v.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (valuation_nnreal_intCast_le_one v (Nat.gcdB l p))) hp
  simp at h1

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NewtonPowerSeriesSurjectiveLinearizationSolutionStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newton_powerSeries_surjective_linearization_solution : ∀ (k ι κ : Type) [Field k] [Fintype ι] [Fintype κ] (G : (ι → PowerSeries k) → κ → PowerSeries k) (x₀ : ι → k) (L : (ι → k) →ₗ[k] (κ → k)), Function.Surjective L →
 (∀ e, PowerSeries.constantCoeff (G (fun i => PowerSeries.C (x₀ i)) e) = 0) →
 (∀ (x h : ι → PowerSeries k) (m : ℕ), 1 ≤ m → (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) → ∀ e,
   (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ G (fun i => x i + PowerSeries.X ^ m * h i) e - G x e - PowerSeries.X ^ m * PowerSeries.C (L (fun i => PowerSeries.constantCoeff (h i)) e)) →
 ∃ x : ι → PowerSeries k, (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) ∧ ∀ e, G x e = 0 := by
  first | exact @GlobalTheory.newton_powerSeries_target | exact GlobalTheory.newton_powerSeries_target | (intros; apply GlobalTheory.newton_powerSeries_target <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormCompatibleSystemFrobeniusEqZeroStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normCompatible_system_frobenius_eq_zero : ∀ (O H : Type) [CommRing O] [IsNoetherianRing O] [IsLocalRing O] [AddCommGroup H] [Module O H] (l : ℕ) [Fact l.Prime], ¬ IsUnit (l : O) → ∀ (q : ℕ) (hq : Nat.Coprime q l), 2 ≤ q → ∀ (M : Submodule O H), M.FG → ∀ (F : H →ₗ[O] H), (∀ x ∈ M, F x ∈ M) → ∀ (c : ∀ r : ℕ, (ZMod (l ^ r))ˣ → H), (∀ r x, c r x ∈ M) → (∀ r x, F (c r x) = c r (x * ZMod.unitOfCoprime q (Nat.Coprime.pow_right r hq))) → (∀ r x, c r x = ∑ x' ∈ Finset.univ.filter (fun x' : (ZMod (l ^ (r + 1)))ˣ => Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x), c (r + 1) x') → ∀ r x, c r x = 0 := by
  first | exact @GlobalTheory.NormSystemVanishing.normCompatible_eq_zero | exact GlobalTheory.NormSystemVanishing.normCompatible_eq_zero | (intros; apply GlobalTheory.NormSystemVanishing.normCompatible_eq_zero <;> assumption)
end

