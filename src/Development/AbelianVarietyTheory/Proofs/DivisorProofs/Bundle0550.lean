import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0545
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHessianPosSemidefOfLeviFormNonnegStatement
section
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexHessian_posSemidef_of_leviForm_nonneg : ∀ (n : ℕ) (φ : V n → ℝ) (z : V n), ContDiffAt ℝ 2 φ z → (∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => (φ v : ℂ)) z ξ).re) → (cHess n (fun v => (φ v : ℂ)) z).PosSemidef := by
  first | exact @GlobalTheory.cHess_posSemidef_of_levi_nonneg | exact GlobalTheory.cHess_posSemidef_of_levi_nonneg | (intros; apply GlobalTheory.cHess_posSemidef_of_levi_nonneg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantFrameComparisonUnit
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem exists_freeForm : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → Nonempty (FreeForm D N ψ) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D ψ hψ
  obtain ⟨eT, eM, hT, hM, hrat⟩ := GlobalTheory.T.determinant_frame_comparison p C v O hv ε hε Λ N h hh D
  obtain ⟨tM, htM, htw⟩ := GlobalTheory.T.exists_frobenius_twisted_frame p O Λ N h ψ D.ρM eM hψ hM
  have hTw := GlobalTheory.T.frame_psi_coordinates_padic p O Λ N h ψ eT hψ hrat
  obtain ⟨hscal, hFG, hG, hΨ, hΨ'⟩ := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D
  obtain ⟨-, -, ψ₀, φ₀, hψ₀, -, -, hφψ⟩ := GlobalTheory.DetInv.psi_phi_tensor p O Λ
  have hψeq : ∀ r, ψ r = ψ₀ r := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a l => rw [hψ, hψ₀]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hsurj : Function.Surjective ψ := fun r => ⟨φ₀ r, by rw [hψeq, hφψ]⟩
  have calc₁ := fun (e e' e'' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) =>
    GlobalTheory.T.frame_matrix_composition_unique p O Λ N h e e' e''
  obtain ⟨F, hF⟩ := GlobalTheory.T.exists_matrix_of_intertwiner p O Λ N h (rhoTA D) D.ρM eT eM D.F hT hM (fun l => D.F_act l)
  obtain ⟨G, hGm⟩ := GlobalTheory.T.exists_matrix_of_intertwiner p O Λ N h D.ρM (rhoTA D) eM eT D.G hM hT hG
  obtain ⟨Ψ, hΨm⟩ := GlobalTheory.T.exists_matrix_of_intertwiner p O Λ N h (fun l => (D.ρM l).map (phiInv p O)) D.ρM tM eM D.Ψ
    htM hM hΨ
  obtain ⟨Ψ', hΨ'm⟩ := GlobalTheory.T.exists_matrix_of_intertwiner p O Λ N h D.ρM (fun l => (D.ρM l).map (phiInv p O)) eM tM D.Ψ'
    hM htM hΨ'
  have hFψ := GlobalTheory.T.frame_transition_psi_matrix p O Λ N h ψ eT eM eT tM D.F F hsurj hTw htw hF
  refine ⟨⟨eT, eM, F, G, Ψ, Ψ', hT, hM, hF, hGm, ?_, ?_, ?_, ?_⟩⟩
  · have h1 := (calc₁ eT eM eT).1 _ _ _ _ hF hGm
    rw [D.G_mul_F] at h1
    exact (calc₁ eT eT eT).2.1 _ _ _ h1 ((calc₁ eT eT eT).2.2 (mu ε))
  · have h1 := (calc₁ eM eT eM).1 _ _ _ _ hGm hF
    rw [hFG] at h1
    exact (calc₁ eM eM eM).2.1 _ _ _ h1 ((calc₁ eM eM eM).2.2 (mu ε))
  · have h1 := (calc₁ eT tM eM).1 _ _ _ _ hFψ hΨm
    rw [← D.F_eq] at h1
    exact (calc₁ eT eM eM).2.1 _ _ _ hF h1
  · have h1 := (calc₁ eM tM eM).1 _ _ _ _ hΨ'm hΨm
    rw [D.Ψ_mul] at h1
    exact (calc₁ eM eM eM).2.1 _ _ _ h1 ((calc₁ eM eM eM).2.2 (xi ε))

end GlobalTheory.DetInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantValuationIotaScalarStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_valuation_iota_scalar : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (ψ : RL p O Λ →+* RL p O Λ) (Φ : FreeForm D N ψ) (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → D.lieRank σ ≤ N ∧ ∃ c : C, c ≠ 0 ∧ Lead ((algebraMap O C).comp f) (inA (xi ε)) Φ.F.det (D.lieRank σ) c := by
  first | exact @GlobalTheory.DetInv.lead_det_all | exact GlobalTheory.DetInv.lead_det_all | (intros; apply GlobalTheory.DetInv.lead_det_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesHarishChandra
section
open Finset

namespace GlobalTheory.DSParam

open Finset in
private theorem diagonal_exp_single_two_pi_eq_one {n : ℕ} (a : Fin n) :
    (Matrix.diagonal fun b ↦
      Complex.exp (↑((Pi.single a (2 * Real.pi) : Fin n → ℝ) b) * Complex.I)) = 1 := by
  rw [← Matrix.diagonal_one]
  congr 1
  funext b
  by_cases h : b = a
  · subst h; simp [Complex.exp_two_pi_mul_I]
  · simp [Pi.single_apply, h]

open Finset in
private theorem exists_int_eq_weight_of_isWtOn {n : ℕ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {K : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hK : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ K)
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {μ : Fin n → ℝ} {v : H} (hv0 : v ≠ 0)
    (hv : _root_.Formalism.MainNotions.S.IsWtOn K σ μ v) (a : Fin n) : ∃ m : ℤ, μ a = m := by
  unfold _root_.Formalism.MainNotions.S.IsWtOn at hv
  have h1 := hv 0 (by simpa using hK)
  have h2 := hv (Pi.single a (2 * Real.pi)) (by rw [diagonal_exp_single_two_pi_eq_one]; exact hK)
  rw [diagonal_exp_single_two_pi_eq_one] at h2
  simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    Matrix.diagonal_one, mul_zero, Finset.sum_const_zero, one_smul] at h1
  rw [h1] at h2
  have hsum : (∑ b, μ b * (Pi.single a (2 * Real.pi) : Fin n → ℝ) b) = μ a * (2 * Real.pi) := by
    simp [Pi.single_apply, mul_ite]
  rw [hsum] at h2
  have he : Complex.exp (↑(μ a * (2 * Real.pi)) * Complex.I) = 1 := by
    by_contra hne
    apply hv0
    have : (Complex.exp (↑(μ a * (2 * Real.pi)) * Complex.I) - 1) • v = 0 := by
      rw [sub_smul, ← h2, one_smul, sub_self]
    exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp he
  refine ⟨m, ?_⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have : ((μ a : ℝ) : ℂ) = (m : ℂ) := by
    apply mul_right_cancel₀ hpi
    push_cast at hm
    linear_combination hm
  exact_mod_cast this

open Finset in
private theorem one_mem_Kset_divisor {n : ℕ} (ε : Fin n → Bool) :
    (1 : Matrix (Fin n) (Fin n) ℂ) ∈ _root_.Formalism.REAL.Kset ε := by
  unfold _root_.Formalism.REAL.Kset
  exact ⟨one_mem _, by simp⟩

open Finset in
private theorem card_same_diff_sign_lt_gt_add_one_eq {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    #{b | a < b ∧ ε b = ε a} + #{b | b < a ∧ ε b = ε a} + #{b | a < b ∧ ε b ≠ ε a}
      + #{b | b < a ∧ ε b ≠ ε a} + 1 = n := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have key : ∀ b, ((if a < b ∧ ε b = ε a then 1 else 0) + (if b < a ∧ ε b = ε a then 1 else 0) +
      (if a < b ∧ ε b ≠ ε a then 1 else 0) + (if b < a ∧ ε b ≠ ε a then 1 else 0) : ℕ)
      = if b = a then 0 else 1 := by
    intro b
    rcases lt_trichotomy a b with h | h | h
    · have h1 : b ≠ a := ne_of_gt h
      have h2 : ¬ b < a := not_lt.mpr h.le
      by_cases he : ε b = ε a <;> simp [h, h1, h2, he]
    · subst h; simp
    · have h1 : b ≠ a := ne_of_lt h
      have h2 : ¬ a < b := not_lt.mpr h.le
      by_cases he : ε b = ε a <;> simp [h, h1, h2, he]
  rw [Finset.sum_congr rfl (fun b _ => key b)]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
    Fintype.card_fin]
  have := a.isLt
  omega

open Finset in
private theorem exists_int_rhoC_sub_rhoN_sub_half {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    ∃ m : ℤ, _root_.Formalism.REAL.rhoC ε a - _root_.Formalism.REAL.rhoN ε a - ((n : ℝ) - 1) / 2 = m := by
  have h := card_same_diff_sign_lt_gt_add_one_eq ε a
  unfold _root_.Formalism.REAL.rhoC _root_.Formalism.REAL.rhoN
  refine ⟨-((#{b | b < a ∧ ε b = ε a} : ℕ) + (#{b | a < b ∧ ε b ≠ ε a} : ℕ) : ℤ), ?_⟩
  have hr : ((#{b | a < b ∧ ε b = ε a} : ℕ) : ℝ) + #{b | b < a ∧ ε b = ε a}
      + #{b | a < b ∧ ε b ≠ ε a} + #{b | b < a ∧ ε b ≠ ε a} + 1 = n := by
    exact_mod_cast h
  push_cast
  linear_combination hr / 2

open Finset in

theorem _root_.GlobalTheory.DSParam.isHCParam_of_isDS : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    StrictAnti lam → _root_.Formalism.MainNotions.S.IsDS ε lam σ → _root_.Formalism.QuantumDeterminants.IsHCParam lam := by
  intro n H _ _ ε lam σ hlam hds
  unfold _root_.Formalism.MainNotions.S.IsDS at hds
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hds
  unfold _root_.Formalism.MainNotions.S.IsKTypeOf at hS
  obtain ⟨-, -, -, ⟨v, -, hv0, hv⟩, -⟩ := hS
  unfold _root_.Formalism.QuantumDeterminants.IsHCParam
  refine ⟨hlam, fun a => ?_⟩
  obtain ⟨k, hk⟩ := exists_int_eq_weight_of_isWtOn (one_mem_Kset_divisor ε) hv0 hv a
  obtain ⟨m, hm⟩ := exists_int_rhoC_sub_rhoN_sub_half ε a
  refine ⟨k + m, ?_⟩
  have hl : _root_.Formalism.QuantumDeterminants.lowK ε lam a = lam a + _root_.Formalism.REAL.rhoN ε a - _root_.Formalism.REAL.rhoC ε a := by
    unfold _root_.Formalism.QuantumDeterminants.lowK; simp
  push_cast
  linarith

end GlobalTheory.DSParam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrAlphaDeterminantProperty
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

section Frame

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

theorem sigma_algebraMap_of_isTheta {σ : Λ →+* O} {f : RL p O Λ →+* O} (hf : IsTheta σ f)
    (c : ℤ_[p]) : σ (algebraMap ℤ_[p] Λ c) = padicToO p O c := by
  have key : ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] (algebraMap ℤ_[p] Λ c)) =
      (algebraMap ℤ_[p] (Ainf p O) c) ⊗ₜ[ℤ_[p]] (1 : Λ) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have h1 := hf 1 (algebraMap ℤ_[p] Λ c)
  rw [key, hf, map_one, map_one, one_mul, mul_one] at h1
  exact h1.symm

theorem exists_poly_of_adjoin (α : Λ) (hα : Algebra.adjoin ℤ_[p] {α} = ⊤) (l : Λ) :
    ∃ g : Polynomial O, ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → σ l = g.eval (σ α) := by
  have hl : l ∈ Algebra.adjoin ℤ_[p] {α} := hα ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hl
  obtain ⟨g, rfl⟩ := (AlgHom.mem_range _).mp hl
  refine ⟨g.map (padicToO p O), fun σ f hf => ?_⟩
  rw [Polynomial.eval_map, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1
  ext c
  exact sigma_algebraMap_of_isTheta hf c

theorem exists_poly_of_elt (α : Λ) (hα : Algebra.adjoin ℤ_[p] {α} = ⊤) (r : RL p O Λ) :
    ∃ P : Polynomial O, ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → f r = P.eval (σ α) := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨0, fun σ f _ => by simp⟩
  | tmul a l =>
    obtain ⟨g, hg⟩ := exists_poly_of_adjoin (O := O) α hα l
    exact ⟨Polynomial.C (WittVector.fontaineTheta O p a) * g, fun σ f hf => by
      rw [hf, hg σ f hf]; simp⟩
  | add x y hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨Q, hQ⟩ := hy
    exact ⟨P + Q, fun σ f hf => by rw [map_add, hP σ f hf, hQ σ f hf, Polynomial.eval_add]⟩

theorem exists_elt_of_poly (hθ : Function.Surjective (WittVector.fontaineTheta O p)) (α : Λ)
    (P : Polynomial O) : ∃ r : RL p O Λ, ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → f r = P.eval (σ α) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨r, hr⟩ := hP
    obtain ⟨s, hs⟩ := hQ
    exact ⟨r + s, fun σ f hf => by rw [map_add, hr σ f hf, hs σ f hf, Polynomial.eval_add]⟩
  | monomial n c =>
    obtain ⟨a, ha⟩ := hθ c
    exact ⟨a ⊗ₜ[ℤ_[p]] (α ^ n), fun σ f hf => by rw [hf, ha, map_pow, Polynomial.eval_monomial]⟩

end Frame

end GlobalTheory.DetInv

namespace GlobalTheory.DetInv

theorem surjective_of_pow_mem_range {C V ι : Type} [Field C] [AddCommGroup V] [Module C V]
    [Finite ι] {N : ℕ} (Φ : V →ₗ[C] (ι → Fin N → C)) (x : ι → C) (hx : Function.Injective x)
    (h : ∀ (i : Fin N) (k : ℕ),
      (fun σ => (Pi.single i (x σ ^ k) : Fin N → C)) ∈ LinearMap.range Φ) :
    Function.Surjective Φ := by
  classical
  haveI := Fintype.ofFinite ι
  have h1 : ∀ (i : Fin N) (c : ι → C),
      (fun σ => (Pi.single i (c σ) : Fin N → C)) ∈ LinearMap.range Φ := by
    intro i c
    set Q := Lagrange.interpolate Finset.univ x c with hQ
    have e : (fun σ => (Pi.single i (c σ) : Fin N → C)) =
        ∑ k ∈ Finset.range (Q.natDegree + 1),
          Q.coeff k • fun σ => (Pi.single i (x σ ^ k) : Fin N → C) := by
      funext σ j
      have hc : c σ = ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * x σ ^ k := by
        rw [← Polynomial.eval_eq_sum_range, hQ,
          Lagrange.eval_interpolate_at_node c hx.injOn (Finset.mem_univ σ)]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs
      · exact hc
      · simp
    rw [e]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (h i k)
  intro y
  have e : y = ∑ i : Fin N, fun σ => (Pi.single i (y σ i) : Fin N → C) := by
    funext σ j
    simp [Finset.sum_apply, Pi.single_apply]
  have : y ∈ LinearMap.range Φ := by
    rw [e]
    exact Submodule.sum_mem _ fun i _ => h1 i _
  exact this

theorem exists_frame_model : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (α : Λ), Algebra.adjoin ℤ_[p] {α} = ⊤ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ D : Datum ε h Λ, ∃ Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C), (∀ l z σ, Φ ((actH D l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ) ∧ ∀ z, (∀ i, z i ∈ (algebraMap O C).range) ↔ ∀ i, ∃ f : Polynomial O, ∀ σ, Φ z σ i = algebraMap O C (f.eval (σ α)) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ α hα N h hh D
  obtain ⟨-, -, -, hθ, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  obtain ⟨-, eM, -, hM, -⟩ := GlobalTheory.T.determinant_frame_comparison p C v O hv ε hε Λ N h hh D
  have hf : ∀ σ : Λ →+* O, ∃ f : RL p O Λ →+* O, IsTheta σ f := fun σ =>
    (theta_tensor_exists p C v O hv ε hε Λ σ).imp fun f hf => hf.1
  choose f hf using hf
  have hπ : ∀ σ : Λ →+* O, ∃ π, IsProj C eM (f σ) π := fun σ =>
    GlobalTheory.T.exists_theta_projection p O C Λ N h σ (f σ) eM (hf σ)
  choose π hπ using hπ
  obtain ⟨hfin, hcard⟩ := GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ
  have hinj : Function.Injective fun σ : Λ →+* O => algebraMap O C (σ α) := by
    intro σ τ hστ
    have h1 : σ α = τ α := hv.hom_inj hστ
    ext l
    obtain ⟨g, hg⟩ := exists_poly_of_adjoin (O := O) α hα l
    rw [hg σ _ (hf σ), hg τ _ (hf τ), h1]
  have hsurj : Function.Surjective (LinearMap.pi π) := by
    refine surjective_of_pow_mem_range _ _ hinj fun i k => ?_
    refine ⟨fun j => algebraMap O C (WittVector.fontaineTheta O p
      (eM (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] (α ^ k))) j)), ?_⟩
    funext σ
    rw [LinearMap.pi_apply, hπ σ]
    funext j
    simp only [Pi.single_apply]
    split_ifs
    · rw [hf σ]; simp
    · simp
  have hrk : Module.finrank C (Fin h → C) = Module.finrank C ((Λ →+* O) → Fin N → C) := by
    haveI := Fintype.ofFinite (Λ →+* O)
    rw [Module.finrank_pi_fintype C (M := fun _ : Λ →+* O => Fin N → C)]
    rw [Nat.card_eq_fintype_card] at hcard
    simp [hcard, hh]
  have hi : Function.Injective (LinearMap.pi π) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).mpr hsurj
  have hb : Function.Bijective (LinearMap.pi π) := ⟨hi, hsurj⟩
  refine ⟨LinearEquiv.ofBijective (LinearMap.pi π) hb, ?_, ?_⟩
  · intro l z σ
    have hmat : IsMat eM eM (D.ρM l)
        (Matrix.diagonal fun _ : Fin N => ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l : RL p O Λ)) := by
      intro w
      rw [← hM l w]
      congr 1
      funext j
      simp [Matrix.mulVec_diagonal]
    have key := GlobalTheory.T.theta_projection_intertwining p O C Λ N h (f σ) eM eM (π σ) (π σ) _ _ (hπ σ) (hπ σ) hmat z
    simp only [LinearEquiv.ofBijective_apply, LinearMap.pi_apply]
    have e1 : (actH D l).map (algebraMap O C) *ᵥ z = redC C (D.ρM l) z := by
      simp only [actH, redC, Matrix.map_map, Matrix.toLin'_apply, RingHom.coe_comp]
    rw [e1, key, Matrix.diagonal_map (map_zero _)]
    funext j
    rw [Matrix.mulVec_diagonal, RingHom.comp_apply, hf σ]
    simp
  · intro z
    simp only [LinearEquiv.ofBijective_apply, LinearMap.pi_apply]
    constructor
    · intro hz i
      choose t ht using hz
      choose a ha using fun j => hθ (t j)
      have e : z = fun j => algebraMap O C (WittVector.fontaineTheta O p (eM (eM.symm a) j)) := by
        funext j
        rw [eM.apply_symm_apply, ha, ht]
      obtain ⟨P, hP⟩ := exists_poly_of_elt α hα (eM.symm a i)
      refine ⟨P, fun σ => ?_⟩
      rw [e, hπ σ, ← hP σ _ (hf σ)]
    · intro hz
      choose P hP using hz
      choose r hr using fun i => exists_elt_of_poly hθ α (P i)
      have e : z = fun j => algebraMap O C (WittVector.fontaineTheta O p (eM r j)) := by
        apply hi
        funext σ
        rw [LinearMap.pi_apply, LinearMap.pi_apply, hπ σ]
        funext i
        rw [hP, hr i σ _ (hf σ)]
      intro j
      rw [e]
      exact ⟨_, rfl⟩

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndLatticeTraceIntegralStatement
section
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.end_lattice_trace_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → Y ∈ endLat Λ → IsIntegral ℤ Y.trace := by
  first | exact @GlobalTheory.LieDisc.trace_integral_main | exact GlobalTheory.LieDisc.trace_integral_main | (intros; apply GlobalTheory.LieDisc.trace_integral_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechAugmentationEquivOfSection
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem cechAug_eqv_of_section : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X : Scheme.{0}) (f : Y ⟶ X) (s : X ⟶ Y),
    s ≫ f = 𝟙 X → Eqv R (cechAug f) F := by
  intro R _ F Y X f s hs
  have hsec : yoneda.map s ≫ yoneda.map f = 𝟙 (yoneda.obj X) := by
    rw [← yoneda.map_comp, hs, yoneda.map_id]
  have hls : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (yoneda.map f) :=
    (GlobalTheory.T.isLocallySurjective_etale_baseChange).2.1 _ _ (yoneda.map f) (yoneda.map s) hsec
  have hq := GlobalTheory.T.quasiIso_chains_cech_of_isLocallySurjective' R (yoneda.obj Y) (yoneda.obj X) (yoneda.map f) hls
  exact ((GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F).2.2.1 _ _ (cechAug f)) hq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivOfLocallyConstantBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem bij_of_subsingleton_pair {A B : Type*} [Subsingleton A] [Subsingleton B] (_b₀ : B) (a₀ : A) (φ : A → B) :
    Function.Bijective φ :=
  ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨a₀, Subsingleton.elim _ _⟩⟩

theorem eqv_of_gen_lc : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (g : Sec F S), Gen F S g →
    ∀ (U V : Scheme.{0}) (s : U ⟶ S) (f : V ⟶ U), AcycF R (sch.obj U) F → AcycF R (sch.obj V) F →
    Function.Bijective (fun φ : LocallyConstant U R ↦ φ.comap f.base.hom) → Eqv R (sch.map f) F := by
  intro R _ F S g hg U V s f hU hV hb n
  obtain ⟨hneg, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero R F
  obtain ⟨eL, -, hE⟩ := GlobalTheory.T.freeRankOne_etaleSheaf_equiv_locallyConstant R F S g hg
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have := hneg (sch.obj U) n hn
    have := hneg (sch.obj V) n hn
    exact bij_of_subsingleton_pair 0 0 _
  · have key : (fun x ↦ pull R (sch.map f) F 0 x) =
        (fun x ↦ e V (eL V (f ≫ s) (LocallyConstant.comap f.base.hom ((eL U s).symm ((e U).symm x))))) := by
      funext x
      conv_lhs => rw [← (e U).apply_symm_apply x, ← (eL U s).apply_symm_apply ((e U).symm x)]
      rw [he, hE]
    change Function.Bijective (fun x ↦ pull R (sch.map f) F 0 x)
    rw [key]
    exact (e V).bijective.comp ((eL V (f ≫ s)).bijective.comp
      (hb.comp ((eL U s).symm.bijective.comp (e U).symm.bijective)))
  · have := hU n hn
    have := hV n hn
    exact bij_of_subsingleton_pair 0 0 _

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExcisionConeMapQuasiIsoStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.excisionConeMap_quasiIso' : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → QuasiIso (excisionConeMap R A A' f) := by
  first | (exact @GlobalTheory.EtC.excisionConeMap_quasiIso) | (exact GlobalTheory.EtC.excisionConeMap_quasiIso) | (intros; apply GlobalTheory.EtC.excisionConeMap_quasiIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndLatticeTraceOneStatement
section
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_end_lattice_trace_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ r → SelfDualLat G Λ → ∃ Z ∈ endLat Λ, Z.trace = 1 := by
  first | exact @GlobalTheory.LieDisc.exists_endLat_trace_eq_one | exact GlobalTheory.LieDisc.exists_endLat_trace_eq_one | (intros; apply GlobalTheory.LieDisc.exists_endLat_trace_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionAdditiveFnPDivGroupStatement
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_additive_fn_pDivGroup : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (b : G.A 1), cobOne R (G.A 1) b = 0 → ∃ B : G.funs, B.1 1 = b ∧ ∀ n, G.transl n (B.1 (n + 1)) = B.1 (n + 1) ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b := by
  first | exact @GlobalTheory.PDivGroup.exists_funs_transl_eq_add | exact GlobalTheory.PDivGroup.exists_funs_transl_eq_add | (intros; apply GlobalTheory.PDivGroup.exists_funs_transl_eq_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusHodgeTateLatticeAinfStatement
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_hodgeTateLattice_ainf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ φ : ∀ G : PDivGroup p O, latt G →ₛₗ[(WittVector.frobenius : Ainf p O →+* Ainf p O)] latt G, (∀ G y t, (φ G y).1 t = WittVector.frobenius (y.1 t)) ∧ ∀ G m, ∃ n, φ G n = (WittVector.frobenius (xi ε) : Ainf p O) • m := by
  first | exact @GlobalTheory.PDivLat.exists_frobenius_latt | exact GlobalTheory.PDivLat.exists_frobenius_latt | (intros; apply GlobalTheory.PDivLat.exists_frobenius_latt <;> assumption)
end

