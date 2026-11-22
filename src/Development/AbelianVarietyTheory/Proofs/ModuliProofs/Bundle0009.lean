import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCocyclePeriodicNonvanishingSections
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardAlgHomReducedTraceSum
section
open scoped TensorProduct

namespace GlobalTheory

theorem finite_card_trace_algHom_of_isReduced_baseChange :
    ∀ (O H K : Type) [CommRing O] [Nontrivial O] [CommRing H] [Algebra O H] [Module.Free O H]
      [Module.Finite O H] [Field K] [IsAlgClosed K] [Algebra O K], IsReduced (K ⊗[O] H) →
      Finite (H →ₐ[O] K) ∧ Nat.card (H →ₐ[O] K) = Module.finrank O H ∧
        ∀ h : H, algebraMap O K (Algebra.trace O H h) = ∑ᶠ ga : H →ₐ[O] K, ga h := by
  intro O H K _ _ _ _ _ _ _ _ _ hred
  have : IsReduced (K ⊗[O] H) := hred
  have hcard : Nat.card (H →ₐ[O] K) = Module.finrank O H :=
    natCard_algHom_eq_finrank_of_isReduced_baseChange O H K
  have hfin : Finite (H →ₐ[O] K) := by
    by_cases h0 : Module.finrank O H = 0
    · have : IsEmpty (H →ₐ[O] K) := by
        refine ⟨fun f => ?_⟩
        have hι : IsEmpty (Module.Free.ChooseBasisIndex O H) := by
          rw [← Fintype.card_eq_zero_iff, ← Module.finrank_eq_card_chooseBasisIndex]
          exact h0
        have h10 : (1 : H) = 0 :=
          (Module.Free.chooseBasis O H).repr.injective (Subsingleton.elim _ _)
        have h1 := congrArg f h10
        rw [map_one, map_zero] at h1
        exact one_ne_zero h1
      infer_instance
    · exact Nat.finite_of_card_ne_zero (hcard ▸ h0)
  refine ⟨hfin, hcard, fun h => ?_⟩
  let _ := Fintype.ofFinite (H →ₐ[O] K)
  rw [finsum_eq_sum_of_fintype]
  exact algebraMap_trace_eq_sum_algHom_of_card (R := O) (S := H) (L := K)
    (by rw [← Nat.card_eq_fintype_card, hcard]) (P := fun g => g) (fun _ _ e => e) h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCocyclePeriodicNonvanishingSectionsStatement
section
open Complex Matrix
open scoped ContDiff BigOperators Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_cocycle_periodic_nonvanishing_sections : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm Θ : Matrix (Fin g) (Fin g) ℂ) (ι : Type) (U : ι → Set (Fin g → ℂ)) (a : ι → (Fin g → ℂ) → ℂ) (k : ι → ι → (Fin g → ℂ) → ℂ) (e : Λ → ℂ), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → (∀ i, DifferentiableOn ℂ (a i) (U i) ∧ ∀ z ∈ U i, a i z ≠ 0) → (∀ i (l : Λ), ∀ z ∈ U i, a i z = e l * cexp (π * (z ⬝ᵥ Hm.mulVec (star (l : (Fin g → ℂ))))) * a i (z + l)) → (∀ i j, DifferentiableOn ℂ (k i j) (U i ∩ U j)) → (∀ i j m, ∀ z ∈ U i ∩ U j ∩ U m, k i j z + k j m z = k i m z) → (∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, k i j (z + l) = k i j z + (fderiv ℂ (a i) z (Θ.mulVec (star (l : (Fin g → ℂ)))) / a i z - fderiv ℂ (a j) z (Θ.mulVec (star (l : (Fin g → ℂ)))) / a j z)) → ∀ z w, Θ.mulVec (star z) ⬝ᵥ Hm.mulVec (star w) = Θ.mulVec (star w) ⬝ᵥ Hm.mulVec (star z) := by
  first | exact @GlobalTheory.PeriodSymm.period_symm | exact GlobalTheory.PeriodSymm.period_symm | (intros; apply GlobalTheory.PeriodSymm.period_symm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorusEllipticSystemSolvableStatement
section
open Complex Matrix
open scoped ContDiff BigOperators Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodic_smooth_solution_torus_system : ∀ (n m : ℕ) (p : Fin m → Fin n → ℂ), (∀ ξ : Fin n → ℝ, (∀ a, ∑ k, p a k * (ξ k : ℂ) = 0) → ξ = 0) → ∀ w : Fin m → (Fin n → ℝ) → ℂ, (∀ a, ContDiff ℝ ∞ (w a) ∧ (∀ (ν : Fin n → ℤ) x, w a (x + fun k => (ν k : ℝ)) = w a x)) → (∀ a b x, ∑ k, p a k * fderiv ℝ (w b) x (Pi.single k 1) = ∑ k, p b k * fderiv ℝ (w a) x (Pi.single k 1)) → ∃ (t : Fin m → ℂ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ f ∧ (∀ (ν : Fin n → ℤ) x, f (x + fun k => (ν k : ℝ)) = f x) ∧ ∀ a x, ∑ k, p a k * fderiv ℝ f x (Pi.single k 1) = w a x - t a := by
  first | exact @GlobalTheory.torus_elliptic_system_solvable | exact GlobalTheory.torus_elliptic_system_solvable | (intros; apply GlobalTheory.torus_elliptic_system_solvable <;> assumption)
end

