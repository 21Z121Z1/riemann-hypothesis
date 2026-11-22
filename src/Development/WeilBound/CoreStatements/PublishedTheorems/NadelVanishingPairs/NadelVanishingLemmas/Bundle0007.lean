import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0984
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsDerivationNonPthPower

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ChartFormsDifferentialClosed
section
open GlobalTheory GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.chart_forms_differential_closed : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ), AlgChart A x → ∀ q, ∀ η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) q, extD K η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) (q + 1) := by
  first | exact @_root_.GlobalTheory.LogDR.extD_mem_chartForms_twist | exact _root_.GlobalTheory.LogDR.extD_mem_chartForms_twist | (intros; apply _root_.GlobalTheory.LogDR.extD_mem_chartForms_twist <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EulerContractionChartForms
section
open GlobalTheory GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.euler_contraction_chart_forms : ∀ (K : Type) [Field K] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K), (∀ j, (x j : K) ∈ A) → IsEulerContraction x i θ → (∀ q, ∀ η ∈ chartForms A x J t (q + 1), θ η ∈ chartForms A x J t q) ∧ ∀ η ∈ chartForms A x J t 0, θ η = 0 := by
  first | exact @_root_.GlobalTheory.LogDR.chartForms_stable_euler | exact _root_.GlobalTheory.LogDR.chartForms_stable_euler | (intros; apply _root_.GlobalTheory.LogDR.chartForms_stable_euler <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KernelDifferentialPthPower
section
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem dK_eq_zero_imp_pow : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (f : K),
    dK f = 0 → ∃ g : K, f = g ^ p := by
  intro K _ p _ _ f hf
  by_contra hne
  push_neg at hne
  obtain ⟨D, hD⟩ := DerivExt.exists_derivation p f hne
  have h := D.liftKaehlerDifferential_comp_D f
  have h0 : (KaehlerDifferential.D ℤ K) f = 0 := hf
  rw [h0, map_zero, hD] at h
  exact zero_ne_one h

end GlobalTheory
end

