import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsUnitaryMoveHermitianHalfSpaceHigh
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0020
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivPairingEqZeroOfIsHeat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsUnitaryMoveHermitianHalfSpaceHighStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_move_hermitianHalfSpace_high : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N : ℕ, ∃ (c : ℕ) (δ : ℝ), 0 < c ∧ 0 < δ ∧ ∀ Z ∈ Hn Ψ N, ∃ γ ∈ UU E N, Den c γ ∧ hAct Ψ γ Z ∈ HnGe Ψ N δ := by
  first | exact @GlobalTheory.SW.exists_move_high | exact GlobalTheory.SW.exists_move_high | (intros; apply GlobalTheory.SW.exists_move_high <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionUnitaryGroupTestFunctionsStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ γ ∈ UU E N, ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsSB (weil Ψ γ φ) ∧ TransH Ψ γ φ (weil Ψ γ φ) ∧ (∀ ψ, IsSB ψ → TransH Ψ γ φ ψ → ψ = weil Ψ γ φ) ∧ (∀ ψ, IsSB ψ → ip (weil Ψ γ φ) (weil Ψ γ ψ) = ip φ ψ ∧ weil Ψ γ (φ + ψ) = weil Ψ γ φ + weil Ψ γ ψ) ∧ (∀ c : ℂ, weil Ψ γ (c • φ) = c • weil Ψ γ φ) ∧ (∀ γ' ∈ UU E N, weil Ψ (γ' * γ) φ = weil Ψ γ' (weil Ψ γ φ)) ∧ weil Ψ 1 φ = φ := by
  first | exact @GlobalTheory.SW.weil_action | exact GlobalTheory.SW.weil_action | (intros; apply GlobalTheory.SW.weil_action <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivPairingEqZeroOfIsHeatStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyDeriv_aeval_pairings_eq_zero_of_isHeat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ) (D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ), IsHeat Ψ D → (∀ Z ∈ Hn Ψ N, D Z 0 0 = 0) → ∀ Z ∈ Hn Ψ N, ∀ s : MvPolynomial (Ψ × Fin N × Fin N) ℂ, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.aeval (fun v : Ψ × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (Ψ × Bool × Fin n × Fin N) ℂ)) s) (fun v => (Pi.single v 1 : Ψ × Bool × Fin n × Fin N → ℂ)) (fun w : Ψ × Bool × Fin n × Fin N → ℂ => D Z (fun τ => Matrix.of fun k a => w (τ, false, k, a)) (fun τ => Matrix.of fun k a => w (τ, true, k, a))) 0 = 0 := by
  first | exact @GlobalTheory.SW.polyDeriv_pairing_eq_zero_of_isHeat | exact GlobalTheory.SW.polyDeriv_pairing_eq_zero_of_isHeat | (intros; apply GlobalTheory.SW.polyDeriv_pairing_eq_zero_of_isHeat <;> assumption)
end

