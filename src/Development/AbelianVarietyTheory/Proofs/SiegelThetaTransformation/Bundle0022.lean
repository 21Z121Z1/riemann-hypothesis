import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EmbeddingCompatibleWithWeilAndDenominator
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianHeisenbergOperatorLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionCommPositiveUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionSiegelParabolicExplicit

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EmbeddingCompatibleWithWeilAndDenominatorStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_compatible_with_weil_and_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∃ ι : M2 E N → M2 E (N + 1), (∀ γ ∈ UU E N, ι γ ∈ UU E (N + 1) ∧ (∀ a, (ι γ).toBlocks₂₁ a 0 = 0) ∧ (∀ (Z : CM Ψ (N + 1) (N + 1)) τ, (hDen Ψ (ι γ) Z τ).det = (hDen Ψ γ (dropZ Ψ Z) τ).det) ∧ (∀ φ : Matrix (Fin n) (Fin (N + 1)) E → ℂ, IsSB φ → dropF (weil Ψ (ι γ) φ) = weil Ψ γ (dropF φ)) ∧ ∀ γ' ∈ UU E N, (botSpan (ι γ) = botSpan (ι γ') ↔ botSpan γ = botSpan γ')) ∧ ∀ g ∈ UU E (N + 1), (∀ a, g.toBlocks₂₁ a 0 = 0) → ∃ γ ∈ UU E N, botSpan g = botSpan (ι γ) := by
  first | exact @GlobalTheory.SW.Emb.exists_embedding | exact GlobalTheory.SW.Emb.exists_embedding | (intros; apply GlobalTheory.SW.Emb.exists_embedding <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianHeisenbergOperatorLawsStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianHeisenbergOperator_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ (d b : Matrix (Fin n) (Fin N) E) (φ : Matrix (Fin n) (Fin N) E → ℂ), IsSB φ → IsSB (heisH d b φ) ∧ (∀ Z ∈ Hn Ψ N, ∀ z z' : CM Ψ n N, thH Ψ (heisH d b φ) Z z z' = cexp (2 * π * I * expo Ψ d Z z z' + π * I * ((Algebra.trace ℚ E (∑ k, ∑ a, b k a * cc (d k a)) : ℚ) : ℂ)) * thH Ψ φ Z (fun τ => z τ + (b.map τ.1).map conj + (d.map τ.1).map conj * (Z τ)ᵀ) (fun τ => z' τ + b.map τ.1 + d.map τ.1 * Z τ)) ∧ ∀ γ ∈ UU E N, weil Ψ γ (heisH d b φ) = heisH (Matrix.fromCols d b * γ⁻¹).toCols₁ (Matrix.fromCols d b * γ⁻¹).toCols₂ (weil Ψ γ φ) := by
  first | exact @GlobalTheory.SW.heisH_laws | exact GlobalTheory.SW.heisH_laws | (intros; apply GlobalTheory.SW.heisH_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionCommPositiveUnitaryGroupStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianWeilAction_comm_positiveUnitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsSB (fun x : Matrix (Fin n) (Fin N) E => φ (h * x)) ∧ (∀ γ ∈ UU E N, weil Ψ γ (fun x => φ (h * x)) = fun x => weil Ψ γ φ (h * x)) ∧ ∀ Z ∈ Hn Ψ N, thH Ψ (fun x => φ (h * x)) Z 0 0 = thH Ψ φ Z 0 0 ∧ eis Ψ (fun x => φ (h * x)) Z 0 0 = eis Ψ φ Z 0 0 := by
  first | exact @GlobalTheory.SW.weil_comp_unitary | exact GlobalTheory.SW.weil_comp_unitary | (intros; apply GlobalTheory.SW.weil_comp_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionSiegelParabolicExplicitStatement
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianWeilAction_siegelParabolic_explicit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → (∀ γ ∈ UU E N, γ.toBlocks₂₁ = 0 → ∀ x, weil Ψ γ φ x = (∏ τ : Ψ, τ.1 γ.toBlocks₂₂.det ^ n) * chiH Ψ (-(γ.toBlocks₁₂ * ccT γ.toBlocks₁₁)) x * φ (x * γ.toBlocks₁₁)) ∧ ∀ γ ∈ UU E N, ∀ γ' ∈ UU E N, botSpan γ = botSpan γ' → ∀ Z ∈ Hn Ψ N, ∀ z z', eisTerm Ψ γ φ Z z z' = eisTerm Ψ γ' φ Z z z' := by
  first | exact @GlobalTheory.SW.weil_parabolic | exact GlobalTheory.SW.weil_parabolic | (intros; apply GlobalTheory.SW.weil_parabolic <;> assumption)
end

