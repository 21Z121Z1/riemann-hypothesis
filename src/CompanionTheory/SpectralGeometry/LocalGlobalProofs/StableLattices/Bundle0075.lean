import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0074
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0071
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0073

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantBlockEigenvalueStatement
section
open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_determinant_block_eigenvalue : ∀ {n : ℕ} (Q : GMod n) (d : Fin 3 → ℕ) (h : ∑ i, d i = n) (w : Q.V), (∀ a b, blk (stdBlocks d h) b < blk (stdBlocks d h) a → Q.E a b w = 0) → ∀ c : Fin 3 → ℂ → ℂ, (∀ i Y, Qd Q d h i Y w = c i Y • w) → ∀ Y : ℂ, qdet Q.E (Y + ((n : ℂ) - 1) / 2) w = (∏ i, c i Y) • w := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.qdet_eigen_of_killed | exact GlobalTheory.CompanionTheory.RgTransport.qdet_eigen_of_killed | (intros; apply GlobalTheory.CompanionTheory.RgTransport.qdet_eigen_of_killed <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorQuotientQuantumDeterminantEigenStatement
section
open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_quotient_quantum_determinant_eigen : StepChar → TensDecomp → ∀ {m : ℕ} (M : GMod m) (χ : Fin m → ℂ), HasChar M χ → ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin m → Fin m → Module.End ℂ V), GlRel E → ∀ Φ : (Fin m → M.V) →ₗ[ℂ] V, (∀ a b u, Φ (tensE M a b u) = E a b (Φ u)) → Φ ≠ 0 → ∃ r, ∃ w ∈ LinearMap.range Φ, w ≠ 0 ∧ ∀ Y : ℂ, qdet E (Y + ((m : ℂ) - 1) / 2) w = Formalism.QuantumDeterminants.capP (χ + Pi.single r 1) Y • w := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.Raise.exists_raised | exact GlobalTheory.CompanionTheory.RgTransport.Raise.exists_raised | (intros; apply GlobalTheory.CompanionTheory.RgTransport.Raise.exists_raised <;> assumption)
end

