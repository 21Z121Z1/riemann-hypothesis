import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0072
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0071

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommutingLocallyNilpotentCommonKernelStatement
section
open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_locally_nilpotent_common_kernel : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (I : Submodule ℂ V), I ≠ ⊥ → ∀ (D : ℂ → Module.End ℂ V), (∀ Y Y', Commute (D Y) (D Y')) → (∀ Y, ∀ x ∈ I, D Y x ∈ I) → (∀ Y, ∀ x ∈ I, ∃ N : ℕ, (D Y ^ N) x = 0) → ∀ (l : ℕ) (c : ℕ → Module.End ℂ V), (∀ Y, D Y = ∑ j ∈ Finset.range l, Y ^ j • c j) → ∃ w ∈ I, w ≠ 0 ∧ ∀ Y, D Y w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.exists_joint_kernel_polynomial_family | exact GlobalTheory.CompanionTheory.RgTransport.exists_joint_kernel_polynomial_family | (intros; apply GlobalTheory.CompanionTheory.RgTransport.exists_joint_kernel_polynomial_family <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviSubspaceInvariantUnderBlocksStatement
section
open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_subspace_invariant_under_blocks : ∀ {n : ℕ} (P : GMod n) (d : Fin 3 → ℕ) (h : ∑ i, d i = n) (χ : Fin n → ℂ) (L : Fin n → Fin 3) (a b : Fin n), blk (stdBlocks d h) a = blk (stdBlocks d h) b → ∀ x ∈ leviSub P d h χ L, P.E a b x ∈ leviSub P d h χ L := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.leviSub_stable | exact GlobalTheory.CompanionTheory.RgTransport.leviSub_stable | (intros; apply GlobalTheory.CompanionTheory.RgTransport.leviSub_stable <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantAntiHomomorphismStatement
section
open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_determinant_anti_homomorphism : ∀ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₗ[ℂ] B), f 1 = 1 → (∀ x y, f (x * y) = f y * f x) → ∀ {m : ℕ} (E : Fin m → Fin m → A), GlRel E → ∀ u : ℂ, qdet (fun a b => f (E b a)) u = f (qdet E u) := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.qdet_anti | exact GlobalTheory.CompanionTheory.RgTransport.qdet_anti | (intros; apply GlobalTheory.CompanionTheory.RgTransport.qdet_anti <;> assumption)
end

