import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.HermitianCharacters.SelfDualLatticeFiltrationCharacter
import Formalism.UnipotentAdelicQuotients.Bundle0003
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Development.AutomorphicSpectrum.Proofs.HermitianForms.IndicatorInSchrodingerSpan
import Formalism.UnipotentAdelicQuotients.SWXSDefs

-- bundled from Development.AutomorphicSpectrum.Proofs.HermitianForms.AdelicCharacterLocalNontrivial
section
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_character_local_nontrivial : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ v : HeightOneSpectrum (𝓞 F), Continuous (psiV F ψ v) ∧ ∃ y, psiV F ψ v y ≠ 1) ∧ Continuous (psiInf F ψ) ∧ ∀ (w : InfinitePlace F), ∃ x : Ainf F, (∀ w', w' ≠ w → x w' = 0) ∧ psiInf F ψ x ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place | exact GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place | (intros; apply GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.HermitianForms.IndicatorInSchrodingerSpanStatement
section
open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_filtration_character : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (χ : V → V → ℂ) (L : ℤ → AddSubgroup V) (D : ℤ → AddSubgroup V), (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → (∀ x y, χ x y = χ y x) → (∀ x y, ‖χ x y‖ = 1) → Continuous (fun p : V × V => χ p.1 p.2) → (∀ n, IsOpen (L n : Set V) ∧ IsCompact (L n : Set V) ∧ IsOpen (D n : Set V) ∧ IsCompact (D n : Set V)) → Antitone L → (∀ U ∈ nhds (0 : V), ∃ n, (L n : Set V) ⊆ U) → (∀ x, ∃ n, x ∈ L n) → (∀ x, ∃ n, x ∈ D n) → (∀ n y, y ∈ D n ↔ ∀ x ∈ L n, χ x y = 1) → (∀ n x, x ∈ L n ↔ ∀ y ∈ D n, χ x y = 1) → ∃ μ : Measure V, SelfDual μ χ := by
  first | exact @GlobalTheory.CompanionTheory.SDPadic.exists_selfDual | exact GlobalTheory.CompanionTheory.SDPadic.exists_selfDual | (intros; apply GlobalTheory.CompanionTheory.SDPadic.exists_selfDual <;> assumption)
end

