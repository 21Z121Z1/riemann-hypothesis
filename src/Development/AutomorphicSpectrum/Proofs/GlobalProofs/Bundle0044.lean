import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0021
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLengthStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0014
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalFiniteness.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
section
namespace GlobalTheory.CompanionTheory.Published

theorem bernsteinZelevinskyFiniteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness :=
  fun k _ _ _ _ => ⟨GlobalTheory.T.irreducible_smooth_admissible_GL k, GlobalTheory.T.jacquet_module_finite_length k, GlobalTheory.T.parabolic_induction_finite_length k, GlobalTheory.T.parabolic_induction_contragredient k⟩

end GlobalTheory.CompanionTheory.Published
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CohomologicalDimensionTwoUnramified
section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
theorem _root_.GlobalTheory.T.cohomological_dimension_two_unramified : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → l ≠ 2 → ∀ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))))) [IsDiscreteRep A], Finite A.V → (∀ a : A.V, (l ^ r) • a = 0) → ∀ n : ℕ, 3 ≤ n → Subsingleton (cohomology A n) :=
  @PositivityTheory.Lit1.GFParts.subsingleton_hn
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteH2UnramifiedOutside
section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
theorem _root_.GlobalTheory.T.finite_H2_unramified_outside : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → ∀ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))))) [IsDiscreteRep A], Finite A.V → (∀ a : A.V, (l ^ r) • a = 0) → Finite (cohomology A 2) :=
  @PositivityTheory.Lit1.GFParts.finite_H2_torsion_module
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.Imports
section
namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity :=
  CompanionTheory.FamInh.globalArtin

end GlobalTheory.CompanionTheory.Hypotheses₂
end

