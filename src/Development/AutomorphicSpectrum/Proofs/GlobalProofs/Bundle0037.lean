import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CohomologicalDimensionTopologicalIso
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsDiscreteRepResMuROrep
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermFrameKTypeCoefficients

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CohomologicalDimensionTopologicalIsoStatement
section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global FiniteSubfield ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.CompanionTheory.GSCd GroundTheory.Global.IdeleGroup GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_unramified_outside_descends_finite : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → ∃ (K : FiniteSubfield) (S' : Finset (HeightOneSpectrum (𝓞 K.1))), ContainsAbove S' l ∧ Nonempty (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ* Gs K S') := by
  first | exact @GlobalTheory.CompanionTheory.GSCd.Transport.exists_gs_transport | exact GlobalTheory.CompanionTheory.GSCd.Transport.exists_gs_transport | (intros; apply GlobalTheory.CompanionTheory.GSCd.Transport.exists_gs_transport <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConstantTermFrameKTypeCoefficientsStatement
section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global FiniteSubfield ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.CompanionTheory.GSCd GroundTheory.Global.IdeleGroup GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomological_dimension_topological_iso : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (p : ℕ), (G ≃ₜ* H) → cdp p G = cdp p H := by
  first | exact @GlobalTheory.CompanionTheory.GSCd.cdp_eq_of_continuousMulEquiv | exact GlobalTheory.CompanionTheory.GSCd.cdp_eq_of_continuousMulEquiv | (intros; apply GlobalTheory.CompanionTheory.GSCd.cdp_eq_of_continuousMulEquiv <;> assumption)
end

