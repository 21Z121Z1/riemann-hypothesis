import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0836
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0022
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsFanLowerMaxMultiplicityStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.exists_fan_lower_max_multiplicity : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → maxMult bar q φ < ⊤ → 2 ≤ maxMult bar q φ → ∃ φ' lab' : InvFun O, IsPolyFan bar q φ' ∧ IsTwG w0 φ' ∧ IsTwG w0 lab' ∧ SimpLab bar q φ' lab' ∧ Subordinate bar q φ' φ ∧ maxMult bar q φ' < maxMult bar q φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.RoundBelowMaxMultiplicity.exists_round_lt_maxMult | exact GlobalTheory.CompanionTheory.Ar.Fan.RoundBelowMaxMultiplicity.exists_round_lt_maxMult | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.RoundBelowMaxMultiplicity.exists_round_lt_maxMult <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSimplicialLabelledRefinementStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.exists_simplicial_labelled_refinement : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → ∃ φ lab : InvFun O, IsPolyFan bar q φ ∧ IsTwG w0 φ ∧ IsTwG w0 lab ∧ SimpLab bar q φ lab ∧ Subordinate bar q φ ψ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.SimplicialLabelRefinement.exists_simpLab_refinement | exact GlobalTheory.CompanionTheory.Ar.Fan.SimplicialLabelRefinement.exists_simpLab_refinement | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.SimplicialLabelRefinement.exists_simpLab_refinement <;> assumption)
end

