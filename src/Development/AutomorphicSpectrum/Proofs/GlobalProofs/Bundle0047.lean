import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0177
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.WeilBound.CoreStatements.ProjectiveValuations.CompactSpaceComplexPointsOfProper
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DiscreteSeriesUpqUnique
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesLowestKTypeOfClassification
import Development.AutomorphicSpectrum.Proofs.SemilocalMultiplicity.LowKMultOneP
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CompactSpaceCxPtsOfIsProper
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

theorem compactSpace_cxPts_of_isProper :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProper p → CompactSpace (CxPts p (RingHom.id ℂ)) :=
  DifferentiableLines.compactSpace_complex_points_of_proper

end GlobalTheory.CompanionTheory.Gaga
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DiscreteSeriesHermitianUnique
section
namespace GlobalTheory.CompanionTheory.Front

theorem discreteSeriesHermitianUnique : GlobalTheory.Published.DiscreteSeriesHermitianUnique :=
  GlobalTheory.Published.discreteSeriesHermitianUnique_iff.2 discreteSeriesUpqUnique

end GlobalTheory.CompanionTheory.Front
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DiscreteSeriesLowestKType
section
namespace GlobalTheory.CompanionTheory.Glob

theorem discreteSeriesLowestKType : GlobalTheory.Published.DiscreteSeriesLowestKType :=
  GlobalTheory.Published.discreteSeriesLowestKType_iff.2
    ⟨GlobalTheory.CompanionTheory.TypeCount.LowK.lowKMultOne, GlobalTheory.CompanionTheory.Front.discreteSeriesUpqUnique⟩

end GlobalTheory.CompanionTheory.Glob
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HolomorphicGluingLocalFunctionsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_gluing_local_functions : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D s → ∀ (R : AnRead s (RingHom.id ℂ) D), ∀ (L : LB X), L.IsLB → ∀ h : L.ι → (Sp ℂ ⟶ X) → ℂ, (∀ (i : L.ι) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s = 𝟙 _ ∧ ⊤ ≤ y b ⁻¹ᵁ L.U i) → DifferentiableOn ℂ (fun b => h i (y b)) B) → (∀ (i j : L.ι) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) → h i x = valAt' x (L.U i ⊓ L.U j) (L.g i j).val * h j x) → ∃ σ ∈ R.holSec L, ∀ (i : L.ι), ∀ y ∈ ptsIn s (RingHom.id ℂ) (L.U i), σ i y = h i y.1 := by
  first | exact @GlobalTheory.CompanionTheory.Gaga.exists_mem_holSec | exact GlobalTheory.CompanionTheory.Gaga.exists_mem_holSec | (intros; apply GlobalTheory.CompanionTheory.Gaga.exists_mem_holSec <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RegularFunctionPolynomialGrowthStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_function_polynomial_growth : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsSeparated p → LocallyOfFiniteType p → ∀ (V : Y.Opens), IsAffineOpen V → ∃ (n : ℕ) (u : Fin n → Γ(Y, V)), ∀ (W : Y.Opens), IsAffineOpen W → ∀ g : Γ(Y, V ⊓ W), ∃ (r m : ℕ) (w : Fin r → Γ(Y, W)), ∀ y ∈ ptsIn p (RingHom.id ℂ) (V ⊓ W), ‖ev p (RingHom.id ℂ) (V ⊓ W) g y‖ ≤ (∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := by
  first | exact @GlobalTheory.CompanionTheory.Gaga.exists_gens_bound | exact GlobalTheory.CompanionTheory.Gaga.exists_gens_bound | (intros; apply GlobalTheory.CompanionTheory.Gaga.exists_gens_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothSchemeDecomposeRelativeDimensionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_scheme_decompose_relative_dimension : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ), Smooth s → ∃ W : ℕ → X.Opens, (∀ D, IsClosed (W D : Set X)) ∧ (∀ D, SmoothOfRelativeDimension D ((W D).ι ≫ s)) ∧ (⨆ D, W D) = ⊤ ∧ Pairwise fun D D' => W D ⊓ W D' = ⊥ := by
  first | exact @GlobalTheory.CompanionTheory.Gaga.exists_clopen_smoothOfRelativeDimension | exact GlobalTheory.CompanionTheory.Gaga.exists_clopen_smoothOfRelativeDimension | (intros; apply GlobalTheory.CompanionTheory.Gaga.exists_clopen_smoothOfRelativeDimension <;> assumption)
end

