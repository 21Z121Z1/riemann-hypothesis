import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagComparisonTheorem
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0061
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0055

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagComparisonTheoremStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_comparison_theorem : GlobalTheory.CompanionTheory.Ar.GR.FlagStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.flagStatement_holds | exact GlobalTheory.CompanionTheory.Ar.GR.flagStatement_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.flagStatement_holds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanInputNefAmpleSectionCountStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kleiman_input_nef_ample_section_count : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0} → NefProductNonneg.Statement ∧ VeryAmpleNefPlusAmple.Statement ∧ SectionCount.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Relay.kleiman_input_nef_ample_section_count | exact GlobalTheory.CompanionTheory.Relay.kleiman_input_nef_ample_section_count | (intros; apply GlobalTheory.CompanionTheory.Relay.kleiman_input_nef_ample_section_count <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientOfAffineChartCoverStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_of_affine_chart_cover : ∀ {P X : Scheme.{0}} (a b : P ⟶ X), (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ HasAffineChart a b V) → ∃ (Y : Scheme.{0}) (q : X ⟶ Y), IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧ IsPullback a b q q := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.exists_of_affineCharts | exact GlobalTheory.CompanionTheory.FreeQuotGlue.exists_of_affineCharts | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.exists_of_affineCharts <;> assumption)
end

