import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoTheta
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NormSSqFrameOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetOfThickPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
import Development.WeilBound.CoreStatements.ArcCellEmbeddings.TraceVolumeDimensionStandard
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0059
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0049
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SumExtendByZeroLeSum
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0079
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.WeightEqZeroOfOneIsSec
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Indef.Tree Formalism.IndefR.Obj
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem PositivityTheory.Xgn.farguesHodgeTate_of_farguesExact : HT.FarguesExact → HT.FarguesHodgeTate := by
  intro hE p _ C _ _ _ v O _ _ _ hv hp hc G
  refine ⟨fun κ hκ w => HT.hodge_tate_cokernel_sharp p C v O hv hp hc G κ ?_ w, hE p C v O hv hp hc G⟩
  split_ifs at hκ with h2
  · subst h2
    have h4 : (4 : C) = ((2 : ℕ) : C) * ((2 : ℕ) : C) := by norm_num
    rw [h4, map_mul] at hκ
    have h1 : (2 - 1 : ℕ) = 1 := rfl
    rw [h1, pow_one]
    exact hκ.trans (mul_le_of_le_one_left' hp.le)
  · exact hκ
