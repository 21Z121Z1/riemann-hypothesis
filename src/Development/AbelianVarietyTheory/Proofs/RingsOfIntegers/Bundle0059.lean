import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0058
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStableStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.integralFramedPoint_baseChange_stable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), PullbackSections.IntFrBCSt Xo c := by
  first | exact @GlobalTheory.IntFrBaseChange.exists_intFr_baseChange | exact GlobalTheory.IntFrBaseChange.exists_intFr_baseChange | (intros; apply GlobalTheory.IntFrBaseChange.exists_intFr_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGeneratorPlaceValuationBoundStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGenerator_place_valuation_bound : ThBoundSt := by
  first | exact @GlobalTheory.ThetaBound.thBound | exact GlobalTheory.ThetaBound.thBound | (intros; apply GlobalTheory.ThetaBound.thBound <;> assumption)
end

