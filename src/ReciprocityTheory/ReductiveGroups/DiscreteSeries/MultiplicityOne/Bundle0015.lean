import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0014
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0005
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeHerm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0012
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0009
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0006
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0003
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0008
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0007
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSmooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvCC
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0010
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0013
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JRankOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.ThmMOfXi
section
namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem thmM_of_xi (h : UnitaryGroupStructuralFacts) (hXi : Formalism.FourierDecayAlt.B.XiExists) : ThmM :=
  theoremM_of h hXi (stBeHerm h) (stBePos h) (stSchurW h) (stSInt h) stSchurG (stPairs h) (stBeConv h) (stBeEquiv h)
    (stRepro h) (stSmooth h) stFrame (stInvGroup h) stInvChar stInvCC (stReps h) (stTransM h) (stSym h) (stSymBeta h)
    (stBetaInf h) (stDichoG h) (stDichoW h) (stMixed h) rankOneMinors

theorem thmM : ThmM := thmM_of_xi multiplicity_one_hypotheses_hold ReciprocityTheory.ChartRestriction.DS.Xi.xiExists

end ReciprocityTheory.ChartRestriction.DS.Mult1
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.TranslateIntegrable
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv ReciprocityTheory.ChartRestriction.DS.Mult1.Fold

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def ph (X : SigData k r) (d : ℝ) (y : Mat k r) : ℂ := (d : ℂ) * star (mc X X.w X.w y)

def tst (X : SigData k r) (B : X.Hs →ₗ[ℂ] Wp) (η : Mat k r → Wp) (v : X.Hs) (g : Mt k r) : ℂ :=
  (wr g : ℂ) * ⟪η (Matrix.of g), B (X.σ (Matrix.of g) v)⟫_ℂ

end ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit
end
end

