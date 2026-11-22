import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement

namespace ReciprocityTheory.ChartRestriction.G.Geo

theorem poincareLelong_of_resolution (hE : ResExistsStatement) (hB : ResBridgeStatement)
    (hPL : ReciprocityTheory.AnForm.M.PoincareLelongStatement) (hPush : ResDivPushStatement) : ArithmeticPoincareLelongFormula :=
  poincareLelong_of_resolution_atlas hE hB hPL ReciprocityTheory.AnForm.M.sncInducedAtlas hPush

theorem stokes_of_resolution (hE : ResExistsStatement) (hB : ResBridgeStatement) : StokesStatement :=
  stokes_of'' hE hB ReciprocityTheory.AnForm.M.byPartsSymm

theorem poincareLelong_of_resolution_pushforward (hE : ResExistsStatement) (hB : ResBridgeStatement) (hPush : ResDivPushStatement) :
    ArithmeticPoincareLelongFormula :=
  poincareLelong_of_resolution hE hB ReciprocityTheory.AnForm.M.poincareLelong hPush

end ReciprocityTheory.ChartRestriction.G.Geo
