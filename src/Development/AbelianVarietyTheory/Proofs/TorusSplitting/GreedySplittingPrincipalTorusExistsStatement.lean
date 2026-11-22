import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0001
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.GlobalTheory.T.greedy_splitting_principal_torus_exists : SplitStatement := by
  first | exact @GlobalTheory.greedy_splitting_exists | exact GlobalTheory.greedy_splitting_exists | (intros; apply GlobalTheory.greedy_splitting_exists <;> assumption)
