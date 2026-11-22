import Formalism.PadicSubsetSums.CentralIdempotents.GL2UnipotentBruhatDecomposition
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0012
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0001
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0007
import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral
import Mathlib
import Formalism.ResultantValuation.ResultantAdjugateProofs.Bundle0001
import Formalism.ResultantValuation.ResultantAdjugateProofs.Bundle0002
import Formalism.ResultantValuation.ResultantAdjugateProofs.Laplace
import Formalism.ResultantValuation.PrimePairDyadicDisjointAlt
import Formalism.CyclotomicNorms.IrreducibilityOfGoodTuple
import Formalism.CyclotomicNorms.SubstitutionAdaptive
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0003
import Formalism.CyclotomicNorms.NonsquarefreeBounds.ResModule

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.DividedPowerCoeffValuation
section
namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial TensorProduct

theorem natLog_le_logb (l n : ℕ) (hl : 2 ≤ l) (hn : 1 ≤ n) : (Nat.log l n : ℝ) ≤ Real.logb l n := by
  have h1 : (l : ℝ) ^ (Nat.log l n) ≤ n := by exact_mod_cast Nat.pow_log_le_self l (by omega)
  have hl' : (1 : ℝ) < l := by exact_mod_cast hl
  rw [Real.le_logb_iff_rpow_le hl' (by exact_mod_cast hn), Real.rpow_natCast]
  exact h1

section Frame

open scoped Matrix

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

end Frame

end Formalism.IrreducibleCountingLemmas.WindowSums
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.TWReuse
section
open Finset Polynomial

namespace Formalism.IrreducibleCountingLemmas.TW

theorem substitution_SUB : LemmaSUB := Formalism.CyclotomicNorms.substitutionAdaptive
theorem low_power_series_LOW : LemmaLOW := Formalism.CyclotomicNorms.lowPowerSeries

end Formalism.IrreducibleCountingLemmas.TW
end

