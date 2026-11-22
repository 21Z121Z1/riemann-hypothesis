import Formalism.LogFactorialIndices.SignedSubspaceIndex.SumInterlacedBoundFails
import Mathlib
import Formalism.LogFactorialIndices.SignedSubspaceIndex.Bundle0001
import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxDet

namespace Formalism.LatticeIndexTer

theorem latFinite : LatFinite := lattice_quotient_finite
theorem latBasis : LatBasis := lattice_has_basis
theorem idxDet : IdxDet := lattice_index_eq_det_valuation

end Formalism.LatticeIndexTer
