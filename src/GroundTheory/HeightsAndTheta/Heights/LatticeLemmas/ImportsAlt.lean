import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Imports
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Bundle0009
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

universe u v

theorem LocalGlobalIndex.full : LocalGlobalIndex.Statement.{u, v} := LocalGlobalIndex.proof

theorem LocalLatticeIndex.full : LocalLatticeIndex.Statement.{u, v} := LocalLatticeIndex.proof

theorem LocalIndex.full : LocalIndex.Statement.{u, v} :=
  LocalIndex.proof LocalGlobalIndex.full LocalLatticeIndex.full

theorem LocalChange.full : LocalChange.Statement.{u, v} :=
  LocalChange.full_of_localIndex LocalIndex.full

end GroundTheory.Heights₂.Heights.LatticeLemmas
