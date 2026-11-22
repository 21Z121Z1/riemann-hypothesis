import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0018
set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLength.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLength.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalLength.proof.{u} GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_SemilocalLengthSum GroundTheory.Heights₂.Heights.FieldNumbers.FibreRelDim.proof GroundTheory.Heights₂.Heights.FieldNumbers.DivCycleMinimal.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_ConeLocalLength
