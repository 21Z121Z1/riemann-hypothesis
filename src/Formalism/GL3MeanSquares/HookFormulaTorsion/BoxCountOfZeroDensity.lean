import Mathlib
import Formalism.GL3MeanSquares.Bundle0004
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0013
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0010

noncomputable section

namespace Formalism.HermitianLattices.ZeroDensityInBoxes

theorem box_tail_bound_all : BoxTailAll := Formalism.HermitianLattices.Ext.BoxTail.box_tail_bound

theorem box_count_of_zero_density : BoxCountOfZD := fun h =>
  Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.boxCountHyp_of_zeroDensityBox h

end Formalism.HermitianLattices.ZeroDensityInBoxes
