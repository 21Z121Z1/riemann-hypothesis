import Development.EtaleCohomology.EtaleSheaves.Bundle0088
import Development.EtaleCohomology.EtaleSheaves.Bundle0066
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008

-- bundled from Development.EtaleCohomology.EtaleSheaves.CompositionGoal
section
namespace LateralTheory.E.CompositionGoal

theorem goal_of : LateralTheory.E.SHExistsPf.Comp := LateralTheory.E.TruncationIsoComparison.Comp_of

end LateralTheory.E.CompositionGoal
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ReducedOfSmooth
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.ReducedOfSmooth

theorem LeafReducedSmooth_of : LateralTheory.E.QuasiFiniteDescent.LeafReducedSmooth := by
  intro k _ Ω _ _ R _ D q hq
  have : Smooth q := hq.smooth
  have : _root_.IsReduced R := isReduced_of_injective R.val Subtype.val_injective
  have : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of R)) := inferInstance
  exact GlobalTheory.isReduced_of_smooth_of_isReduced q

end LateralTheory.E.ReducedOfSmooth
end
end

