import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0008
import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0006
import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0003

namespace PositivityTheory.ThKClose

theorem iLeft_of (h : PositivityTheory.ThKEst.IInv) : PositivityTheory.ThKF.ILeft :=
  fun F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp Φ hΦ g =>
    (h F E σ B n d X W M χX χW om r s r' s' hp Φ hΦ).2.1 g

theorem domWeil_of (h : PositivityTheory.ThKEst.DomWeilU) : PositivityTheory.ThKEst.DomWeil := PositivityTheory.ThKEst.domWeil_of_U h

theorem soSemi_of (h : PositivityTheory.ThKEst.SoSemiU) : PositivityTheory.ThKEst.SoSemi := PositivityTheory.ThKEst.soSemi_of_U h

end PositivityTheory.ThKClose
