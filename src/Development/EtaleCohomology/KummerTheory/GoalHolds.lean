import Development.EtaleCohomology.KummerTheory.Bundle0003
import Development.EtaleCohomology.KummerTheory.Bundle0016
import Development.EtaleCohomology.KummerTheory.Bundle0017
import Development.EtaleCohomology.KummerTheory.FinBock
import Development.EtaleCohomology.KummerTheory.Bundle0013

namespace LateralTheory.KummerTheory

theorem goal_holds : GOAL :=
  goal_of LateralTheory.Fin.LH.intersectionNumber_baseChange LateralTheory.Fin.SHInv.intersectionNumber_baseChange LateralTheory.Fin.Stalk.intersectionNumber_baseChange LateralTheory.Fin.Bock.intersectionNumber_baseChange
    LateralTheory.Fin.AdicDeg.intersectionNumber_baseChange LateralTheory.Fin.Limit.intersectionNumber_baseChange

end LateralTheory.KummerTheory
