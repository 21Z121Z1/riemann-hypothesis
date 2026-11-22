import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.Bundle0003
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.Bundle0002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.Bundle0005
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PHypEmb
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PFinCov
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PLowTL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PTowerL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.Bundle0004
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PTopPart

namespace UpperTheory.Gal.KunnethLefschetz

theorem steps_holds : Steps :=
  ⟨offEx_holds, pairs_holds, pnFacts_holds, hypEmb_holds, finCov_holds, finFib_holds, comps_holds, ringL_holds, lowTL_holds, ptVanT_holds, lowL_holds, towerL_holds, affVan_holds, twBij_holds, gysTL_holds, gysinTwistZero_exists, qEasy_holds, limOnto_holds, qOnto_holds, qProj_holds, kunBij_holds, kunL_holds, swap_holds, slice_holds, ptInt_holds, detectL_holds, dualL_holds, finSupp_holds, pnCls_holds, injL_holds, trComp_holds, divL_holds, basisOne_holds, topPart_holds⟩

theorem qDual_holds (hI : In) (hT : TrIn) : QDual := steps_holds.qDual hI hT

theorem qDiag_holds (hI : In) (hT : TrIn) : QDiag := steps_holds.qDiag hI hT

end UpperTheory.Gal.KunnethLefschetz
