import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.JointWinOfCounts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.PropZ
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoBkRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0011
import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.ThmBabOfLemmaK
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaKOfPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.KBridgeOfKPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ThmBcOfPsiBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Iv
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.MainCotSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LemmaP
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0010
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CorGKOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0018
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Number
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0015
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0017
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ConductorAtMapInjectiveCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CongNum
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ChrInvNeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.LemmaX
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ResidualBernoulliNonvanishing
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0015
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0014

open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy

namespace UpperTheory.V.HV.U

theorem pt (hN : LitN) : GlobalTheory.Published.PoitouTateDuality := GlobalTheory.PoitouTateConj.poitouTateDuality_of_normalised hN.coh.pt

theorem lemmaK (hN : LitN) (hK : K.KBridge) : ∃ CK : ℝ, LemmaK CK :=
  (K.lemmaK (pt hN) hN.coh.lfK hN.coh.ltK hK).imp fun _ h => h.2

theorem localGaloisCohomology₂ (hN : LitN) : Loc.LocalPublishedTheorems :=
  ⟨hN.coh.lfK, hN.coh.ltK, hN.coh.leK, hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.bk⟩

theorem hostVanE (hN : LitN) (hK : K.KBridge) : UnitaryThreeInertia.HostVanE := by
  obtain ⟨CK, hL⟩ := lemmaK hN hK
  exact X.So.hostVanE CK hL (pt hN) hN.coh.lfK hN.coh.ltK hN.coh.lf hN.coh.lt hN.coh.le

end UpperTheory.V.HV.U
