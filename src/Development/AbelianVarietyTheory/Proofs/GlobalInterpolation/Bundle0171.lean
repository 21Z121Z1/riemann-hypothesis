import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0170
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EFirstGeOfULastNonpos
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FivePointLawsTrueChainsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fivePointLaws_trueChains : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∃ Bd : Built.Dat (I.rec7 l Z) u, Bd.ch = tw (I.tw l l0 Z) u a ∧ (∀ i, i ≤ (I.rec7 l Z).R.m → Nonempty (Split (Bd.J.A i) Bd.J.T)) ∧ Bd.Sees ∧ (∀ i, i < (I.rec7 l Z).R.m → ∃ k : Bd.Ker i, Dat.KerEq k ∧ Dat.KerDil k ∧ Dat.KerUK k ∧ Dat.KerBar k ∧ Dat.KerP k) ∧ Bd = dat I l Z u a := by
  first | exact @GlobalTheory.LvT.Built.TrueLaws.laws_true_fam | exact GlobalTheory.LvT.Built.TrueLaws.laws_true_fam | (intros; apply GlobalTheory.LvT.Built.TrueLaws.laws_true_fam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PropertyAtConstructedPointsOfTrueColumnsViewStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView : ∀ (R : ∀ D : D7, Obj D → Prop), (∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)) (nch : NChoice (w.D Z)), ColView w Z O.ex.tw nch → GlobalTheory.LvT.WtSign.BaseSigns B → Formalism.L2.Theta.RealTied (w.D Z) → R (w.D Z) O) → ∀ (K : Ctx) (β : BPt K), β.Is HasCols → R β.D β.O := by
  first | exact @GlobalTheory.Fc.Cv.view_at_built | exact GlobalTheory.Fc.Cv.view_at_built | (intros; apply GlobalTheory.Fc.Cv.view_at_built <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowHInstROfHU
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory

theorem row_hInstR_of_hU (hU : ∀ D : D7, MassRatioUnderVolume D) : ∀ (Bd : BdT) (Q : V4.Slot) (Lk : LkT Bd), ClassTwoEntries.InstanceRankAtConstructedPoints Q Lk :=
  fun _ Q Lk => Row0.row (Row0.of_all (Q := Q) fun _ => by
    intro eps Fm _ x _ i
    exact GlobalTheory.T.volume_signature_indep_and_classNumberItems hU (Fm.D x i)) Lk

end GlobalTheory
end

