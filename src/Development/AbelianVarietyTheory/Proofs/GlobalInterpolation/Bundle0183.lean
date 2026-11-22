import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0169
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0288
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0351
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0299

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTwistCoresOverTrueColumns
section
noncomputable section

namespace GlobalTheory.Fc.Cv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem overCols_goodE : ∀ (𝒮 : Slots) (R : V4.Slot), OverCols (IsGoodE 𝒮) ∧ OverCols (sAnd (IsGoodE 𝒮) R) := by
  intro 𝒮 R
  have h : OverCols (IsGoodE 𝒮) :=
    (overCols_built 𝒮).2 (GoodE 𝒮) fun _ _ _ _ _ _ _ g => ⟨g.1.choose⟩
  exact ⟨h, OverCols.and_left h⟩

end GlobalTheory.Fc.Cv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowAAtGAtBuilt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Fc

theorem row_aAtG_at_built (𝒮 : Slots) (hR : 𝒮.Rx = RX) (Lk : LkT Bundle) :
    Lg1 KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) fun S => AllBundlePointProperties.ArithmeticConditionAtBundlePoints S Lk := by
  refine ⟨fun _ _ _ _ _ => True, largeBaseProperty_true, ?_⟩
  refine GlobalTheory.T.holds_at_bundlePoints_of_trueColumns _ Lk fun K X f T c h => ?_
  refine positionOf_mono (P := GoodE 𝒮) ?_ K X f T c h.1
  rintro K B f T w Z c ⟨⟨b, -⟩, -⟩
  refine ⟨(GlobalTheory.Svd.builtC_hasPart 𝒮).1 K B f T w Z c ⟨b⟩, fun a => ?_⟩
  have hx : RX K B f T w Z c.Wt c.O.p0 b.what₂ := hR ▸ b.rx
  exact GlobalTheory.T.rowFormsMatchPeriodMap_of_furtherProperties K B f T w Z c.Wt c.O.p0 b.what₂ hx a

end GlobalTheory.Fc
end

