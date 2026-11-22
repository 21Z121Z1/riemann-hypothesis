import Formalism.LocalToGlobal.CharacterGerms.Bundle0016
import Formalism.LocalToGlobal.CharacterGerms.Bundle0017
import Formalism.LocalToGlobal.CharacterGerms.Bundle0024
import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStab
import Formalism.LocalToGlobal.CharacterGerms.CoeffSingleSubstOfLowDegree
import Formalism.LocalToGlobal.CharacterGerms.Bundle0036
import Formalism.LocalToGlobal.CharacterGerms.IndependenceBoundRaw
import Formalism.LocalToGlobal.CharacterGerms.Bundle0009
import Formalism.LocalToGlobal.CharacterGerms.RankMaximalOfNondegenerate
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.Bundle0014
import Formalism.LocalToGlobal.CharacterGerms.Bundle0018
import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
import Formalism.LocalToGlobal.CharacterGerms.Bundle0021
import Formalism.LocalToGlobal.CharacterGerms.Bundle0022
import Formalism.LocalToGlobal.CharacterGerms.RowTieValK
import Formalism.LocalToGlobal.CharacterGerms.Bundle0042
import Formalism.LocalToGlobal.CharacterGerms.Bundle0010
import Formalism.LocalToGlobal.CharacterGerms.CharacterHypothesisUnramified
import Formalism.LocalToGlobal.CharacterGerms.Bundle0028
import Formalism.LocalToGlobal.CharacterGerms.Bundle0034

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField Formalism.L2.FormalSeriesBounds.RF
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def TCoordFBSt : Prop := AllFB fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.TCoordSt Hc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

structure GeoIn : Prop where

  lab : LabGeoCoreSt Xo c

  ndg : NondegenerateCharts Xo c

  ch : UpFBr.CharacterHypothesisUnramified Xo c

theorem descent_holds : DescentSt Xo c := descent_of (nabMapSt_holds Xo c) descent_span nvalEqSt_holds

variable {Xo c}
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb] {d : ℕ} [NeZero d]

end Formalism.L2.FormalSeriesBounds
