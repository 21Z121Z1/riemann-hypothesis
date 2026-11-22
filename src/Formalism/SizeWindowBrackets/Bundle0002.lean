import Formalism.RankGapBounds.Bundle0001
import Formalism.SizeWindowBrackets.Bundle0001

-- bundled from Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
section
open Real

namespace Formalism.LFunctionChainParameters.WeightedSlopeBounds

open Formalism.RankGapBounds.WeightedMeanData

noncomputable section

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)

def Lo5 (u0 : U0) (u : W u0) : ℝ :=
  C.cSl1 * D.IO u0 + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * Real.log (D.T u0 u)
    + C.cSl1 * Xpp + 1

def QuotientSlopeBoundsWith : Prop :=
  ∀ u0 (u : W u0),
    D.muMaxN u0 u ≤ D.muMaxM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u + C.cSl1 * (m : ℝ) * D.B0 ∧
    D.muM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u - Lo5 D C Xpp u0 u ≤ D.muN u0 u

def EComp5 : Prop :=
  ∀ u0 (u : W u0), |D.Ee u0 u - (m : ℝ) * D.sumA * D.lg| ≤ C.cE * (m : ℝ) * D.B0

def Count5 : Prop :=
  ∀ u0 (u : W u0),
    ((∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)) + (m : ℝ) * D.lg
        - C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k) ≤ Real.log (D.T u0 u)) ∧
    Real.log (D.T u0 u) ≤ C.cCount * (m : ℝ) * D.L ∧
    ∀ u' : W u0, |Real.log (D.T u0 u) - Real.log (D.T u0 u')| ≤ C.cCount * Real.log D.k

def LossBounds : Prop :=
  ∀ u0, D.ASK u0 - D.Ga u0 ≤ D.LoP C ∧ D.IO u0 ≤ D.LoP C

def MLo5 : ℝ :=
  C.cSl1 * D.LoP C + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L)
    + C.cSl1 * Xpp + 1

def UBar5 : ℝ :=
  C.cSlope * D.nT * D.a * D.La * (2 + (m : ℝ) / D.k) + D.Vvar C + C.cSl1 * (m : ℝ) * D.B0
    + MLo5 D C Xpp

def ErrX5at (u0 : U0) : ℝ :=
  D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k))
    + (C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε))
    + (m : ℝ) * C.cE * D.B0
    + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
    + Real.log (Fintype.card (W u0) : ℝ)
    + D.LoP C
    + MLo5 D C Xpp
    + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH) * (UBar5 D C Xpp + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))

def errorTermWith : ℝ :=
  D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k))
    + (C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε))
    + (m : ℝ) * C.cE * D.B0
    + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
    + umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))
    + D.LoP C
    + MLo5 D C Xpp
    + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH) * (UBar5 D C Xpp + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))

def MeanBoundWith : Prop :=
  Nonempty U0 → D.HidaSetting C → D.DIV C → EComp5 D C → D.HComp C → Count5 D C → D.Slopes C →
    QuotientSlopeBoundsWith D C Xpp → LossBounds D C → D.SlopeIneq → D.HHBound C → D.FParams →
    umean D.ASK ≤ umean D.Main + errorTermWith D C Xpp

def PointwiseBoundVariant : Prop :=
  D.HidaSetting C → D.DIV C → EComp5 D C → D.HComp C → Count5 D C → D.Slopes C →
    QuotientSlopeBoundsWith D C Xpp → LossBounds D C → D.SlopeIneq → D.HHBound C → D.FParams →
    ∀ u0, D.ASK u0 ≤ D.Main u0 + ErrX5at D C Xpp u0

def MeanBoundOfLossBounds : Prop :=
  Nonempty U0 → D.HidaSetting C → D.DIV C → EComp5 D C → D.HComp C → Count5 D C → D.Slopes C →
    QuotientSlopeBoundsWith D C Xpp → D.Losses C → D.SlopeIneq → D.HHBound C → D.FParams →
    umean D.ASK ≤ umean D.Main + errorTermWith D C Xpp

end

end Formalism.LFunctionChainParameters.WeightedSlopeBounds
end

-- bundled from Formalism.SizeWindowBrackets.SlopeExcessBoundExponentZero
section
open Real

namespace Formalism.LFunctionChainParameters.PhiMonotonicityLemmas

noncomputable section

def phi (H u : ℝ) : ℝ := u * Real.log (1 + H / u)

def ErrF (del u HH η e : ℝ) : ℝ :=
  (1 - del)⁻¹ * (4 * phi HH u + (η + 4 * Real.sqrt e) * HH)

def ConclF (s mu logI del u HH η e : ℝ) : Prop :=
  s - logI - ErrF del u HH η e ≤ mu

def PhiStrictMono : Prop :=
  ∀ H : ℝ, 0 < H → StrictMonoOn (phi H) (Set.Ici 0)

def PhiMono : Prop :=
  ∀ H : ℝ, 0 ≤ H → MonotoneOn (phi H) (Set.Ici 0)

def PhiMax : Prop :=
  ∀ H u b : ℝ, 0 ≤ H → 0 ≤ u → phi H u ≤ phi H (max u b)

def PhiBelow : Prop :=
  ∀ H u b : ℝ, 0 ≤ H → 0 ≤ u → u ≤ b → phi H u ≤ phi H b ∧ phi H u ≤ phi H b + b

def PhiSplit : Prop :=
  ∀ H u c : ℝ, 0 ≤ H → 0 ≤ u → 0 < c →
    phi H u ≤ u * Real.log (1 + H / c) + c * Real.exp (-1)

def ConclFMono : Prop :=
  ∀ s mu logI del u u' HH η e : ℝ, del < 1 → 0 ≤ HH → 0 ≤ u → u ≤ u' →
    ConclF s mu logI del u HH η e → ConclF s mu logI del u' HH η e

def EtaHH : Prop :=
  ∀ sg b HH η e e0 de C1 : ℝ, 0 < sg → 0 ≤ HH → HH ≤ b / sg →
    η ≤ 5 * sg + C1 * Real.sqrt de → e ≤ 2 * e0 →
    C1 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ sg →
    (η + 4 * Real.sqrt e) * HH ≤ 6 * b

def EtaHHSharp : Prop :=
  ∀ sg b e0 de C1 : ℝ, 0 < sg → 0 < b →
    (((5 * sg + C1 * Real.sqrt de) + 4 * Real.sqrt (2 * e0)) * (b / sg) ≤ 6 * b ↔
      C1 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ sg)

def SmallE : Prop :=
  ∀ sg e0 : ℝ, 4 * Real.sqrt (2 * e0) ≤ sg → sg ≤ 2 → 2 * e0 ≤ 1 / 4

def DelConst : Prop :=
  ∀ del : ℝ, del < 1 →
    ((1 - del)⁻¹ * 4 ≤ 5 ↔ del ≤ 1 / 5) ∧ ((1 - del)⁻¹ * 6 ≤ 7 ↔ del ≤ 1 / 7)

def Line1 : Prop :=
  ∀ s mu logI del u HH η e b : ℝ, del ≤ 1 / 7 → 0 ≤ b → 0 ≤ HH → 0 ≤ u →
    (η + 4 * Real.sqrt e) * HH ≤ 6 * b → ConclF s mu logI del u HH η e →
    s ≤ mu + logI + 5 * phi HH u + 7 * b

def Line1Max : Prop :=
  ∀ s mu logI del u HH η e b : ℝ, del ≤ 1 / 7 → 0 ≤ b → 0 ≤ HH → 0 ≤ u →
    (η + 4 * Real.sqrt e) * HH ≤ 6 * b → ConclF s mu logI del u HH η e →
    s ≤ mu + logI + 5 * phi HH (max u b) + 7 * b

def Line1NeedsDel : Prop :=
  ∀ del : ℝ, 1 / 7 < del → del < 1 → ∃ s mu logI u HH η e b : ℝ,
    0 < b ∧ 0 < HH ∧ 0 ≤ u ∧ 0 ≤ η ∧ η ≤ 1 ∧ 0 ≤ e ∧ e ≤ 1 / 4 ∧ 0 ≤ logI ∧ s - mu ≤ HH ∧
    (η + 4 * Real.sqrt e) * HH ≤ 6 * b ∧ ConclF s mu logI del u HH η e ∧
    ¬ (s ≤ mu + logI + 5 * phi HH u + 7 * b)

def LogMax : Prop :=
  ∀ sg b HH u : ℝ, 0 < sg → 0 < b → 0 ≤ HH → HH ≤ b / sg →
    Real.log (1 + HH / max u b) ≤ Real.log (1 + 1 / sg)

def LogPow : Prop :=
  ∀ x c : ℝ, 2 ≤ x → 0 ≤ c → Real.log (1 + x ^ c) ≤ (c + 1) * Real.log x

def LogPow4 : Prop :=
  ∀ x c : ℝ, 2 ≤ x → 0 ≤ c → Real.log (1 + 4 * x ^ c) ≤ (c + 3) * Real.log x

def PhiErr : Prop :=
  ∀ u E HH b x c : ℝ, 2 ≤ x → 0 ≤ c → 0 < b → 0 ≤ HH → HH ≤ x ^ c * b → 0 ≤ u → u ≤ E → b ≤ E →
    phi HH u ≤ E * ((c + 1) * Real.log x)

def FinalLine : Prop :=
  ∀ s mu logI del u U HH η e b x c : ℝ, 2 ≤ x → 0 ≤ c → 0 < b → 0 ≤ HH → HH ≤ x ^ c * b →
    0 ≤ u → u ≤ U → del ≤ 1 / 7 → (η + 4 * Real.sqrt e) * HH ≤ 6 * b →
    ConclF s mu logI del u HH η e →
    s ≤ mu + logI + 5 * (c + 1) * Real.log x * (U + b) + 7 * b

def CorFinal : Prop :=
  ∀ s mu logI del u U HH η e e0 de C1 b x c : ℝ, 2 ≤ x → 0 ≤ c → 0 < b → 0 ≤ HH →
    HH ≤ x ^ c * b → 0 ≤ u → u ≤ U → del ≤ 1 / 7 →
    η ≤ 5 * x ^ (-c) + C1 * Real.sqrt de → e ≤ 2 * e0 →
    C1 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ x ^ (-c) →
    ConclF s mu logI del u HH η e →
    s ≤ mu + logI + 5 * (c + 1) * Real.log x * (U + b) + 7 * b

def CorFinalModel : Prop :=
  ∃ s mu logI del u U HH η e e0 de C1 b x c : ℝ, 2 ≤ x ∧ 0 ≤ c ∧ 0 < b ∧ 0 < HH ∧
    HH ≤ x ^ c * b ∧ 0 < u ∧ u ≤ U ∧ 0 < del ∧ del ≤ 1 / 7 ∧ 0 < de ∧ 0 < e0 ∧ 0 < C1 ∧
    x ^ (-c) ≤ 1 / 20 ∧ η = 5 * x ^ (-c) + C1 * Real.sqrt de ∧ e = 2 * e0 ∧ e ≤ 1 / 4 ∧
    C1 * Real.sqrt de + 4 * Real.sqrt (2 * e0) ≤ x ^ (-c) ∧ 0 ≤ logI ∧ s - mu ≤ HH ∧
    s - logI - ErrF del u HH η e = mu

def WindowBoundInB : Prop :=
  ∀ s mu logI k del u cU W HH η e b x c : ℝ, 2 ≤ x → 0 ≤ c → 0 < b → 0 ≤ HH →
    HH ≤ x ^ c * b → 0 ≤ u → u ≤ cU * W → del ≤ 1 / 20 →
    (η + 4 * Real.sqrt e) * HH ≤ 6 * b → logI ≤ k → k ≤ b / 5 →
    ConclF s mu logI del u HH η e →
    s ≤ mu + 5 * (c + 3) * cU * Real.log x * W + 7 * b

def WindowBoundInW : Prop :=
  ∀ s mu logI k del u cU W HH η e b x c : ℝ, 2 ≤ x → 0 ≤ c → 0 < b → 0 ≤ HH →
    HH ≤ x ^ c * b → 0 ≤ u → u ≤ cU * W → del ≤ 1 / 7 →
    (η + 4 * Real.sqrt e) * HH ≤ 6 * b → logI ≤ k → k ≤ W → b ≤ W →
    ConclF s mu logI del u HH η e →
    s ≤ mu + (5 * (c + 1) * (cU + 1) + 2) * Real.log x * W + 7 * b

def WindowBoundSizes : Prop :=
  ∀ s mu logI k del u cU nT a L mB0 Loss HH η e b x c : ℝ, 2 ≤ x → 0 ≤ c → 0 < b → 0 ≤ HH →
    HH ≤ x ^ c * b → 0 ≤ u → a = x * b → 1 ≤ nT → 1 ≤ L → 0 ≤ mB0 → 0 ≤ Loss →
    u ≤ cU * (nT * a * L + mB0 + Loss) → del ≤ 1 / 7 →
    (η + 4 * Real.sqrt e) * HH ≤ 6 * b → logI ≤ k → k ≤ b →
    ConclF s mu logI del u HH η e →
    s ≤ mu + (5 * (c + 1) * (cU + 1) + 2) * Real.log x * (nT * a * L + mB0 + Loss) + 7 * b

def WindowBoundSharp : Prop :=
  ∀ s mu del u cU W HH η e b x c : ℝ, 2 ≤ x → 0 ≤ c → 0 < b → 0 ≤ HH →
    HH ≤ x ^ c * b → 0 ≤ u → u ≤ cU * W → del ≤ 1 / 7 →
    (η + 4 * Real.sqrt e) * HH ≤ 6 * b → b ≤ W →
    ConclF s mu 0 del u HH η e →
    s ≤ mu + 5 * (c + 1) * (cU + 1) * Real.log x * W + 7 * b

def WindowBoundNeedsK : Prop :=
  ∀ C c : ℝ, 0 < c → ∃ s mu logI k del u W HH η e b x : ℝ,
    2 ≤ x ∧ 0 < b ∧ 0 < HH ∧ HH ≤ x ^ c * b ∧ 0 ≤ u ∧ u ≤ W ∧ b ≤ W ∧ 0 ≤ del ∧ del ≤ 1 / 20 ∧
    0 ≤ η ∧ 0 ≤ e ∧ e ≤ 1 / 4 ∧ (η + 4 * Real.sqrt e) * HH ≤ 6 * b ∧ 0 ≤ logI ∧ logI ≤ k ∧
    s - mu ≤ HH ∧ ConclF s mu logI del u HH η e ∧
    ¬ (s ≤ mu + C * Real.log x * W + 7 * b)

def WindowBoundNeedsKNotSharp : Prop :=
  ∀ s mu del u W HH η e b x c C : ℝ, 2 ≤ x → 0 ≤ c → 0 < b → 0 ≤ HH →
    HH ≤ x ^ c * b → 0 ≤ u → u ≤ W → del ≤ 1 / 7 →
    (η + 4 * Real.sqrt e) * HH ≤ 6 * b → b ≤ W → 10 * (c + 1) ≤ C →
    ¬ (s ≤ mu + C * Real.log x * W + 7 * b) → ¬ ConclF s mu 0 del u HH η e

def SlopeExcessBoundExponentZero : Prop :=
  ∀ s mu W HH b x C : ℝ, 2 ≤ x → 0 < b → 0 ≤ W → 0 ≤ C → HH ≤ x ^ (0 : ℝ) * b → s - mu ≤ HH →
    s ≤ mu + C * Real.log x * W + 7 * b

open Formalism.LFunctionChainParameters.WeightedMeanLemmas in

def CorFamily (ι : Type*) [Fintype ι] [Nonempty ι] : Prop :=
  ∀ (d muMaxN muN muMaxM muM h dr BE : ι → ℝ) (Sg0 A A' V mu del HH η e b x c : ℝ),
    (∀ u, 0 < d u) → (∀ u, 0 ≤ dr u) → (∀ u, muN u ≤ muMaxN u) →
    Slopes2ge muMaxN muN muMaxM muM dr BE Sg0 →
    (∀ u, muMaxM u ≤ A) → (∀ u, -A' ≤ muM u) → (∀ u u', |h u - h u'| ≤ V) →
    2 ≤ x → 0 ≤ c → 0 < b → 0 ≤ HH → HH ≤ x ^ c * b → del ≤ 1 / 7 →
    (η + 4 * Real.sqrt e) * HH ≤ 6 * b →
    ConclF (sF d muN h) mu (Real.log (Fintype.card ι : ℝ)) del (uF d muMaxN muN h) HH η e →
    sF d muN h ≤ mu + Real.log (Fintype.card ι : ℝ)
      + 5 * (c + 1) * Real.log x * (A + A' + V + wmean d (fun u => dr u + BE u) + b) + 7 * b

section SizeData₂

open Formalism.RankGapBounds.WeightedMeanData

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)

def EntropyBound : Prop :=
  D.HidaSetting C → D.SlopeIneq → D.HHBound C → D.FParams → D.delBar ≤ 1 / 7 →
    (D.etaBar + 4 * Real.sqrt D.eBar) * D.x ^ C.cHH ≤ 6 →
    ∀ u0, D.s u0 ≤ D.muCC u0 + Real.log (Fintype.card (W u0) : ℝ)
      + 5 * (D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0)) + 7 * D.b

end SizeData₂

end

end Formalism.LFunctionChainParameters.PhiMonotonicityLemmas
end

