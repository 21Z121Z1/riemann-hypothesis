import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

structure GermAt [StarRing (𝓞 E)] (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) where

  B : Germ.FB S d (𝓞 E)

  x : ∀ m, jOG x0 d m 1 ⟶ t.G

  e : ∀ m, FrTyG t x0 d x m

  tg : Fin d → (Sp (DualNumber S) ⟶ t.G.left)
  chart : IsChartG t x0 d B.G.F B.A.act tg (fun l j => if l = j then 1 else 0) x
  tan : ∀ l, IsTanAtG t x0 (tg l)
  basis : ∀ w, IsTanAtG t x0 w → ∃! a : Fin d → S, IsCombAtG t x0 tg a w
  frame : IsFrameG t x0 d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e
  trunc : FrTrunc t x0 d x e
  axes : FrAxes t x0 d x e

def PowFns (t : SAB H X0) : Prop := ∀ n, Function.Bijective (Out.powObj t.G n).hom.appTop.hom

def GeomPF (t : SAB H X0) {k : Type} [Field k] (x : Sp k ⟶ X0) : Prop :=
  ∃ (T : TorusExtension ((Over.pullback x).obj t.G)) (M : LB T.B.left),
    letI := T.grpB
    M.IsLB ∧ Out.KTriv T.B M ∧ LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (M.pull T.q.left)

def FibPF (t : SAB H X0) (z : X0) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ X0), x (IsLocalRing.closedPoint k) = z ∧ GeomPF t x

def toFirst (k : Type) [CommRing k] (m : ℕ) (hm : 1 ≤ m) : Jet k Unit m →ₐ[k] Jet k Unit 1 :=
  Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (by omega))

def TanPF (t : SAB H X0) {k : Type} [Field k] (x : Sp k ⟶ X0) (p : ℕ) : Prop :=
  ∀ (hp : 1 ≤ p) (y : overAt x (Jet k Unit p) ⟶ t.G), homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → y ^ p = 1 →
    (∃ c : LB.Gen (Out.translDiff t.G t.PP.L (homAt x (toFirst k p hp) ≫ y)), c.IsGen) →
      homAt x (toFirst k p hp) ≫ y = 1

end GlobalTheory.CompanionTheory.Ar.Conj
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TraceWedgePairingPerfectRationalForms
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.abelian₂

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

def ball1 (r p : ℕ) (η : ℝ) : Set (Upq r p) :=
  {g | ∀ a b : Fin r, ‖((g : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b - (if a = b then 1 else 0)‖ ≤ η}

def ballVol (r p : ℕ) (η : ℝ) : ℝ≥0∞ := haarU r p (ball1 r p η)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def uBall (X : Data E r) (η : ℝ) : Set (RealGrp X) := {g | ∀ τ, g τ ∈ ball1 r X.p0 η}

def VolLe (X : Data E r) (V : ℝ) : Prop :=
  quotInt X (fun _ => 1) ≤ ENNReal.ofReal (Real.exp V) * ballVol r X.p0 1 ^ fdeg E

def Thick (X : DataX E r) (ε : ℝ) (x : Frame X.Ψ r) : Prop :=
  ∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v)

def Transv (X : DataX E r) (la : Wt X.Ψ r) (M : ℝ) : Prop :=
  ∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
    ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧
      ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.flowMat v τ ((M : ℂ) * τ.1 b)

def wtAbs {Ψ : Finset (E →+* ℂ)} (la : Wt Ψ r) : ℝ := ∑ τ, ∑ i, |(la τ i : ℝ)|

def shortB (f r d ε : ℝ) : ℝ := max 1 ((2 * f * r) ^ 4 * d ^ 2 / (4 * ε))

def injRad (f r d N ε : ℝ) : ℝ := Real.sqrt (ε / shortB f r d ε) / (8 * r ^ 2 * N)

def zNum (f r L d Om : ℝ) : ℝ := f * r + L + Real.log d + |Om|

def lamConst (C f r L d Om S : ℝ) : ℝ :=
  C * zNum f r L d Om ^ 2 * (1 + Real.log S) * S + C * (f * r * L) ^ 3

end GlobalTheory.CompanionTheory.Ar.abelian₂
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwistedDualRegularFormsFiniteCover
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Deg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open Classical in

def fundF (X : Data E r) : Set (V (nd X)) :=
  if h : ∃ FF, IsFundSet X (x0F X) FF then h.choose else ∅

def petU (X : Data E r) (la : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ) : ℂ :=
  ∫ z in fundF X, P (cpt X (x0F X) z) * (starRingEnd ℂ) (Q (cpt X (x0F X) z)) *
    ((X.nfac la (cpt X (x0F X) z) ^ 2 : ℝ) : ℂ) ∂muF X (x0F X)

def pet (X : Data E r) (la : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ) : ℂ :=
  petU X la P Q / (((covol X).toReal : ℝ) : ℂ)

end GlobalTheory.CompanionTheory.Ar.Deg
end
end

