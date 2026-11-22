import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0015
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlCTendsto
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar.Rec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx} {Fr : Small.GenFrame Or} {h : GenFrEx Xo c} {Z : Comp Xo c}

def GeoRead (Rd : Reading Fr h Z) : Prop :=
  letI := Small.cstAlg Or
  ∃ y' : FrPt Xo c RM.Ω, FrMap ({ Rd.φ with commutes' := Rd.φ_cst } : Om Z →ₐ[c.F] RM.Ω) (genFr h Z) y' ∧
    FrBor Rd.t y' Fr.y₀

end GlobalTheory.CompanionTheory.Ar.Plug
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ShortIn
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

open Classical in

def MultIn (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) (Z : Comp Xo c)
    (a₁ a' : WZ D.host.E) (B : ℕ) (cc : ℝ) : Prop :=
  ∃ (aτ : WZ D.host.E) (w : CMType H → ℤ) (F : FlatSec U (xiR D) (e Z) (flatZ H w)) (μ m : ℕ) (τ : Rul Xo c)
    (S : Finset ℕ) (ep bτ b cp : ℕ → ℝ) (c₀ ρ A P R₀ cinf : ℝ) (rh : ∀ σ k, Frame ((U σ).X k).Ψ D.R.r → ℝ),
    0 < μ ∧ WEq Dw ((8 * μ) • a₁) ((8 * μ) • a' + (3 * μ) • aτ + m • flatZ H w) ∧ τ ∈ secZ Xo c aτ ∧ evC h Z τ ≠ 0 ∧
    c₀ ≤ 3 * ρ ∧
    (∀ (p : ℕ), p.Prime → ∀ la : HeightOneSpectrum (𝓞 c.F), (p : 𝓞 c.F) ∈ la.asIdeal →
      (Ref.pjSys Xo c).RefBound (cuspZ Xo c U a₁) la (ramOverZ la * ep p) c₀ (Ref.phU Xo c la) ∧
      -F.cFin la ≤ ramOverZ la * b p ∧ ∀ y : (Ref.pjSys Xo c).Pt la, 0 ≤ Ref.phU Xo c la y ∧
        ((8 * ρ * Ref.phU Xo c la y - ramOverZ la * bτ p : ℝ) : EReal) ≤ (Ref.pjSys Xo c).val y τ) ∧
    (∀ p ∈ S, p.Prime) ∧ (∀ p, 0 ≤ cp p) ∧ (∀ p, p ∉ S → cp p = 0) ∧
    (∀ p : ℕ, p.Prime → (((8 * μ : ℕ) : ℝ) * (ep p + (if p ≤ B ∨ (p : ℤ) ∣ 2 * discr D.host.E * l.M' then
      1 / ((p : ℝ) - 1) + (if p = 2 then 1 else 0) + (padicValInt p (discr D.host.E) : ℝ) / Module.finrank ℚ D.host.E else 0) *
        Top.l1 (towerWt Dw a')) + ((3 * μ : ℕ) : ℝ) * bτ p + m * b p) * Real.log p ≤ ((8 * μ : ℕ) : ℝ) * cp p) ∧
    (∀ σ, GoodEmb c σ → ∀ k, Over (U σ) (e Z) k →
      ∃ (x0 : Frame ((U σ).X k).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))),
        IsOrth ((U σ).X k) x0 ∧ IsFundSet ((U σ).X k) x0 FF ∧ ∀ y ∈ ((U σ).X k).dom,
          ThA.BergLB ((U σ).X k) x0 FF (laZ (U σ) a₁ k) y (Real.exp (-(A + 3 * rh σ k y))) ∧
          lieFacZ Dw (xiR D) aτ * ((U σ).X k).pnorm (laZ (U σ) aτ k) (rdU (U σ) τ k) y ≤
            Real.exp (4 * (2 * P - rh σ k y) + R₀)) ∧
    ((8 * μ : ℕ) : ℝ) * (A / 2 + 3 * P) + ((3 * μ : ℕ) : ℝ) * R₀ +
      m * ((∑ σ : c.F →+* ℂ, Real.log (F.cInf σ)) / Module.finrank ℚ c.F) ≤ ((8 * μ : ℕ) : ℝ) * cinf ∧
    ∑ p ∈ S, cp p + cinf ≤ cc

def ShortIn {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] (L : Submodule (𝓞 K) V)
    (ip : (K →+* ℂ) → V → V → ℂ) (Λ : ℝ) : Prop :=
  ∃ (n : ℕ) (ω : Fin n → V), Submodule.span ℤ (Set.range ω) = L.restrictScalars ℤ ∧ ∀ σ j, (ip σ (ω j) (ω j)).re ≤ Λ ^ 2

example {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] (ip : (K →+* ℂ) → V → V → ℂ) (Λ : ℝ) :
    ShortIn (⊥ : Submodule (𝓞 K) V) ip Λ := ⟨0, Fin.elim0, by simp, fun _ j => j.elim0⟩

end GlobalTheory.CompanionTheory.Ar.Rec
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerPin
section
noncomputable section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Rec

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH

def TowerPin {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (a : WZ E) (B : ℕ) (top dg : Comp Xo c → ℚ → ℝ) : Prop :=
  ∃ (_ : DecidableEq (CMType H)) (II : IntersectionSystem) (Xf : ∀ l : Level H, Moduli Dw l) (hX : Xo = Xf l)
    (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T)
    (κ : Comp Xo c ≃ T.Comp), IsFullIntersectionSystem II ∧ Top.IsGlobal Xf l c (hX ▸ Y) ∧ o.Extra ∧
      CompOf o.toTowerOrigin κ ∧ ∀ (Z : Comp Xo c) (s : ℚ),
        top Z s = T.mbarTop II B (κ Z) (towerWt Dw a) s ∧ dg Z s = T.mDeg B (κ Z) (towerWt Dw a) s

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def MbarPin {D : D7} {Q : Par D} {M : ℕ} (S : SharpGeo Q M) (i : Fin D.R.m) (up : RW D) (g : ℝ) (Bm : MbarIn S i up) :
    Prop :=
  TowerPin (S.Xo i) S.c (wtZ' D i up) ⌊Top.bigB0 (towerWt (Q.Dw ((i : ℕ) + 1)) (wtZ' D i up)) g⌋₊ Bm.top Bm.dg

end GlobalTheory.CompanionTheory.Ar.Rec
end
end

