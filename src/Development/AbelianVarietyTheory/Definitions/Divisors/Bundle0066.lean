import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)

namespace GlobalTheory.HSApp

def AmpleAt {Y : Scheme.{0}} (N : LB Y) (y : Y) : Prop :=
  ∃ (m : ℕ) (A : LB Y) (s : (LB.div (lbPow N m) A).Sec), 0 < m ∧ A.IsLB ∧ IsAmpleLB A ∧ y ∈ nonzeroLocus s

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def GapGe (g : ℤ) (la : AllWt.Weight Dw) : Prop := ∀ (τ : Psi H) (k : ℕ), k + 1 < Dw.p + Dw.q → g ≤ gap (la τ) k

structure WtBig (P : WtPar Dw) : Prop where
  gaps : GapGe (((dimFlag Dw + 3) * ((dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + dimFlag Dw + 3) : ℕ) : ℤ) P.u₁
  le_T : dimFlag Dw + 1 ≤ P.T
  one_le : 1 ≤ dimFlag Dw

variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def CuspIso (la : AllWt.Weight Dw) : Prop := Extends X Z U la ∧ vanBd X Z la ≤ space X Z U la

def Steep (la : AllWt.Weight Dw) : Prop :=
  ∃ s : space X Z U la, s ≠ 0 ∧ ∀ (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) (Δ : Cartier ((baseId X Z U la).comap M.σ)),
    ∀ y ∈ M.bd, y ∉ nonzeroLocus (toSec (Δ.lift s))

variable {D : D7} (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r)

def BergLe (la : AllWt.Weight Dw) (β : ℝ) : Prop :=
  ∀ σ, GoodEmb c σ → ∀ y : FPt (U σ).X, (⟨y.1, y.2.1⟩ : Σ k, FD.Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
    bergOn (U σ) (V σ) (dict σ) Z (wtOf Dw la 0) y ≤ ENNReal.ofReal β

theorem GapGe.mono {g g' : ℤ} {la : AllWt.Weight Dw} (h : GapGe g la) (e : g' ≤ g) : GapGe g' la :=
  fun τ k hk => e.trans (h τ k hk)

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ScalOf
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT

namespace GlobalTheory.BigOn

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Any

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def scalOf (R : RealDat D A Ks) (F : Face D A) : (type_of% R.lam) × ℝ :=
  haveI : Nonempty ((type_of% R.lam) × ℝ) := ⟨(R.lam, 0)⟩
  Classical.epsilon fun q => (reScal R q.1 q.2).Char F

def charOf (R : RealDat D A Ks) (F : Face D A) : RealDat D A Ks := reScal R (scalOf R F).1 (scalOf R F).2

end Any

variable {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

set_option maxHeartbeats 1000000 in

def reFw (fw : FWTie J R κ v₀) (F : Face D A) : FWTie J (charOf R F) κ v₀ := { fw with }

set_option maxHeartbeats 1000000 in

def reOM {i : Fin D.R.m} (O : OMDat J.toCore R i Unit (fun _ => A.μ0)) (F : Face D A) :
    OMDat J.toCore (charOf R F) i Unit (fun _ => A.μ0) := { O with }

end GlobalTheory.BigOn

end
end

