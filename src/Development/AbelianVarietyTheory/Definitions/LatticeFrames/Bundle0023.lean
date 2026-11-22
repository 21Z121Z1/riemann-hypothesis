import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch

variable {D : D7}

def ConjBy {G : Type} [Group G] (q : G) (K K' : Subgroup G) : Prop := ∀ k, k ∈ K ↔ q⁻¹ * k * q ∈ K'

def gelfT (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (k : ℕ) (f : GA D V → ℂ) : GA D V → ℂ :=
  (-1 : ℂ) ^ (k + 1) • ∑ idx : Fin (k + 1) → Fin V.rank,
    (List.ofFn fun a : Fin (k + 1) => RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)).reverse.foldr (fun A acc => A acc) f

def wordDer (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (w : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (f : GA D V → ℂ) :
    GA D V → ℂ := w.foldr (fun Z g => RderC θ V τ Z g) f

def meanPair (V : HSp D) (m : Measure (GA D V)) (F E : GA D V → ℂ) : ℂ :=
  ⨍ q, descend (GQ V) (fun h => F h * E h) q ∂autMeasure V m

structure Pass (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χ : (AE D)ˣ →* Circle)
    (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (ν : Measure (WO A B)) (𝓨 : Set (WO A B))
    (μ : D.host.E) (κ : GA D (dblSp A) ≃* StdUnn.G D A.rank)
    (omS : StdUnn.G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank)) : Prop where
  weil : IsWeilDatumO ψ (dblSp A) B 1 χ om
  cov : IsCovolOne (ratL B A) ν 𝓨
  inf : IsInfFam θ
  skew : StdUnn.IsSkew μ
  chart : StdUnn.IsChart A μ κ
  trans : StdUnn.IsTransport ψ θ A B ν 𝓨 om κ omS

end GlobalTheory.RegSch

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7}

namespace Dat

variable {u : D.what₂.Word} (d : Dat D u)

def CommTo : Prop :=
  ∀ j, j ≤ D.R.m → ∃ (U : Col D u 0 →ₗ[ℂ] Col D u 0) (c : ℂ), (∀ ψ ∈ (D.mem u).A.Mram, U ψ ∈ (D.mem u).A.Mram) ∧
    (∀ ψ ∈ (D.mem u).A.Mram, U ψ = 0 → ψ = 0) ∧
    ∀ ψ ∈ (D.mem u).A.Mram, d.S j (GlobalTheory.Core.Rk.colTo (D.mem u).C j ψ) = c • GlobalTheory.Core.Rk.colTo (D.mem u).C j (U ψ)

structure LawsT : Prop where
  base : d.Base
  topOK : CoCpt D.sp.X'
  supp1 : d.Supp1
  supp2 : d.Supp2
  val : d.ValS
  valLast : d.ValLastS
  kerLift : d.KerLift
  perLast : d.PerLast
  topOnto : d.TopOnto
  rdLaw : d.RdLaw
  stab : d.Stab
  comm : d.CommTo
  bot : d.Bot

end Dat

def SeeSawT (D : D7) (u : D.what₂.Word) : Prop := ∃ d : Dat D u, d.LawsT

end GlobalTheory.SeeSaw

end
end

