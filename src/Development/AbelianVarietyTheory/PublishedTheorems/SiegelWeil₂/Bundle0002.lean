import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

open GlobalTheory.RegSch

def EisensteinResidue : Prop :=
  ∀ (D : D7) (V V₀ : HSp D) (r : ℕ) (d : HypDec V V₀ r), IsAniso V₀ → 0 < r →
  ∀ (l : Lvl V) (l₀ : Lvl V₀), l.Good → l₀.Good → Compat d l l₀ → HasIw d l.K →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ h, PoleLE (sphericalEisensteinSeriesOnGroup d l.K h) (rhoH V r) 1 ∧ ResidueAt (sphericalEisensteinSeriesOnGroup d l.K h) (rhoH V r) κ

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentityResidues
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

open GlobalTheory.RegSch

def FirstTermIdentityResidues : Prop :=
  ∀ (D : D7) (n : ℕ) (T T' : HSp D) (t : ℕ) (d : HypDec T T' t),
    T.rank + T'.rank = 2 * n → T'.rank < T.rank → 0 < T'.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ T.rank →
  ∀ (μ : Measure (Mx D T.rank n)) (𝓕 : Set (Mx D T.rank n)), IsCovolOne (ratMx D T.rank n) μ 𝓕 →
  ∀ (μ' : Measure (Mx D T'.rank n)) (𝓕' : Set (Mx D T'.rank n)), IsCovolOne (ratMx D T'.rank n) μ' 𝓕' →
  ∀ (μ₁ : Measure (Mx D t n)) (𝓕₁ : Set (Mx D t n)), IsCovolOne (ratMx D t n) μ₁ 𝓕₁ →
  ∀ (ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ T.rank n)) (ω' : StdUnn.G D n →* Module.End ℂ (schwartzA θ T'.rank n)),
    StdUnn.IsWeilSch ψ χ θ T μ ω → StdUnn.IsWeilSch ψ χ θ T' μ' ω' →
  ∀ H : StdUnn.G D n → ℝ≥0, StdUnn.IsHeight H →
  ∀ (l : Lvl T) (l' : Lvl T'), l.Good → l'.Good → Compat d l l' → HasIw d l.K →
  ∀ ν : Measure l.K, ν.IsHaarMeasure → IsProbabilityMeasure ν →
  ∀ m : Measure (GA D T'), m.IsHaarMeasure →
  ∀ lr : D.what₂.Tau → ℝ, StdUnn.HasRealPar ψ θ lr →
  ∀ s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ τ, IsCartanInv (gramAt D T τ) (s τ)) →
    (∀ k ∈ l.K, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T k) * s τ = s τ * compAt θ τ (Formalism.L2.Theta.mt T k)) →
    (IsAniso T' → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ Φ : schwartzA θ T.rank n, Φ.1 ∈ StdUnn.fockA θ T n lr s → KFin ω Φ →
      ∀ Φ' : schwartzA θ T'.rank n, Φ'.1 = ikS d μ₁ (projS ν Φ.1) → ∀ g (A : ℂ),
        ResidueAt (eisS ω H Φ g) (StdUnn.s0 T n) A → A = κ * StdUnn.thetaInt ω' m Φ' g) ∧
    ∀ (T₀ : HSp D) (r' : ℕ) (d₀ : HypDec T' T₀ r'), IsAniso T₀ → 0 < r' →
    ∀ l₀ : Lvl T₀, l₀.Good → Compat d₀ l' l₀ → HasIw d₀ l'.K →
    ∀ (τ : D.what₂.Tau) (zG zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ), IsRegS τ ω' d₀ l'.K zG zH P →
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ Φ : schwartzA θ T.rank n, Φ.1 ∈ StdUnn.fockA θ T n lr s → KFin ω Φ →
        ∀ Φ' Ψ : schwartzA θ T'.rank n, Φ'.1 = ikS d μ₁ (projS ν Φ.1) → Ψ.1 = cenH θ τ T' zH Φ'.1 → ∀ g (A B : ℂ),
          ResidueAt (eisS ω H Φ g) (StdUnn.s0 T n) A → ResidueAt (regIntS ω' d₀ l'.K m P Ψ g) (rhoH T' r') B → A = κ * B

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentitySchrodinger
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

open GlobalTheory.RegSch

def FirstTermIdentitySchrodinger : Prop :=
  ∀ (D : D7) (n : ℕ) (T T' : HSp D) (t : ℕ) (d : HypDec T T' t),
    T.rank + T'.rank = 2 * n → T'.rank < T.rank → 0 < T'.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ T.rank →
  ∀ (μ : Measure (Mx D T.rank n)) (𝓕 : Set (Mx D T.rank n)), IsCovolOne (ratMx D T.rank n) μ 𝓕 →
  ∀ (μ' : Measure (Mx D T'.rank n)) (𝓕' : Set (Mx D T'.rank n)), IsCovolOne (ratMx D T'.rank n) μ' 𝓕' →
  ∀ (μ₁ : Measure (Mx D t n)) (𝓕₁ : Set (Mx D t n)), IsCovolOne (ratMx D t n) μ₁ 𝓕₁ →
  ∀ (ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ T.rank n)) (ω' : StdUnn.G D n →* Module.End ℂ (schwartzA θ T'.rank n)),
    StdUnn.IsWeilSch ψ χ θ T μ ω → StdUnn.IsWeilSch ψ χ θ T' μ' ω' →
  ∀ H : StdUnn.G D n → ℝ≥0, StdUnn.IsHeight H →
  ∀ (l : Lvl T) (l' : Lvl T'), l.Good → l'.Good → Compat d l l' → HasIw d l.K →
  ∀ ν : Measure l.K, ν.IsHaarMeasure → IsProbabilityMeasure ν →
  ∀ m : Measure (GA D T'), m.IsHaarMeasure →
    (IsAniso T' → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ Φ : schwartzA θ T.rank n, KFin ω Φ →
      ∀ Φ' : schwartzA θ T'.rank n, Φ'.1 = ikS d μ₁ (projS ν Φ.1) → ∀ g,
        ResidueAt (eisS ω H Φ g) (StdUnn.s0 T n) (κ * StdUnn.thetaInt ω' m Φ' g)) ∧
    ∀ (T₀ : HSp D) (r' : ℕ) (d₀ : HypDec T' T₀ r'), IsAniso T₀ → 0 < r' →
    ∀ l₀ : Lvl T₀, l₀.Good → Compat d₀ l' l₀ → HasIw d₀ l'.K →
      ∃ (τ : D.what₂.Tau) (zG zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ), IsRegS τ ω' d₀ l'.K zG zH P ∧
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ Φ : schwartzA θ T.rank n, KFin ω Φ →
        ∀ Φ' Ψ : schwartzA θ T'.rank n, Φ'.1 = ikS d μ₁ (projS ν Φ.1) → Ψ.1 = cenH θ τ T' zH Φ'.1 → ∀ g,
          ∃ B : ℂ, ResidueAt (regIntS ω' d₀ l'.K m P Ψ g) (rhoH T' r') B ∧
            ResidueAt (eisS ω H Φ g) (StdUnn.s0 T n) (κ * B)

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.RegularisingElement
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

open GlobalTheory.RegSch

def RegularisingElement : Prop :=
  ∀ (D : D7) (n : ℕ) (V V₀ : HSp D) (r : ℕ) (d : HypDec V V₀ r), IsAniso V₀ → 0 < r → V.rank ≤ n →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank →
  ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
  ∀ ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n), StdUnn.IsWeilSch ψ χ θ V μ ω →
  ∀ (l : Lvl V) (l₀ : Lvl V₀), l.Good → l₀.Good → Compat d l l₀ → HasIw d l.K →
  ∀ τ : D.what₂.Tau, ∃ (zG zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ),
    IsRegS τ ω d l.K zG zH P ∧ P.eval (rhoH V r : ℂ) ≠ 0

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

open GlobalTheory.Eis

def SiegelEisensteinSimplePole : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a →
    HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
    ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b →
    ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ →
      V.rank < b → EisPoleLE V (flat V a φ s₁) (((b : ℂ) - V.rank) / 2) 1

end GlobalTheory.Published

end
end

