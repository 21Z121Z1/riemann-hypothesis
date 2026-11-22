import Formalism.Bundle0001

-- bundled from Formalism.DefsOC
section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

def Sa (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (x / n - 1)

def MellinSgen : Prop :=
  ∀ (a : ℕ → ℝ) (K : ℝ), (∀ n : ℕ, |a n| ≤ K * ArithmeticFunction.vonMangoldt n) →
    Measurable (Sa a) ∧
    (∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => |Sa a x| * x ^ (-σ - 1)) (Ioi 1)) ∧
    ∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1:ℝ), (Sa a x : ℂ) * (x : ℂ) ^ (-s - 1) =
        LSeries (fun n => (a n : ℂ)) s / (s * (s - 1))

def LSeriesTwistRe : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), (∀ n : ℕ, (χ n).im = 0) →
    ∀ s : ℂ, 1 < s.re →
      LSeries (fun n => ((ArithmeticFunction.vonMangoldt n * (χ n).re : ℝ) : ℂ)) s =
        -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s

def LandauEq : Prop :=
  ∀ (H : ℝ → ℝ) (a b : ℝ), a < b → AEStronglyMeasurable H (volume.restrict (Ioi 1)) →
    (∀ x : ℝ, 1 < x → 0 ≤ H x) →
    (∀ σ : ℝ, b < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1)) →
    ∀ Φ : ℂ → ℂ, (∀ s : ℂ, b < s.re → AnalyticAt ℂ Φ s) →
    (∀ σ : ℝ, a < σ → σ ≤ b → AnalyticAt ℂ Φ σ) →
    (∀ s : ℂ, b < s.re → Φ s = ∫ x in Ioi (1:ℝ), (H x : ℂ) * (x : ℂ) ^ (-s - 1)) →
    ∀ σ : ℝ, a < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1) ∧
      Φ σ = ∫ x in Ioi (1:ℝ), (H x : ℂ) * (x : ℂ) ^ (-(σ : ℂ) - 1)

def LogDerivResidue : Prop :=
  ∀ (f : ℂ → ℂ) (ρ : ℂ), Differentiable ℂ f → (∃ z, f z ≠ 0) →
    Tendsto (fun s => (s - ρ) * (deriv f s / f s)) (𝓝[≠] ρ) (𝓝 (analyticOrderNatAt f ρ : ℂ))

def OrderLogDeriv : Prop :=
  ∀ (ι : Type) [Fintype ι] (P0 : ℂ → ℂ) (P : ι → ℂ → ℂ) (W : ℝ) (w : ι → ℝ) (q : ℂ → ℂ)
    (U : Set ℂ), IsOpen U → Differentiable ℂ P0 → (∀ i, Differentiable ℂ (P i)) →
    (∃ z, P0 z ≠ 0) → (∀ i, ∃ z, P i z ≠ 0) → DifferentiableOn ℂ q U →
    (∀ s ∈ U, P0 s ≠ 0 → (∀ i, P i s ≠ 0) →
        (W : ℂ) * (deriv P0 s / P0 s) - ∑ i, (w i : ℂ) * (deriv (P i) s / P i s) = q s) →
    ∀ s ∈ U, W * (analyticOrderNatAt P0 s : ℝ) = ∑ i, w i * (analyticOrderNatAt (P i) s : ℝ)

end Formalism
end
end

-- bundled from Formalism.StatementCM
section
open Finset

noncomputable section

namespace Formalism

def IsCMType {l : ℕ} (Φ : Finset (ZMod l)ˣ) : Prop := ∀ g : (ZMod l)ˣ, g ∈ Φ ↔ -g ∉ Φ

def dualType {l : ℕ} (Φ : Finset (ZMod l)ˣ) : Finset (ZMod l)ˣ :=
  insert 1 ((Φ.erase 1).image (fun g => -g))

def counts {l : ℕ} (Φ : Finset (ZMod l)ˣ) (σ : (ZMod l)ˣ) : Prop := σ ∉ Φ ∧ σ ≠ -1

def TwoTypes : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 3 ≤ l → ∀ Φ : Finset (ZMod l)ˣ, IsCMType Φ → 1 ∈ Φ →
    IsCMType (dualType Φ) ∧ 1 ∈ dualType Φ ∧
    ∀ σ : (ZMod l)ˣ, σ ≠ 1 → σ ≠ -1 → (counts Φ σ ↔ ¬ counts (dualType Φ) σ)

open Classical in
def HalfTypes : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 3 ≤ l → ∀ σ : (ZMod l)ˣ, σ ≠ 1 → σ ≠ -1 →
    2 * ((Finset.univ.filter (fun Φ : Finset (ZMod l)ˣ => IsCMType Φ ∧ 1 ∈ Φ ∧ counts Φ σ)).card)
      = (Finset.univ.filter (fun Φ : Finset (ZMod l)ˣ => IsCMType Φ ∧ 1 ∈ Φ)).card

open ArithmeticFunction Classical in

def WeightedVonMangoldtSumInClasses (l : ℕ) (Φ : Finset (ZMod l)ˣ) (a b : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊a / b⌋₊,
    if h : IsUnit (n : ZMod l) then
      (if counts Φ h.unit then Λ n * (a / n - b) else 0)
    else 0

def ForcedSumCM : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 3 ≤ l → ∀ Φ : Finset (ZMod l)ˣ, IsCMType Φ → 1 ∈ Φ →
  ∀ a b : ℝ, 0 < a → 0 < b → b ≤ a →
    let R := b * Sz (a / b) - (WeightedVonMangoldtSumInClasses l Φ a b + WeightedVonMangoldtSumInClasses l (dualType Φ) a b)
    0 ≤ R ∧ R ≤ 3 * a / l * Real.log (a / b) * (1 + Real.log (a / b)) + a * Real.log l / (l - 1)

def ForcedSumIdentity : Prop :=
  ∀ a b : ℝ, 0 < b →
    b * Sz (a / b) = a * (Real.log (a / b) - 1 - Real.eulerMascheroniConstant) + b * Gz (a / b)

end Formalism
end
end

-- bundled from Formalism.StatementU
section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

def Gzbar (x : ℝ) : ℝ := ∫ u in (1 : ℝ)..2, u * Gz (x / u)

def wavg {m : ℕ} (xs ω : Fin m → ℝ) (x : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ j, ω j * (x / xs j) * f (xs j)

def ZetaLandau : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gz x ≤ C * x ^ θ) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def ZetaLandauBar : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gzbar x ≤ C * x ^ θ) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def ZetaLandauEps : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gz x ≤ C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def ZetaLandauBarEps : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * Gzbar x ≤ C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def GzLipschitz : Prop :=
  ∃ K : ℝ, ∀ t t' : ℝ, 1 / 2 ≤ t → 1 / 2 ≤ t' → |Gz t| ≤ K * t ∧ |Gz t - Gz t'| ≤ K * |t - t'|

def SampleAverageApprox : Prop :=
  ∃ K : ℝ, ∀ (m : ℕ) (xs ω : Fin m → ℝ) (x η : ℝ), 1 ≤ x → (∀ j, 0 ≤ ω j) → ∑ j, ω j = 1 →
    (∀ j, x / 2 ≤ xs j ∧ xs j ≤ x) → (∀ j, |xs j / x - 1| ≤ η) →
    |wavg xs ω x Gz - Gz x| ≤ K * η * x

def RiemannSumApprox : Prop :=
  ∃ K : ℝ, ∀ (m : ℕ) (x : ℝ), 0 < m → 1 ≤ x →
    |wavg (fun j : Fin m => x / (1 + ((j : ℕ) + 1 : ℝ) / m)) (fun _ => (1 : ℝ) / m) x Gz - Gzbar x|
      ≤ K * x / m

end Formalism
end
end

