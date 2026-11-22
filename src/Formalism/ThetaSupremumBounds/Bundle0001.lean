import Mathlib
import Formalism.LogFactorialIndices.Bundle0001

-- bundled from Formalism.ThetaSupremumBounds.StatementA
section
open Finset MeasureTheory
open scoped ComplexConjugate Real Nat

noncomputable section

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)

def nsq {κ : Type} [Fintype κ] (u : κ → ℂ) : ℝ := ∑ x, ‖u x‖ ^ 2

def mono {κ : Type} [Fintype κ] (u : κ → ℂ) (e : κ → ℕ) : ℂ := ∏ x, u x ^ e x

def mfact {κ : Type} [Fintype κ] (e : κ → ℕ) : ℕ := ∏ x, (e x)!

def cj {κ : Type} (u : κ → ℂ) : κ → ℂ := fun x => conj (u x)

def SupShift : Prop :=
  ∀ y e s : ℝ, 0 ≤ y → 0 < e → e < 1 → 0 ≤ s →
    s ^ y * Real.exp (-((1 - e) * s ^ 2) / 2) ≤ (1 - e) ^ (-(y / 2)) * Real.exp (ph y / 2)

def EChoice : Prop :=
  ∀ n : ℝ, 0 ≤ n → (1 - 1 / (n + 1)) ^ (-(n / 2)) ≤ Real.exp (1 / 2)

def GaussCoord : Prop :=
  ∀ (κ : Type) [Fintype κ] (b : κ → ℝ), (∀ x, 0 < b x) →
    Integrable (fun u : κ → ℂ => Real.exp (-∑ x, b x * ‖u x‖ ^ 2)) ∧
    ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2) = ∏ x, π / b x

def SingularIntegral : Prop :=
  ∀ (ι : Type) [Fintype ι] (r : ℕ) (ν : Fin r → ℝ) (s : (ι → ℂ) → Fin r → ℝ),
    (∀ i, 0 ≤ ν i) → (∀ i, Measurable fun u => s u i) → (∀ u i, 0 ≤ s u i) →
    (∀ u, ∑ i, s u i ^ 2 = nsq u) →
    Integrable (fun u : ι → ℂ => (∏ i, s u i ^ ν i) * Real.exp (-(nsq u) / 2)) ∧
    (∫ u : ι → ℂ, (∏ i, s u i ^ ν i) * Real.exp (-(nsq u) / 2)) / π ^ Fintype.card ι ≤
      Real.exp (1 / 2) * (2 * (∑ i, ν i) + 2) ^ Fintype.card ι * Real.exp ((∑ i, ph (ν i)) / 2)

def FockJet : Prop :=
  ∀ (κ : Type) [Fintype κ] (F : (κ → ℂ) → ℂ) (c : (κ → ℕ) → ℂ) (S : ℝ),
    Continuous F → (∀ u, HasSum (fun e => c e * mono u e) (F u)) →
    (∀ u, ‖F u‖ ≤ S * Real.exp (nsq u / 2)) →
    ∀ e : κ → ℕ,
      Integrable (fun u : κ → ℂ => F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) ∧
      ∫ u : κ → ℂ, F u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ) =
        (π : ℂ) ^ Fintype.card κ * (c e * (mfact e : ℂ))

def BlockIntegral : Prop :=
  ∀ (Pl ι : Type) [Fintype Pl] [Fintype ι] (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
    (r : ℕ) (ν : Pl → Fin r → ℝ) (s : Pl → (ι → ℂ) → Fin r → ℝ)
    (Th : (Pl × ι → ℂ) → ℂ) (R : (Pl × ι → ℂ) → W) (S : ℝ),
    (∀ τ i, 0 ≤ ν τ i) → (∀ τ u i, 0 ≤ s τ u i) → (∀ τ u, ∑ i, s τ u i ^ 2 = nsq u) →
    (∀ u, ‖Th u‖ ≤ S * Real.exp (nsq u / 2)) →
    (∀ u, ‖R u‖ ≤ ∏ τ, ∏ i, s τ (fun x => u (τ, x)) i ^ ν τ i) →
    ‖∫ u : Pl × ι → ℂ, (Th u * (Real.exp (-(nsq u)) : ℂ)) • R u‖ /
        π ^ (Fintype.card Pl * Fintype.card ι) ≤
      S * ∏ τ, (Real.exp (1 / 2) * (2 * (∑ i, ν τ i) + 2) ^ Fintype.card ι *
        Real.exp ((∑ i, ph (ν τ i)) / 2))

def BlockBound : Prop :=
  ∀ (Pl ι : Type) [Fintype Pl] [Fintype ι] (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
    [CompleteSpace W]
    (r : ℕ) (ν : Pl → Fin r → ℝ) (n : Pl → ℕ) (s : Pl → (ι → ℂ) → Fin r → ℝ)
    (Th : (Pl × ι → ℂ) → ℂ) (c : (Pl × ι → ℕ) → ℂ) (Rc : (Pl × ι → ℕ) →₀ W)
    (lam : Pl → ℂ) (Om : Pl → ℝ) (S : ℝ),
    (∀ τ i, 0 ≤ ν τ i) → (∀ τ, ∑ i, ν τ i = n τ) →
    (∀ τ u i, 0 ≤ s τ u i) → (∀ τ u, ∑ i, s τ u i ^ 2 = nsq u) →
    Continuous Th → (∀ u, HasSum (fun e => c e * mono u e) (Th u)) →
    (∀ u, ‖Th u‖ ≤ S * Real.exp (nsq u / 2)) →
    (∀ e ∈ Rc.support, ∀ τ, ∑ x, e (τ, x) = n τ) →
    (∀ u, ‖Rc.sum (fun e A => mono (cj u) e • A)‖ ≤ ∏ τ, ∏ i, s τ (fun x => u (τ, x)) i ^ ν τ i) →
    (∀ τ, 0 < Om τ) → (∀ τ, ‖lam τ‖ ^ 2 = (Om τ)⁻¹) →
    ‖Rc.sum (fun e A => (c e * (mfact e : ℂ) * ∏ x, lam x.1 ^ e x) • A)‖ ^ 2 ≤
      S ^ 2 * ∏ τ, ((Om τ)⁻¹ ^ n τ *
        (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * Fintype.card ι) * Real.exp (∑ i, ph (ν τ i))))

def KernelSup : Prop :=
  ∀ (κ Rt : Type) [Fintype κ] [Fintype Rt] (t : Rt → κ → ℂ) (cf : Rt → ℂ) (ka : ℂ)
    (Th0 Th : (κ → ℂ) → ℂ) (B : ℝ), 0 ≤ B →
    (∀ z, ‖Th0 z‖ ^ 2 * Real.exp (-(nsq z)) ≤ B ^ 2) →
    (∀ z, Th z = ka * ∑ a, cf a *
      (Complex.exp (-(∑ x, z x * conj (t a x)) - (nsq (t a) : ℂ) / 2) * Th0 (z + t a))) →
    ∀ z, ‖Th z‖ ≤ ‖ka‖ * (∑ a, ‖cf a‖) * B * Real.exp (nsq z / 2)

def GaussSubmean : Prop :=
  ∀ (κ : Type) [Fintype κ] (F : (κ → ℂ) → ℂ) (c : (κ → ℕ) → ℂ),
    Continuous F → (∀ u, HasSum (fun e => c e * mono u e) (F u)) →
    Integrable (fun w : κ → ℂ => ‖F w‖ ^ 2 * Real.exp (-(2 * nsq w))) →
    ‖F 0‖ ^ 2 ≤ 2 ^ Fintype.card κ *
      ((∫ w : κ → ℂ, ‖F w‖ ^ 2 * Real.exp (-(2 * nsq w))) / π ^ Fintype.card κ)

def ThetaSup : Prop :=
  ∀ (κ : Type) [Fintype κ] (La : AddSubgroup (κ → ℂ)) [Countable La] (D : Set (κ → ℂ))
    (al : La → ℂ) (Th : (κ → ℂ) → ℂ) (c : (κ → ℕ) → ℂ) (hmin : ℝ),
    IsAddFundamentalDomain La D (volume : Measure (κ → ℂ)) →
    0 < hmin → (∀ y ∈ La, y ≠ 0 → π * hmin ≤ nsq y) →
    Continuous Th → (∀ u, HasSum (fun e => c e * mono u e) (Th u)) →
    (∀ y : La, ‖al y‖ = 1) →
    (∀ (y : La) (z : κ → ℂ), Th (z + y) =
      al y * Complex.exp ((∑ x, z x * conj ((y : κ → ℂ) x)) + (nsq (y : κ → ℂ) : ℂ) / 2) * Th z) →
    IntegrableOn (fun u : κ → ℂ => ‖Th u‖ ^ 2 * Real.exp (-(nsq u))) D →
    ∀ z, ‖Th z‖ ^ 2 * Real.exp (-(nsq z)) ≤
      4 ^ Fintype.card κ * (2 + 8 * (Fintype.card κ : ℝ) / hmin) ^ Fintype.card κ *
        ((∫ u in D, ‖Th u‖ ^ 2 * Real.exp (-(nsq u))) / π ^ Fintype.card κ)

end Formalism.DimensionVariation
end
end

-- bundled from Formalism.ThetaSupremumBounds.StatementB
section
open Finset MeasureTheory
open scoped Real Nat

noncomputable section

namespace Formalism.DimensionVariation

def DominanceMono : Prop :=
  ∀ (r : ℕ) (s μ ν : Fin r → ℝ), Antitone s → (∀ i, 0 ≤ s i) → (∀ i, 0 ≤ μ i) → (∀ i, 0 ≤ ν i) →
    (∀ k : ℕ, (∑ i ∈ univ.filter (fun i : Fin r => (i : ℕ) < k), μ i) ≤
      ∑ i ∈ univ.filter (fun i : Fin r => (i : ℕ) < k), ν i) →
    (∑ i, μ i) = ∑ i, ν i →
    (∏ i, s i ^ μ i) ≤ ∏ i, s i ^ ν i

def ClassSchur : Prop :=
  ∀ (Cl Cl' : Type) [Fintype Cl] [Fintype Cl'] (A B : Type)
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
    (γ : Cl → ℝ) (γ' : Cl' → ℝ) (ε : Cl → Cl' → ℂ) (T : Cl → Cl' → A →L[ℂ] B) (tmax : ℝ)
    (fn : Cl → A),
    (∀ L, 0 < γ L ∧ γ L ≤ 1) → (∀ L', 0 < γ' L' ∧ γ' L' ≤ 1) → (∀ L L', ‖ε L L'‖ = 1) →
    (∀ L L', ‖T L L'‖ ^ 2 ≤ tmax) →
    (∑ L', γ' L' * ‖∑ L, ((γ L : ℂ) * ε L L') • T L L' (fn L)‖ ^ 2) ≤
      ((Fintype.card Cl : ℝ) * (Fintype.card Cl' : ℝ)) * tmax * ∑ L, γ L * ‖fn L‖ ^ 2

def HminAMGM : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (β : Pl → ℝ) (v : ℝ), 0 < v → (∀ τ, 0 ≤ β τ) →
    ((2 * v) ^ Fintype.card Pl)⁻¹ ≤ ∏ τ, β τ →
    (Fintype.card Pl : ℝ) / v ≤ 2 * ∑ τ, β τ

def SupTailIntegral : Prop :=
  ∀ (g : ℕ) (h : ℝ), 1 ≤ g → 0 < h →
    (∫ u in Set.Ioi (0 : ℝ), (1 + 4 * u / h) ^ g * (π * Real.exp (-(π * u)))) ≤
      2 ^ (g - 1) * (1 + (4 / h) ^ g * (g ! : ℝ) / π ^ g)

def SupNumeric : Prop :=
  ∀ (g : ℕ) (h : ℝ), 1 ≤ g → 0 < h →
    (2 : ℝ) ^ g * (2 ^ g * (2 ^ (g - 1) * (1 + (4 / h) ^ g * (g ! : ℝ) / π ^ g))) ≤
      4 ^ g * (2 + 8 * (g : ℝ) / h) ^ g

def OriginColumn : Prop :=
  ∀ u e n0 n1 t i a : ℝ, n1 = n0 + t + 1 →
    (u - (n0 + 1 - 2 * i) / 2) + (e - n1 / 2) = (u + e) - (n0 + n1 + 1 - 2 * i) / 2 ∧
    (u - (n1 + 1 - 2 * i) / 2) + (e - n0 / 2) = (u + e) - (n0 + n1 + 1 - 2 * i) / 2 ∧
    (e - n0 / 2) - (e - n1 / 2) = (t + 1) / 2 ∧
    ((-e + (t + 2 - 2 * a) / 2) - (n1 + 1 - 2 * (n0 + a)) / 2) + (e - n0 / 2) = 0

def OriginBlock : Prop :=
  ∀ k t j j' a e e' : ℝ,
    ((-e' + (t + 2 - 2 * a) / 2) + e) -
      ((k + (j - 1) * (t + 1)) + (k + j * (t + 1)) + 1 - 2 * (k + (j' - 1) * (t + 1) + a)) / 2 =
      (e - e') - (j - j') * (t + 1)

def SignatureCount : Prop :=
  ∀ k m j : ℝ, 1 ≤ j → j ≤ m →
    -k + (k + j - 1) - (m - j) = 2 * j - 1 - m ∧ |((k + j - 1) - (m - j)) - k| ≤ m

def RowsOffTop : Prop :=
  ∀ (k : ℕ) (c : Fin k → ℝ) (w blk Cc N S m tt η C0 : ℝ),
    (∀ i, |c i| ≤ Cc * (N + S)) → 0 ≤ blk → blk ≤ m * (tt + 1) * η →
    0 ≤ w → 0 ≤ N → 0 ≤ S → 1 ≤ C0 → Cc ≤ C0 →
    ∃ δ : ℝ, (∑ i, (w + c i)) + blk = (k : ℝ) * w + δ ∧
      |δ| ≤ C0 * (w + (k : ℝ) * (N + S) + m * (tt + 1) * η)

def RowsTop : Prop :=
  ∀ (k2 : ℕ) (c : Fin (k2 + 1) → ℝ) (a w rk blk Cc N S m tt η b' x C0 : ℝ),
    (∀ i, |c i| ≤ Cc * (N + S)) → 0 ≤ blk → blk ≤ m * (tt + 1) * η →
    0 ≤ rk → rk ≤ 2 * b' / x → 1 ≤ x →
    0 ≤ w → 0 ≤ N → 0 ≤ S → 1 ≤ C0 → Cc ≤ C0 →
    ∃ δ : ℝ, a + (∑ i, (w + c i)) + rk + blk = a + ((k2 + 2 : ℕ) : ℝ) * w + δ ∧
      |δ| ≤ C0 * (w + ((k2 + 2 : ℕ) : ℝ) * (N + S) + m * (tt + 1) * η + ((k2 + 2 : ℕ) : ℝ) * b')

end Formalism.DimensionVariation
end
end

-- bundled from Formalism.ThetaSupremumBounds.StatementC
section
open Finset
open scoped Real

noncomputable section

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)

def SizeAtEmbedding : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (r g0 : ℕ) (ν : Pl → Fin r → ℝ) (n : Pl → ℕ) (Om : Pl → ℝ)
    (Ksq kc Msq Th0sq hh : ℝ),
    0 < Ksq → 0 < kc → 0 < Msq → 0 < Th0sq → 0 < hh → (∀ τ, 0 < Om τ) →
    Ksq ≤ hh * ((kc ^ 2 * Msq * Th0sq) * ∏ τ, ((Om τ)⁻¹ ^ n τ *
      (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * g0) * Real.exp (∑ i, ph (ν τ i))))) →
    Real.log Ksq ≤ (∑ τ, ((∑ i, ph (ν τ i)) - (n τ : ℝ) * Real.log (Om τ))) + Real.log Th0sq +
      (Real.log Msq + 2 * Real.log kc + (∑ τ, (1 + 2 * (g0 : ℝ) * Real.log (2 * (n τ : ℝ) + 2))) +
        Real.log hh)

def DiHyp (J Pl : Type) [Fintype J] [Fintype Pl] (hK eK : J → ℝ) (phν nν : J → Pl → ℝ)
    (logOm f m N L La dC C0 : ℝ) : Prop :=
  (∀ j, hK j ≤ ∑ ρ, (phν j ρ - nν j ρ * logOm) + eK j) ∧
  (∀ j, eK j ≤ C0 * (f * N ^ 2 * (La + dC) + f * m ^ 3 * N ^ 2 * L))

def DiCondition : Prop :=
  ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ) (g0 : J → ℝ)
    (logK MainNotions : J → Emb → ℝ) (logOmτ : Pl → Emb → ℝ) (logth0 : Emb → ℝ) (logh logh' hK : J → ℝ)
    (logOm v f m N L La dC logT logg C2 C3 C4 c5 c6 C7 C8 C0 : ℝ),

    (∀ j s, logK j s ≤
      (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
      (Fintype.card Pl : ℝ) * g0 j * logth0 s +
      ((Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
        2 * MainNotions j s + (∑ τ, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) +
        (logh j + logh' j))) →

    (∀ j, hK j = (∑ s, logK j s) / (Fintype.card Emb : ℝ)) →

    (∀ τ, (∑ s, logOmτ τ s) / (Fintype.card Emb : ℝ) = logOm) →

    (∀ j s, MainNotions j s ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) →
    (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ C3 * L →
    (∀ j, logh j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, logh' j ≤ C4 * f * N ^ 2 * (L + logT + logg)) →

    (Fintype.card Pl : ℝ) ≤ f → (∀ j, 0 ≤ g0 j ∧ g0 j ≤ N ^ 2) →
    1 ≤ m → 1 ≤ N → 0 ≤ L → L ≤ La → 1 ≤ dC →
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) ≤ c5 * La) →
    (∀ j τ, Real.log (2 * (∑ i, ν j τ i) + 2) ≤ c6 * La) →
    logT ≤ C7 * m * L → logg ≤ C8 * L →
    0 ≤ C2 → 0 ≤ C3 → 0 ≤ C4 → 0 ≤ c5 → 0 ≤ c6 → 0 ≤ C7 → 0 ≤ C8 →
    C3 + c5 + 2 * c6 + 1 + 2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8) ≤ C0 →
    ∃ eK : J → ℝ,
      DiHyp J Pl hK eK (fun j ρ => ∑ i, ph (ν j ρ i)) (fun j ρ => ∑ i, ν j ρ i)
        logOm f m N L La dC C0

def MsqBound : Prop :=
  ∀ (g : ℕ) (h v : ℝ), 0 < v → 1 / v ≤ h →
    (4 : ℝ) ^ g * (2 + 8 * (g : ℝ) / h) ^ g ≤ (8 + 32 * (g : ℝ) * v) ^ g

def StepDiProd : Prop :=
  ∀ (J Pl Emb : Type) [Fintype J] [Fintype Pl] [Fintype Emb] [Nonempty Emb] (r : ℕ)
    (ν : J → Pl → Fin r → ℝ) (n : J → Pl → ℕ) (g0 : J → ℕ)
    (Ksq kc : J → Emb → ℝ) (Om : Pl → Emb → ℝ) (th0sq : Emb → ℝ) (hcl hcl' hK : J → ℝ)
    (logOm v f m N L La dC logT logg C2 C3 C4 c5 c6 C7 C8 C0 : ℝ),
    (∀ j τ, ∑ i, ν j τ i = (n j τ : ℝ)) →
    (∀ j s, 0 < Ksq j s) → (∀ j s, 0 < kc j s) → (∀ τ s, 0 < Om τ s) → (∀ s, 0 < th0sq s) →
    (∀ j, 0 < hcl j) → (∀ j, 0 < hcl' j) → 0 < v →

    (∀ j s, Ksq j s ≤ (hcl j * hcl' j) *
      ((kc j s ^ 2 * (8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v) ^ (Fintype.card Pl * g0 j) *
          th0sq s ^ (Fintype.card Pl * g0 j)) *
        ∏ τ, ((Om τ s)⁻¹ ^ n j τ *
          (Real.exp 1 * (2 * (n j τ : ℝ) + 2) ^ (2 * g0 j) * Real.exp (∑ i, ph (ν j τ i)))))) →
    (∀ j, hK j = (∑ s, Real.log (Ksq j s)) / (Fintype.card Emb : ℝ)) →
    (∀ τ, (∑ s, Real.log (Om τ s)) / (Fintype.card Emb : ℝ) = logOm) →
    (∀ j s, Real.log (kc j s) ≤ C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) →
    (∑ s, Real.log (th0sq s)) / (Fintype.card Emb : ℝ) ≤ C3 * L →
    (∀ j, Real.log (hcl j) ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (∀ j, Real.log (hcl' j) ≤ C4 * f * N ^ 2 * (L + logT + logg)) →
    (Fintype.card Pl : ℝ) ≤ f → (∀ j, (g0 j : ℝ) ≤ N ^ 2) →
    1 ≤ m → 1 ≤ N → 0 ≤ L → L ≤ La → 1 ≤ dC →
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v) ≤ c5 * La) →
    (∀ j τ, Real.log (2 * (n j τ : ℝ) + 2) ≤ c6 * La) →
    logT ≤ C7 * m * L → logg ≤ C8 * L →
    0 ≤ C2 → 0 ≤ C3 → 0 ≤ C4 → 0 ≤ c5 → 0 ≤ c6 → 0 ≤ C7 → 0 ≤ C8 →
    C3 + c5 + 2 * c6 + 1 + 2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8) ≤ C0 →
    ∃ eK : J → ℝ,
      DiHyp J Pl hK eK (fun j ρ => ∑ i, ph (ν j ρ i)) (fun j ρ => ∑ i, ν j ρ i)
        logOm f m N L La dC C0

def PeriodValue : Prop :=
  ∀ d v rdE A1 Z LL0 p_power_smul_sub_sum logOmK logOm : ℝ, 0 < d → 0 < v → rdE = 2 * v →
    Z = Real.log (2 / Real.sqrt d) + (A1 + Real.log π) →
    Z = Real.log (2 * π) + LL0 →
    LL0 = -p_power_smul_sub_sum - Real.log (d / π) + Real.eulerMascheroniConstant + Real.log 2 →
    logOmK = A1 →
    logOm = logOmK - Real.log rdE + Real.log (Real.sqrt d) →
    A1 = LL0 + Real.log d / 2 ∧
    logOmK = Real.eulerMascheroniConstant + Real.log (2 * π / Real.sqrt d) - p_power_smul_sub_sum ∧
    logOm = Real.eulerMascheroniConstant + Real.log (π / v) - p_power_smul_sub_sum

end Formalism.DimensionVariation
end
end

