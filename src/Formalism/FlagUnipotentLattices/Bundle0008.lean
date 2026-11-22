import Formalism.FlagUnipotentLattices.Bundle0006
import Formalism.FlagUnipotentLattices.Bundle0003
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LatticeDataCounting

-- bundled from Formalism.FlagUnipotentLattices.CuspidalityThreshold
section
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder

noncomputable section

namespace Formalism.HermitianLatticeCounting.S7

open Formalism.NuclearRankWeightBounds.D (lead hs q0)

def NearTotalAbs : Prop :=
  ∀ c : ℝ, 0 < c → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ C Cg : ℝ, 1 ≤ C → 1 ≤ Cg → ∃ n₀ : ℕ,
    ∀ (n q J a f : ℕ) (rd g b : ℝ), n₀ ≤ n → q ^ 2 ≤ n → 1 ≤ a → a ≤ J → J ≤ q → 1 ≤ f →
    Real.log f ≤ Real.sqrt n → 2 ≤ b → 1 ≤ g → g ≤ b ^ Cg → 1 ≤ rd →
    Real.log (Real.log rd) ≤ n → Real.log (Real.log b) ≤ c₁ * n * f * Real.log n →
    (2 : ℝ) ^ q * (2 * Real.exp (-(c * J * n * f * Real.log n)))
        * (C * f * (q : ℝ) ^ 2 * Real.log (Ydat n f rd g b)) ^ a ≤
      Real.exp (-(c₂ * n * f * Real.log n))

def CuspidalityThreshold : Prop :=
  ∀ (n q : ℕ) (h : ℝ), 1 ≤ q → 2 * q ≤ n → 40 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h →
    2 * (n : ℝ) * Real.sqrt (2 * (q : ℝ)) + 2 * (n : ℝ) ^ 2 < h / 8 / Real.sqrt (2 * (q : ℝ))

def ThreshCuspOp : Prop :=
  ∀ (n q : ℕ) (h : ℝ), 1 ≤ q →
    (16 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) < h ↔ 2 * (n : ℝ) * q < h / 8 / Real.sqrt q) ∧
    (q ≤ n → 40 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h →
      2 * (n : ℝ) ^ 2 + 2 * (n : ℝ) * q < h / 8 / Real.sqrt q ∧
        16 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) < h)

def ThreshCountOp : Prop :=
  ∀ (n q : ℕ) (h : ℝ), 32 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h →
    16 * (Real.sqrt 2 * (n : ℝ) ^ 2) * Real.sqrt (2 * (q : ℝ)) ≤ h

def DecExpOp : Prop :=
  ∀ (h : ℝ) (q : ℕ) (d t : ℝ), 0 ≤ h → 0 ≤ d → Real.sqrt 2 * d ≤ t →
    decExp h q (Real.sqrt 2 * d) = h / 8 * min (2 * d ^ 2) (d / Real.sqrt q) ∧
      decExp h q (Real.sqrt 2 * d) ≤ decExp h q t

open Classical in

def AllSumOp : Prop :=
  ∀ (ι Γ : Type) [Fintype ι] [Nonempty ι] (S : Finset Γ) (d : Γ → ι → ℝ) (A h : ℝ) (n q : ℕ),
    1 ≤ q → 1 ≤ n → 0 ≤ A → 32 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h →
    (∀ γ ∈ S, ∀ v, 0 ≤ d γ v) →
    (∀ r : ι → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, d γ v ≤ r v).card : ℝ) ≤ A * Real.exp (2 * (n : ℝ) ^ 2 * ∑ v, r v)) →
    ∑ γ ∈ S, ∏ v, Real.exp (-(h / 8 * min (2 * d γ v ^ 2) (d γ v / Real.sqrt q))) ≤
      A * (2 * Real.exp (2 * (n : ℝ) ^ 2)) ^ Fintype.card ι

def OpHS : Prop :=
  ∀ (N : ℕ) (ep : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ), X.IsHermitian →
    (∀ a b, ep a = ep b → X a b = 0) →
    ((hs X ^ 2 / 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X.conjTranspose * X).PosSemidef ∧
      ∀ ρ : ℝ, ((ρ ^ 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ) - X.conjTranspose * X).PosSemidef →
        hs X ^ 2 ≤ 2 * (q0 ep : ℝ) * ρ ^ 2

open scoped Matrix.Norms.L2Operator in

def OpNormPsd : Prop :=
  ∀ (N : ℕ) (W : Matrix (Fin N) (Fin N) ℂ) (ρ : ℝ), 0 ≤ ρ →
    (((ρ ^ 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ) - W.conjTranspose * W).PosSemidef ↔ ‖W‖ ≤ ρ)

open scoped Matrix.Norms.L2Operator in

def OpHSNorm : Prop :=
  ∀ (N : ℕ) (ep : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ), X.IsHermitian →
    (∀ a b, ep a = ep b → X a b = 0) →
    Real.sqrt 2 * ‖X‖ ≤ hs X ∧ hs X ≤ Real.sqrt (2 * (q0 ep : ℝ)) * ‖X‖

def PZero : Prop :=
  ∀ (N : ℕ) (ep : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ), q0 ep = 0 →
    (∀ a b, ep a = ep b → X a b = 0) → X = 0

def SupportLevel : Prop :=
  ∀ (G : Type) [Group G] (e : G → ℂ) (Kg : Subgroup G) (U : Set G), e 1 ≠ 0 →
    (∀ k ∈ Kg, ∀ x, e (k * x) = e x) → (∀ x, e x ≠ 0 → x ∈ U) → (Kg : Set G) ⊆ U

def LevelForces : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n g : ℕ), 1 ≤ n → 2 < p →
    (∀ γ : Matrix (Fin n) (Fin n) ℤ_[p], IsUnit γ → (∀ i j, (g : ℤ_[p]) ∣ (γ - 1) i j) →
      ∀ i j, (p : ℤ_[p]) ∣ ((γ - 1) ^ n) i j) →
    p ∣ g

def KernelZero : Prop :=
  ∀ (K H : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (κ : K → H →L[ℂ] H), Continuous κ →
    (∀ φ : K → H, Continuous φ → (∫ k, κ k (φ k) ∂μ) = 0) → ∀ k, κ k = 0

def RhoNorm : Prop :=
  ∀ n : ℕ, ∑ i ∈ range n, (((n : ℝ) - 1) / 2 - i) ^ 2 = (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 12

def CasimirDiff : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (lam rn rc rho mu : V) (P : ℝ),
    ‖mu - (lam + rn - rc)‖ ≤ Real.sqrt 2 * P →
    ‖mu + rc‖ ^ 2 - ‖rc‖ ^ 2 - (‖lam‖ ^ 2 - ‖rho‖ ^ 2) ≤
        (‖lam‖ + ‖rn‖ + Real.sqrt 2 * P) ^ 2 - ‖lam‖ ^ 2 + ‖rho‖ ^ 2 ∧
      2 * (‖mu + rc‖ ^ 2 - ‖rc‖ ^ 2) - (‖lam‖ ^ 2 - ‖rho‖ ^ 2) ≤
        2 * (‖lam‖ + ‖rn‖ + Real.sqrt 2 * P) ^ 2 - ‖lam‖ ^ 2 + ‖rho‖ ^ 2

def StepBound : Prop :=
  ∀ (n P : ℕ) (b L rn rho2 : ℝ), 1 ≤ n → Real.sqrt n ≤ b ^ 2 → 0 ≤ L → L ≤ Real.sqrt n * b ^ 2 →
    0 ≤ rn → rn ≤ 2 * Real.sqrt ((n : ℝ) ^ 3 / 12) → rho2 ≤ (n : ℝ) ^ 3 / 12 →
    (L + rn + Real.sqrt 2 * P) ^ 2 - L ^ 2 + rho2 ≤ (3 * (n : ℝ) * (b ^ 2 + (P : ℝ) * n)) ^ 2 ∧
      2 * (L + rn + Real.sqrt 2 * P) ^ 2 - L ^ 2 + rho2 ≤ (3 * (n : ℝ) * (b ^ 2 + (P : ℝ) * n)) ^ 2

def EntriesNorm : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (B : ℝ), (∀ i, |lam i| ≤ B) →
    Real.sqrt (∑ i, lam i ^ 2) ≤ Real.sqrt n * B ∧ ∀ (i j : Fin n) (h : ℝ), h ≤ lam i - lam j → h ≤ 2 * B

def CubeMult : Prop :=
  ∀ (C : ℝ) (n f : ℕ) (b₁ τ : ℝ), 1 ≤ C → 0 ≤ b₁ → 0 < τ →
    (4 / (1 / (C * n * b₁))) ^ (n ^ 2 * f) * (C * Real.sqrt n / τ ^ 2) ^ (2 * n ^ 2 * f) ≤
      (4 * C * (n : ℝ) ^ 2 * b₁) ^ (n ^ 2 * f) * (4 * C / τ) ^ (4 * n ^ 2 * f)

def LevelIndex : Prop :=
  ∀ (R : Type) [CommRing R] [Finite R] (n : ℕ),
    Nat.card (Matrix (Fin n) (Fin n) R)ˣ ≤ Nat.card R ^ (n ^ 2)

def VolLevel : Prop :=
  ∀ (C : ℝ) (n f : ℕ) (rd g b volG volK : ℝ), 1 ≤ n → 1 ≤ f → 1 ≤ rd → 1 ≤ g → 2 ≤ b →
    0 < volK → volG ≤ Ydat n f rd g b ^ (C * (n : ℝ) ^ 2 * f) → volK⁻¹ ≤ g ^ (2 * n ^ 2 * f) →
    volG / volK ≤ Ydat n f rd g b ^ ((C + 2) * (n : ℝ) ^ 2 * f)

def DeepChainV : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ C' : ℝ, 1 ≤ C' ∧
    ∀ (n q f : ℕ) (rd g b τ₁ τs ρ Kxx Bs D volG volK : ℝ), 1 ≤ n → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ f →
    1 ≤ rd → 1 ≤ g → 2 ≤ b → 0 < τ₁ → τ₁ < τs → 0 ≤ D → 0 < volK → 0 ≤ volG → 0 ≤ ρ →
    ρ ≤ C * (n : ℝ) ^ 2 * f * g * rd * (2 * τ₁) ^ ((1 : ℝ) / q) →
    Kxx ≤ (C * ρ * (n : ℝ) ^ 2 * f * b1 n q f b) ^ (2 * P0 n q f) * Bs →
    Bs ≤ D * volK⁻¹ * (C * (n : ℝ) ^ 2 * b1 n q f b) ^ (n ^ 2 * f) * (C / τ₁) ^ (4 * n ^ 2 * f) →
    volG / volK ≤ Ydat n f rd g b ^ (C * (n : ℝ) ^ 2 * f) →
    volG * Kxx ≤ D * Ydat n f rd g b ^ (C' * (n : ℝ) ^ 2 * f)
      * (C' * (n : ℝ) ^ 4 * (f : ℝ) ^ 2 * g * rd * b1 n q f b) ^ (16 * q * n ^ 2 * f)
      * τs ^ (12 * n ^ 2 * f)

end Formalism.HermitianLatticeCounting.S7
end
end

-- bundled from Formalism.FlagUnipotentLattices.HeightConditionFromCubic
section
open Finset

noncomputable section

namespace Formalism.HermitianLatticeCounting.S8

def SizeAR : Prop :=
  (∀ x : ℝ, 1801 ≤ x → 120 * x * (x / 2 * Real.sqrt (x / 2)) ≤ x ^ 3) ∧
  ∀ k m t j : ℕ, 1801 ≤ (k + m - 1) + t → 1 ≤ j →
    120 * ((k + m - 1 + j * t : ℕ) : ℝ) * (((k + m - 1 + j * t : ℕ) : ℝ) / 2 * Real.sqrt (((k + m - 1 + j * t : ℕ) : ℝ) / 2))
      ≤ ((k + m - 1 + j * t : ℕ) : ℝ) ^ 3

def HeightConditionFromCubic : Prop :=
  ∀ k m t : ℕ, 1 ≤ k → 2 ≤ m → (k + m - 1) + 5 ≤ t →
    3 * ((k + m - 1 : ℕ) : ℝ) < Mrk k m t ∧ 54 * ((k + m - 1 : ℕ) : ℝ) ^ 3 < 2 * Mrk k m t ^ 3 ∧
    ∀ h : ℝ, 2 * Mrk k m t ^ 3 + t + 3 < h →
      43 * (((k + m - 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((k + m - 1 : ℕ) : ℝ)) ≤ h

def ParamDCosetMinus : Prop :=
  ∀ (k m t j : ℕ) (v : List ℝ) (b e : ℕ → ℝ), 1 ≤ k → Even m → Odd t →
    (∀ x ∈ v, ∃ z : ℤ, x = (z : ℝ) + (k : ℝ) / 2) → (∀ i < m, ∃ z : ℤ, b i = (z : ℝ) + (k : ℝ) / 2) →
    (∀ i < m, ∃ z : ℤ, e i = (z : ℝ) + (k : ℝ) / 2) →
    ∀ x ∈ paramD t j m v b e, Odd j → ∃ z : ℤ, x - 1 / 2 - (((k + m - 1 + j * t : ℕ) : ℝ) - 1) / 2 = (z : ℝ)

def hcCompact (a t' : ℕ) (c : ℝ) (ν : ℕ → ℤ) (i : ℕ) : ℝ :=
  (ν i : ℝ) + ((a : ℝ) + ((a + t' : ℕ) : ℝ) + 1) / 2 - (i : ℝ) + c

def CompactPairParam : Prop :=
  ∀ (a t' : ℕ) (c : ℝ),
    (List.range t').map (fun l : ℕ => ((a : ℝ) + ((a + t' : ℕ) : ℝ) + 1) / 2 - ((a + 1 + l : ℕ) : ℝ) + c) = blockP c t' ∧
    (∀ ν : ℝ, (c + ((t' : ℝ) + 1) / 2 ≤ ν + ((a : ℝ) + ((a + t' : ℕ) : ℝ) + 1) / 2 - a + c ↔ 0 ≤ ν)) ∧
    (∀ ν : ℕ → ℤ,
      (∀ i : ℕ, hcCompact a t' c ν i - (c + ((t' : ℝ) + 1) / 2) = ((ν i + (a : ℤ) - (i : ℤ) : ℤ) : ℝ)) ∧
      (∀ i : ℕ, ν (i + 1) ≤ ν i ↔ hcCompact a t' c ν (i + 1) < hcCompact a t' c ν i) ∧
      (0 ≤ ν a ↔ c + ((t' : ℝ) + 1) / 2 ≤ hcCompact a t' c ν a)) ∧
    (∀ α : ℕ → ℝ, (∀ i, ∃ z : ℤ, α i = c + ((t' : ℝ) + 1) / 2 + (z : ℝ)) → ∃! ν : ℕ → ℤ, ∀ i, α i = hcCompact a t' c ν i)

def GArithC : Prop :=
  ∀ k m t : ℕ, 1 ≤ k → 2 ≤ m → (k + m - 1) + 5 ≤ t → 1801 ≤ (k + m - 1) + t →
    ((k + m - 1 : ℕ) : ℝ) + (t : ℝ) ≤ Mrk k m t ∧
    40 * Real.sqrt ((m : ℝ) / 2) ≤ Mrk k m t ∧
      ∀ n q₀ : ℝ, 0 ≤ n → n ≤ Mrk k m t → 0 ≤ q₀ → q₀ ≤ (m : ℝ) / 2 →
        40 * n ^ 2 * Real.sqrt q₀ ≤ Mrk k m t ^ 3

def UnitIntegrableArithmetic : Prop :=
  ∀ n q : ℝ, 1 ≤ n → 1 ≤ q →
    16 * (n - 1) * q < 120 * n * (q * Real.sqrt q) ∧
    ∀ h : ℝ, 120 * n * (q * Real.sqrt q) ≤ h → 8 * 0 * Real.sqrt q + 16 * (n - 1) * q < h

def CorConsts : Prop :=
  ∀ n q : ℝ, 0 ≤ q → q ≤ n / 2 →
    120 * n * (q * Real.sqrt q) ≤ 42.5 * (n ^ 2 * Real.sqrt n) ∧
    (2 ≤ n →
      8 * (n ^ 2 + 2) * Real.sqrt q + 16 * (n - 1) * q ≤ 8.5 * (n ^ 2 * Real.sqrt n) + 8 * n ^ 2 ∧
      8.5 * (n ^ 2 * Real.sqrt n) + 8 * n ^ 2 ≤ 17 * (n ^ 2 * Real.sqrt n))

end Formalism.HermitianLatticeCounting.S8
end
end

-- bundled from Formalism.FlagUnipotentLattices.IotaCountFullAsm
section
namespace Formalism.HermitianLatticeCounting.Final.S6

theorem dualGen : Formalism.HermitianLatticeCounting.S6.DualGen := Formalism.HermitianLatticeCounting.P.dual_generators

end Formalism.HermitianLatticeCounting.Final.S6
end

