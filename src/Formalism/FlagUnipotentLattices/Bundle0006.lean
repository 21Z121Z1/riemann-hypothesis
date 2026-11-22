import Formalism.FlagUnipotentLattices.UnipotentStabiliserCharacterisation
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorSumCounterexample
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IntegrableOnIoiTruncatedPowerMoment
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CircleIntegralInvSubEqZeroOfOutside
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.Bundle0002
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial
import Formalism.FlagUnipotentLattices.Bundle0005
import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LatticeSumBounds
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.DetMulEqSumProdMulDetSubmatrix
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IdealsOfNormEqIndexSet
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SchurAverage
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExponentInequalityNondegenerateMid
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MeasurePreservingPiCompProd
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SumComplexEmbeddingsEqSumInfinitePlace
import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
import Formalism.FlagUnipotentLattices.Bundle0001
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LiftingDecomposition

-- bundled from Formalism.FlagUnipotentLattices.AlgebraicIdentityHigherDegree
section
namespace Formalism.HermitianLatticeCounting.Final.ExpansionTerms

theorem integral_norm_estimate : Formalism.HermitianLatticeCounting.ExpansionTerms.AlgebraicIntegerNormGeOne := Formalism.HermitianLatticeCounting.P.integral_norm_estimate_holds
theorem component_total_sixty_four : Formalism.HermitianLatticeCounting.ExpansionTerms.BlockMinorSumPowSixtyFour := Formalism.HermitianLatticeCounting.P.block_minor_sum_pow_sixty_four
theorem integral_norm_application : Formalism.HermitianLatticeCounting.ExpansionTerms.NormGeOneMaxBound := Formalism.HermitianLatticeCounting.P.integral_norm_application_holds
theorem corollary_consequence : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentBound₂ := Formalism.HermitianLatticeCounting.P.corollary_consequence_holds
theorem mass_inequality_iteration : Formalism.HermitianLatticeCounting.ExpansionTerms.MomentRecursionIterate := Formalism.HermitianLatticeCounting.P.moment_recursion_iterate
theorem abstract_iteration_theorem : Formalism.HermitianLatticeCounting.ExpansionTerms.SuperharmonicMomentBound := Formalism.HermitianLatticeCounting.P.abstract_iteration_theorem_holds

theorem leadingMinorUnipotentInvariant : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorUnipotentInvariant := Formalism.HermitianLatticeCounting.P.invariant_value_holds
theorem e4aVanish : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorVanishesOffBlockEnds := Formalism.HermitianLatticeCounting.P.leading_minor_vanishes_off_block_ends
theorem e4aValue : Formalism.HermitianLatticeCounting.ExpansionTerms.LeadingMinorAtBlockEnd := Formalism.HermitianLatticeCounting.P.leading_minor_at_block_end
theorem integral_evaluation_fourth : Formalism.HermitianLatticeCounting.ExpansionTerms.OrbitIntegralEntries := Formalism.HermitianLatticeCounting.P.orbit_integral_entries
theorem majorant_lower_bound : Formalism.HermitianLatticeCounting.ExpansionTerms.LastDistanceLowerBound := Formalism.HermitianLatticeCounting.P.last_distance_lower_bound

theorem degRatioMinus : Formalism.HermitianLatticeCounting.ExpansionTerms.DegRatioMinus := Formalism.HermitianLatticeCounting.P.degree_ratio_minus_bound
theorem degStepBound : Formalism.HermitianLatticeCounting.ExpansionTerms.DegStepBound := Formalism.HermitianLatticeCounting.P.degree_increment_bound
theorem sup_l2_ratio_majorant : Formalism.HermitianLatticeCounting.ExpansionTerms.supL2RatioMajorant := Formalism.HermitianLatticeCounting.P.first_operator_norm_bound

end Formalism.HermitianLatticeCounting.Final.ExpansionTerms
end

-- bundled from Formalism.FlagUnipotentLattices.AutBoundOfMinkowskiBound
section
namespace Formalism.HermitianLatticeCounting.Final.S6

theorem y1 : Formalism.HermitianLatticeCounting.S6.Y1 := by
  first
    | exact Formalism.HermitianLatticeCounting.P.wedgeMapInLieAlgebra
    | exact Formalism.HermitianLatticeCounting.P.S6e.wedgeMapInLieAlgebra
theorem n0c : Formalism.HermitianLatticeCounting.S6.MemOfOrthogonalAnisotropic := by
  first
    | exact Formalism.HermitianLatticeCounting.P.memOfOrthogonalAnisotropic
    | exact Formalism.HermitianLatticeCounting.P.S6e.memOfOrthogonalAnisotropic
theorem nFJZero : Formalism.HermitianLatticeCounting.S6.NFJZero := by
  first
    | exact Formalism.HermitianLatticeCounting.P.normalFormZero
    | exact Formalism.HermitianLatticeCounting.P.S6e.normalFormZero

theorem normalForm : Formalism.HermitianLatticeCounting.S6.NormalForm := by
  first
    | exact Formalism.HermitianLatticeCounting.P.existsNormalForm
    | exact Formalism.HermitianLatticeCounting.P.S6e.existsNormalForm

theorem normSgBound : Formalism.HermitianLatticeCounting.S6.NormSgBound := by
  first
    | exact Formalism.HermitianLatticeCounting.P.norm_singular_value_bound
    | exact Formalism.HermitianLatticeCounting.P.S6e.norm_singular_value_bound

theorem minkowskiDvdFactorial : Formalism.HermitianLatticeCounting.S6.MinkowskiDvdFactorial := by
  first
    | exact Formalism.HermitianLatticeCounting.P.minkowski_number_dvd_factorial
    | exact Formalism.HermitianLatticeCounting.P.S6e.minkowski_number_dvd_factorial
theorem autBound_of_minkowskiBound : Formalism.HermitianLatticeCounting.S6.MinkowskiBound → Formalism.HermitianLatticeCounting.S6.AutBound := by
  intro hMk s f G hG
  have h1 := (hMk (2 * s * f) G hG).trans (minkowskiDvdFactorial (2 * s * f))
  have h2 : Nat.card G ≤ (2 * (2 * s * f)).factorial := Nat.le_of_dvd (Nat.factorial_pos _) h1
  have h3 : (2 * (2 * s * f)).factorial ≤ (4 * s * f) ^ (4 * s * f) := by
    have e : 2 * (2 * s * f) = 4 * s * f := by ring
    rw [e]
    exact Nat.factorial_le_pow _
  exact_mod_cast h2.trans h3

theorem expIdentity : Formalism.HermitianLatticeCounting.S6.ExpIdentity := by
  first
    | exact Formalism.HermitianLatticeCounting.P.exponential_identity
    | exact Formalism.HermitianLatticeCounting.P.S6e.exponential_identity
theorem finalSum : Formalism.HermitianLatticeCounting.S6.FinalSum := by
  first
    | exact Formalism.HermitianLatticeCounting.P.final_sum_bound
    | exact Formalism.HermitianLatticeCounting.P.S6e.final_sum_bound

end Formalism.HermitianLatticeCounting.Final.S6
end

-- bundled from Formalism.FlagUnipotentLattices.BlockDistFromLows
section
open Finset MeasureTheory Filter Topology TensorProduct

noncomputable section

namespace Formalism.HermitianLatticeCounting.S8

def SoftVanish : Prop :=
  ∀ (X O : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [TopologicalSpace O] [LocallyCompactSpace O] [MeasurableSpace O] [BorelSpace O] (μ : Measure O)
    [μ.IsOpenPosMeasure] (ι : O → X) (𝒜 : Set (X → ℂ)) (c : O → ℂ),
    Continuous ι → Function.Injective ι → Continuous c →
    (∀ β ∈ 𝒜, Continuous β ∧ HasCompactSupport β) →
    (∀ β ∈ 𝒜, ∀ β' ∈ 𝒜, (fun x => β x * β' x) ∈ 𝒜) →
    (∀ β ∈ 𝒜, (fun x => star (β x)) ∈ 𝒜) →
    (∀ x y : X, x ≠ y → ∃ β ∈ 𝒜, β x ≠ β y) →
    (∀ C : Set X, IsCompact C → ∃ β ∈ 𝒜, ∀ x ∈ C, β x = 1) →
    (∀ β ∈ 𝒜, Integrable (fun h => β (ι h) * c h) μ) →
    (∀ β ∈ 𝒜, ∫ h, β (ι h) * c h ∂μ = 0) →
    c = 0

def SoftNonzero : Prop :=
  ∀ (X O : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [TopologicalSpace O] [LocallyCompactSpace O] [MeasurableSpace O] [BorelSpace O] (μ : Measure O)
    [μ.IsOpenPosMeasure] (ι : O → X) (𝒜 : Set (X → ℂ)) (c : O → ℂ) (h₀ : O),
    Continuous ι → Function.Injective ι → Continuous c →
    (∀ β ∈ 𝒜, Continuous β ∧ HasCompactSupport β) →
    (∀ β ∈ 𝒜, ∀ β' ∈ 𝒜, (fun x => β x * β' x) ∈ 𝒜) →
    (∀ β ∈ 𝒜, (fun x => star (β x)) ∈ 𝒜) →
    (∀ x y : X, x ≠ y → ∃ β ∈ 𝒜, β x ≠ β y) →
    (∀ C : Set X, IsCompact C → ∃ β ∈ 𝒜, ∀ x ∈ C, β x = 1) →
    (∀ β ∈ 𝒜, Integrable (fun h => β (ι h) * c h) μ) →
    c h₀ ≠ 0 → ∃ β ∈ 𝒜, ∫ h, β (ι h) * c h ∂μ ≠ 0

def EIdempotent : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (G : Type) [Group G]
    [MeasurableSpace G] (μ : Measure G) (ρ : G →* (E →L[ℂ] E)) (d : ℝ),
    (∀ g, ρ g ∈ unitary (E →L[ℂ] E)) → d ≠ 0 →
    (∀ a b c b' : E, ∫ g, (inner ℂ b (ρ g a) : ℂ) * star (inner ℂ b' (ρ g c) : ℂ) ∂μ =
      (d : ℂ)⁻¹ * (inner ℂ c a : ℂ) * star (inner ℂ b' b : ℂ)) →
    ∀ w : E, ‖w‖ = 1 →
      (∀ x : G, ∫ g, ((d : ℂ) * star (inner ℂ w (ρ g w) : ℂ)) * ((d : ℂ) * star (inner ℂ w (ρ (g⁻¹ * x) w) : ℂ)) ∂μ =
        (d : ℂ) * star (inner ℂ w (ρ x w) : ℂ)) ∧
      (∀ y : E, ∫ g, ((d : ℂ) * star (inner ℂ w (ρ g w) : ℂ)) * (inner ℂ y (ρ g w) : ℂ) ∂μ = (inner ℂ y w : ℂ)) ∧
      (∀ g x : G, ∫ y, ((d : ℂ) * star (inner ℂ w (ρ y w) : ℂ)) *
          ((d : ℂ) * star (inner ℂ w (ρ (g⁻¹ * y⁻¹ * x) w) : ℂ)) ∂μ =
        (inner ℂ w (ρ g w) : ℂ) * ((d : ℂ) * star (inner ℂ w (ρ x w) : ℂ)))

def PsiInvert : Prop :=
  ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (n r k : ℕ) (c w : ℕ → Fin n)
    (E : Fin n → Fin n → Module.End ℂ V) (π : Fin k → Fin k → Module.End ℂ U) (d : ℕ → ℂ) (ℓ : V →ₗ[ℂ] U)
    (A : Module.End ℂ V) (ε : Fin n → ℂ),
    ChainLabel r k c w → ChainEquivariant r k c w E π d ℓ →
    (∀ i ≤ 2 * r, ε (c i) = (-1) ^ (r + i)) → (∀ s < k, ε (w s) = 1) →
    (∀ a b v, A (E a b v) = (ε a * ε b) • E a b (A v)) →
    ChainEquivariant r k c w E π (fun j => -d j) (ℓ ∘ₗ A)

def BlockDistFromLows : Prop :=
  ∀ (m t : ℕ) (b e : ℕ → ℝ),
    (∀ i < m, b i < e i) → (∀ i, i + 1 < m → e i < b (i + 1)) →
    (∀ i < m, ∀ j < m, ((t : ℝ) + 3) / 2 ≤ |b i - e j|) →
    ∀ i < m, ∀ j < m, i ≠ j → (t : ℝ) + 3 ≤ |e i - e j| ∧
      ∀ len ≤ t + 1, ∀ x ∈ blockP (-e i) len, (t : ℝ) / 2 + 3 ≤ |x + e j|

def Mrk (k m t : ℕ) : ℝ := ((k + m - 1 : ℕ) : ℝ) + (m : ℝ) * t

def GArith : Prop :=
  ∀ k m t : ℕ, 1 ≤ k → Even m → 2 ≤ m → (k + m - 1) + 5 ≤ t →
    (m : ℝ) * ((m : ℝ) + 6) ≤ Mrk k m t ∧
    (∀ n q₀ : ℝ, 0 ≤ n → n ≤ Mrk k m t → 0 ≤ q₀ → q₀ ≤ (m : ℝ) / 2 →
      120 * n * (q₀ * Real.sqrt q₀) < Mrk k m t ^ 3 ∧ 16 * n * (q₀ * Real.sqrt q₀) ≤ 2 * Mrk k m t ^ 3) ∧
    (Even k → Odd t → 20 * Real.sqrt ((m : ℝ) / 2) ≤ Mrk k m t ∧
      ∀ n q₀ : ℝ, 0 ≤ n → n ≤ Mrk k m t → 0 ≤ q₀ → q₀ ≤ (m : ℝ) / 2 →
        40 * n ^ 2 * Real.sqrt q₀ ≤ 2 * Mrk k m t ^ 3)

def DSArgs : Prop :=
  ∀ a t' i : ℕ, 1 ≤ t' → i < a → (t' : ℝ) + 1 ≤ (a : ℝ) + t' - i ∧ (2 : ℝ) ≤ (a : ℝ) + t' - i

def paramPi (t j : ℕ) (u : List ℝ) (e : ℕ → ℝ) : List ℝ :=
  u ++ (List.range j).flatMap (fun i => blockP (-e i) (t + 1))

def ParamPiCoset : Prop :=
  ∀ (k t j : ℕ) (u : List ℝ) (e : ℕ → ℝ), Odd t →
    (∀ x ∈ u, ∃ z : ℤ, x = (z : ℝ) + ((k : ℝ) - 1) / 2) → (∀ i < j, ∃ z : ℤ, e i = (z : ℝ) + (k : ℝ) / 2) →
    ∀ x ∈ paramPi t j u e, ∃ z : ℤ, x - ((dimX k t j : ℝ) - 1) / 2 = (z : ℝ)

def CompactPairRange : Prop :=
  ∀ (k m t j : ℕ) (u : List ℝ) (b e : ℕ → ℝ), Odd t → j < m → (∀ x ∈ u, -b 0 < x) →
    (∀ i < m, b i < e i) → (∀ i, i + 1 < m → e i < b (i + 1)) →
    (∀ i < m, ∀ i' < m, ((t : ℝ) + 3) / 2 ≤ |b i' - e i|) →
    (∀ x ∈ u, ∃ z : ℤ, x = (z : ℝ) + ((k : ℝ) - 1) / 2) → (∀ i < m, ∃ z : ℤ, e i = (z : ℝ) + (k : ℝ) / 2) →
    ∀ x ∈ paramPi t j u e, -e j + ((t : ℝ) + 2) / 2 ≤ x ∧ ∃ z : ℤ, x - (-e j + ((t : ℝ) + 2) / 2) = (z : ℝ)

def CentreInt : Prop :=
  ∀ (k : ℕ) (e : ℝ), Even k → (∃ z : ℤ, e = (z : ℝ) + (k : ℝ) / 2) → ∃ z : ℤ, e = (z : ℝ)

def kCh (k : ℕ) (t : ℕ → ℕ) : ℕ → ℕ
  | 0 => k
  | j + 1 => kCh k t j + t j + 1

def BaseRank : Prop :=
  ∀ (k m : ℕ) (t : ℕ → ℕ), 1 ≤ k → 1 ≤ m → (∀ j, 1 ≤ t j) →
    (∀ j ≤ m, (k + m - 1 + ∑ i ∈ Finset.range j, t i) + (j + 1) = kCh k t j + m) ∧
    (∀ j ≤ m, k + m - 1 + ∑ i ∈ Finset.range j, t i ≤ kCh k t m - 1)

def BaseExplicit : Prop :=
  ∀ (k m : ℕ) (t : ℕ → ℕ), Even k → 2 ≤ k → Even m → 2 ≤ m → (∀ j, t j = kCh k t j + 1) →
    (∀ j, kCh k t j + 2 = 2 ^ j * (k + 2)) ∧
    (∀ j, Even (kCh k t j) ∧ Odd (t j) ∧ 2 * kCh k t j < kCh k t (j + 1) ∧ t j < t (j + 1)) ∧
    kCh k t m + 2 = 2 ^ m * (k + 2) ∧ 13 ≤ kCh k t m - 1 ∧
    120 * ((m : ℝ) / 2 * Real.sqrt ((m : ℝ) / 2)) < ((kCh k t m : ℝ) - 1) ^ 2 ∧
    (∀ j, ((t j : ℝ) + 2) / 2 - ((kCh k t j : ℝ) - 1) / 2 = 2)

def sgnDV (k m : ℕ) (t : ℕ → ℕ) (j : ℕ) : List Bool :=
  List.replicate (k - 1 + (j + 1) + ∑ i ∈ Finset.range j, t i) true ++
    (List.range (m - j - 1)).map (fun i => decide (i % 2 = 1))

def paramDV (t : ℕ → ℕ) (j m : ℕ) (v : List ℝ) (b e : ℕ → ℝ) : List ℝ :=
  v ++ (List.range m).flatMap (fun i => -b i :: if i < j then blockP (-e i) (t i) else [])

def VConst : Prop :=
  ∀ (k m t j : ℕ) (v : List ℝ) (b e : ℕ → ℝ),
    sgnDV k m (fun _ => t) j = sgnD k m t j ∧ paramDV (fun _ => t) j m v b e = paramD t j m v b e

def ParamDChainV : Prop :=
  ∀ (k m j : ℕ) (t : ℕ → ℕ) (u v : List ℝ) (b e : ℕ → ℝ),
    1 ≤ k → j < m → Interlaces u v → u.length = k → (∀ x ∈ u, -b 0 < x) →
    (∀ i < m, b i < e i) → (∀ i, i + 1 < m → e i < b (i + 1)) →
    (∀ i < m, ∀ i' < m, ((t i : ℝ) + 1) / 2 ≤ |b i' - e i|) →
    (paramDV t j m v b e).IsChain (· > ·) ∧ (paramDV t j m v b e).length = (sgnDV k m t j).length ∧
      (sgnDV k m t j).length = k + m - 1 + ∑ i ∈ Finset.range j, t i

def GapDV : Prop :=
  ∀ (k m j : ℕ) (t : ℕ → ℕ) (h : ℝ) (u v : List ℝ) (b e : ℕ → ℝ),
    1 ≤ k → j < m → Interlaces u v → u.length = k → (∀ x ∈ u, -b 0 < x) →
    (∀ i < m, b i < e i) → (∀ i, i + 1 < m → e i < b (i + 1)) →
    (∀ i < m, ∀ i' < m, ((t i : ℝ) + 1) / 2 ≤ |b i' - e i|) →
    (∀ i, i + 1 < m → h ≤ b (i + 1) - b i) →
    Formalism.QuantumDeterminants.GapAtLeast (n := (paramDV t j m v b e).length)
      (fun a => (sgnDV k m t j).getD (a : ℕ) true) (fun a => (paramDV t j m v b e).get a) h

def BaseExists : Prop :=
  ∀ (b : ℕ → ℝ) (H : ℝ), ∃ b0 : ℕ → ℝ, b0 0 = b 0 ∧ (∀ i, ∃ z : ℕ, b0 i = b i + (z : ℝ)) ∧
    ∀ i, H ≤ b0 (i + 1) - b0 i

def ExplicitC : Prop :=
  ∀ (n : ℕ) (q h : ℝ), 2 ≤ n → 0 ≤ q → q ≤ (n : ℝ) / 2 →
    16 * (((n ^ 2 / 2 + 1 : ℕ) : ℝ)) * Real.sqrt q ≤ 8 * ((n : ℝ) ^ 2 + 2) * Real.sqrt q ∧
    43 * ((n : ℝ) ^ 2 * Real.sqrt n) ≤ 43 * (n : ℝ) ^ 3 ∧
    (43 * ((n : ℝ) ^ 2 * Real.sqrt n) ≤ h →
      120 * n * (q * Real.sqrt q) ≤ h ∧ 8 * ((n : ℝ) ^ 2 + 2) * Real.sqrt q + 16 * ((n : ℝ) - 1) * q < h ∧
        16 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h)

def DecayArith : Prop :=
  ∀ (q : ℕ) (n : ℝ) (t : Fin q → ℝ), (∀ i, 0 ≤ t i) →
    ((∑ i : Fin q, ∑ j ∈ univ.filter (fun j : Fin q => i < j), (2 * ((t i - t j) + (t i + t j)))) +
        (∑ i : Fin q, ((2 * (n - 2 * q) + 2) * t i)) = ∑ i : Fin q, (2 * (n - 2 * (i : ℕ) - 1) * t i)) ∧
    (∑ i : Fin q, 2 * (n - 2 * (i : ℕ) - 1) * t i ≤ 2 * (n - 1) * ∑ i, t i) ∧
    (∑ i : Fin q, 2 * (n - 2 * ((i : ℕ) : ℝ) - 1) = 2 * q * (n - q)) ∧
    (∀ i, t i ≤ Real.sqrt (2 * ∑ i, t i ^ 2) / Real.sqrt 2) ∧
    (∑ i, t i ≤ Real.sqrt ((q : ℝ) / 2) * Real.sqrt (2 * ∑ i, t i ^ 2)) ∧
    (1 ≤ q → ∀ h M : ℝ, (0 < h / (8 * Real.sqrt (2 * q)) - M / Real.sqrt 2 - (n - 1) * Real.sqrt (2 * q) ↔
      8 * M * Real.sqrt q + 16 * (n - 1) * q < h))

def HypArith : Prop :=
  ∀ (k r : ℕ) (n q B₀ h : ℝ), 1 ≤ k → n = (k : ℝ) + 2 * r + 1 → q = (r : ℝ) + 1 →
    B₀ = ((r : ℝ) * (r - 1) + 2 * r * (k + 1) + (r : ℝ) ^ 2) + (r : ℝ) ^ 2 + 1 →
    (r : ℝ) * (r - 1) + 2 * r * (k + 1) + (r : ℝ) ^ 2 = r * (n + k) ∧ B₀ = r * (2 * n - r - 1) + 1 ∧
    2 * B₀ + 2 * q * (n - q) + 1 = 6 * r * n - 4 * (r : ℝ) ^ 2 - 6 * r + 2 * n + 1 ∧
    2 * B₀ + 2 * q * (n - q) + 1 ≤ 2 * n ^ 2 - 3 * n + 3 ∧ 2 * n ^ 2 - 3 * n + 3 ≤ 2 * n ^ 2 ∧
    (16 * n ^ 2 * Real.sqrt q ≤ h → 2 * B₀ + 2 * q * (n - q) + 1 ≤ h / (8 * Real.sqrt q))

def ResidueValue : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module ℂ E] (n k : ℕ) (lam : Fin n → ℂ) (u : Fin k → ℂ) (a : Fin n → E)
    (K : E) (s₀ s₁ : ℂ),
    Function.Injective lam →
    (∀ x : ℂ, (∀ s, x + s₀ - lam s ≠ 0) →
      ∑ i, (x - (lam i - s₀))⁻¹ • a i = ((∏ j, (x + s₁ - u j)) / ∏ s, (x + s₀ - lam s)) • K) →
    ∀ i, a i = ((∏ j, (lam i + (s₁ - s₀) - u j)) / ∏ s ∈ univ.erase i, (lam i - lam s)) • K

end Formalism.HermitianLatticeCounting.S8
end
end

-- bundled from Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
section
namespace Formalism.HermitianLatticeCounting.Final.LatticeSumBounds

theorem absA : Formalism.HermitianLatticeCounting.LatticeSumBounds.AbsA := Formalism.HermitianLatticeCounting.P.absolute_value_bound
theorem wedgeHadamard : Formalism.HermitianLatticeCounting.LatticeSumBounds.WedgeHadamard := Formalism.HermitianLatticeCounting.P.wedge_hadamard_inequality
theorem cramerUpper : Formalism.HermitianLatticeCounting.LatticeSumBounds.CramerUpper := Formalism.HermitianLatticeCounting.P.leadingMinorColumnReplace
theorem gramHadamard : Formalism.HermitianLatticeCounting.LatticeSumBounds.GramHadamard := Formalism.HermitianLatticeCounting.P.gram_hadamard_inequality
theorem lemmaP : Formalism.HermitianLatticeCounting.LatticeSumBounds.LemmaP := Formalism.HermitianLatticeCounting.P.prodMaxInvLeSq
theorem packing : Formalism.HermitianLatticeCounting.LatticeSumBounds.Packing := Formalism.HermitianLatticeCounting.P.packing_bound
theorem traceLower : Formalism.HermitianLatticeCounting.LatticeSumBounds.TraceLower := Formalism.HermitianLatticeCounting.P.traceLowerBound
theorem classNumberBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.ClassNumberBound := Formalism.HermitianLatticeCounting.P.class_number_upper_bound
theorem c2a : Formalism.HermitianLatticeCounting.LatticeSumBounds.CardSubmodulesOfIndexLePow := Formalism.HermitianLatticeCounting.P.ideal_count_statement
theorem c2b : Formalism.HermitianLatticeCounting.LatticeSumBounds.CardSubmodulesAndLinearEquivBounds := Formalism.HermitianLatticeCounting.P.submodule_automorphism_count
theorem unipotentReduce : Formalism.HermitianLatticeCounting.LatticeSumBounds.UnipotentReduce := Formalism.HermitianLatticeCounting.P.unitriangularReduction
theorem leadingMinorInvariant : Formalism.HermitianLatticeCounting.LatticeSumBounds.LeadingMinorInvariant := Formalism.HermitianLatticeCounting.P.leadingMinorTriangularInvariant
theorem minorBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.MinorBound := Formalism.HermitianLatticeCounting.P.normMinorMulLe
theorem monomialMinor : Formalism.HermitianLatticeCounting.LatticeSumBounds.MonomialMinor := Formalism.HermitianLatticeCounting.P.normMinorMonomialLe
theorem omegaNorm : Formalism.HermitianLatticeCounting.LatticeSumBounds.OmegaNorm := Formalism.HermitianLatticeCounting.P.complementNormIdentity
theorem boxCount : Formalism.HermitianLatticeCounting.LatticeSumBounds.BoxCount := Formalism.HermitianLatticeCounting.P.box_count_alt
theorem kernelRowSpace : Formalism.HermitianLatticeCounting.LatticeSumBounds.KernelRowSpace := Formalism.HermitianLatticeCounting.P.cofactorVectorKernel
theorem cofVecAdjugate : Formalism.HermitianLatticeCounting.LatticeSumBounds.CofVecAdjugate := Formalism.HermitianLatticeCounting.P.adjugateLastColumnEqCofactor
theorem projQuotCard : Formalism.HermitianLatticeCounting.LatticeSumBounds.ProjQuotCard := Formalism.HermitianLatticeCounting.P.projective_quotient_card
theorem degFactorBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.DegFactorBound := Formalism.HermitianLatticeCounting.P.prodHyperbolicRatioSqLe
theorem deNonDegBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.DeNonDegBound := Formalism.HermitianLatticeCounting.P.nondegenerateFactorBound
theorem deDegBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.DeDegBound := Formalism.HermitianLatticeCounting.P.degenerateFactorBound
theorem nonDegRow : Formalism.HermitianLatticeCounting.LatticeSumBounds.NonDegRow := Formalism.HermitianLatticeCounting.P.nondegenerateRowBound
theorem degRow : Formalism.HermitianLatticeCounting.LatticeSumBounds.DegRow := Formalism.HermitianLatticeCounting.P.degenerateRowBound
theorem nonDegSum : Formalism.HermitianLatticeCounting.LatticeSumBounds.NonDegSum := Formalism.HermitianLatticeCounting.P.sumNondegenerateRowsLe
theorem degSum : Formalism.HermitianLatticeCounting.LatticeSumBounds.DegSum := Formalism.HermitianLatticeCounting.P.sumDegenerateRowsLe
theorem smallTerm : Formalism.HermitianLatticeCounting.LatticeSumBounds.SmallTerm := Formalism.HermitianLatticeCounting.P.prodMinLeOfProdRatio
theorem single_row_lattice_sum_bound : Formalism.HermitianLatticeCounting.LatticeSumBounds.SingleRowBound := Formalism.HermitianLatticeCounting.P.singleRowBound
theorem lattice_exp_sum_upper_bound : Formalism.HermitianLatticeCounting.LatticeSumBounds.ExpSumLe' := Formalism.HermitianLatticeCounting.P.expSumLe'
theorem gainSqrt : Formalism.HermitianLatticeCounting.LatticeSumBounds.GainSqrt := Formalism.HermitianLatticeCounting.P.invSqrtPowLeExp
theorem boxCountO : Formalism.HermitianLatticeCounting.LatticeSumBounds.BoxCountO := Formalism.HermitianLatticeCounting.P.box_count_big_O
theorem latticeSum : Formalism.HermitianLatticeCounting.LatticeSumBounds.LatticeSum := Formalism.HermitianLatticeCounting.P.lattice_sum_alt
theorem homRestrictIndex : Formalism.HermitianLatticeCounting.LatticeSumBounds.HomRestrictIndex := Formalism.HermitianLatticeCounting.P.cardCokernelRestriction

theorem coveringO_of_transference (h : Formalism.HermitianLatticeCounting.LatticeSumBounds.Transference) :
    Formalism.HermitianLatticeCounting.LatticeSumBounds.CoveringO := Formalism.HermitianLatticeCounting.P.coveringO_of_transference h

end Formalism.HermitianLatticeCounting.Final.LatticeSumBounds
end

-- bundled from Formalism.FlagUnipotentLattices.CoveringRadius2
section
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder

noncomputable section

namespace Formalism.HermitianLatticeCounting.S7

open Formalism.NuclearRankWeightBounds.D (lead hs q0)

def PolarInv : Prop :=
  ∀ (N : ℕ) (k X : Matrix (Fin N) (Fin N) ℂ), k ∈ Matrix.unitaryGroup (Fin N) ℂ → X.IsHermitian →
    (k * NormedSpace.exp X)⁻¹ = k.conjTranspose * NormedSpace.exp (-(k * X * k.conjTranspose)) ∧
      (-(k * X * k.conjTranspose)).IsHermitian ∧ hs (-(k * X * k.conjTranspose)) = hs X ∧
      ((Real.exp (hs X) ^ 2 : ℝ) • (1 : Matrix (Fin N) (Fin N) ℂ)
        - (k * NormedSpace.exp X).conjTranspose * (k * NormedSpace.exp X)).PosSemidef

open Classical in

def AllSum : Prop :=
  ∀ (ι Γ : Type) [Fintype ι] [Nonempty ι] (S : Finset Γ) (d : Γ → ι → ℝ) (A B h ε : ℝ) (q : ℕ),
    1 ≤ q → 0 ≤ A → 0 ≤ B → 0 < ε → ε * Real.sqrt (2 * (q : ℝ)) ≤ 1 → B * ε ≤ 1 →
    32 * B ≤ h * ε → 16 ≤ h * ε ^ 2 →
    (∀ γ ∈ S, ∀ v, 0 ≤ d γ v) →
    (∀ r : ι → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, d γ v ≤ r v).card : ℝ) ≤ A * Real.exp (B * ∑ v, r v)) →
    ∑ γ ∈ S, ∏ v, Real.exp (-(decExp h q (d γ v))) ≤ A * 4 ^ Fintype.card ι

open Classical in

def AllSumRate : Prop :=
  ∀ (ι Γ : Type) [Fintype ι] [Nonempty ι] (S : Finset Γ) (d : Γ → ι → ℝ) (A B h : ℝ) (q : ℕ),
    1 ≤ q → 0 ≤ A → 0 < B → 16 * B * Real.sqrt (2 * (q : ℝ)) ≤ h →
    (∀ γ ∈ S, ∀ v, 0 ≤ d γ v) →
    (∀ r : ι → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, d γ v ≤ r v).card : ℝ) ≤ A * Real.exp (B * ∑ v, r v)) →
    ∑ γ ∈ S, ∏ v, Real.exp (-(decExp h q (d γ v))) ≤
      A * (Real.exp B / (1 - Real.exp (-B))) ^ Fintype.card ι

def ThreshCount : Prop :=
  ∀ (n q : ℕ) (h : ℝ), 46 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h →
    16 * (2 * (n : ℝ) ^ 2) * Real.sqrt (2 * (q : ℝ)) ≤ h

def NearUnipotent : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n g : ℕ) (ε : ℝ), Squarefree g → 4 * n < g →
    (∀ P : Ideal (𝓞 E), P.IsPrime → ((g : ℤ) : 𝓞 E) ∈ P → P.ramificationIdx ℤ = 1) →
    (n : ℝ) * ε ≤ 1 → ε ≤ 1 / 4 →
    ∀ γ : Matrix (Fin n) (Fin n) E, IsUnit γ →
    ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ →
      (∀ x ∈ L, γ *ᵥ x ∈ L) →
      (∀ P : Ideal (𝓞 E), P.IsPrime → ((g : ℤ) : 𝓞 E) ∈ P →
        ∀ x ∈ L, ((γ - 1) ^ n) *ᵥ x ∈ P • L) →
      ∀ (x k X : (E →+* ℂ) → Matrix (Fin n) (Fin n) ℂ),
      (∀ φ, IsUnit (x φ) ∧ k φ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ (X φ).IsHermitian ∧ hs (X φ) ≤ ε ∧
        (x φ)⁻¹ * γ.map φ * x φ = k φ * NormedSpace.exp (X φ)) →
      (γ - 1) ^ n = 0 ∧ ∀ φ, hs ((x φ)⁻¹ * γ.map φ * x φ - 1) ≤ 3 * Real.sqrt (n * ε)

def NearAssembly : Prop :=
  Formalism.SA.D.Unipotence → NearPowBound → UnipTrace → NearIdentity → NearUnipotent

def IsotropicDim : Prop :=
  ∀ (N : ℕ) (ep : Fin N → Bool) (W : Submodule ℂ (Fin N → ℂ)),
    (∀ x ∈ W, ∀ y ∈ W, ∑ a, (if ep a then (1 : ℂ) else -1) * star (x a) * y a = 0) →
    Module.finrank ℂ W ≤ q0 ep

def LayerCount : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (N : ℕ) (de la laM : ℝ), 0 ≤ de → 0 < la → la / 2 ≤ laM →
    (1 + 2 * (∏ _v : ι, 3 * de) ^ ((1 : ℝ) / Fintype.card ι) / laM) ^ (N * Fintype.card ι) ≤
      (1 + 12 * de / la) ^ (N * Fintype.card ι)

def KappaAssembly : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ C' : ℝ, 1 ≤ C' ∧
    ∀ (a p q n0 f : ℕ) (j : Fin a → ℕ) (v res cIw volN volR : ℝ) (volGL : Fin a → ℝ),
    (∀ x, 1 ≤ j x) → 1 ≤ a → (∑ x, j x) ≤ q → q ≤ p → p + q = n0 + 2 * ∑ x, j x → 1 ≤ f →
    1 / 2 ≤ v → 0 ≤ res →
    0 ≤ volN → volN ≤ (C * v) ^ ((f : ℝ) * dimN j n0 / 2) →
    (∀ x, 0 ≤ volGL x ∧ volGL x ≤ (C * v) ^ (j x ^ 2 * f) * res * C ^ f) →
    0 ≤ volR → volR ≤ v ^ (-(((p + q : ℕ) : ℝ) ^ 2 - (n0 : ℝ) ^ 2) * f / 2) * C ^ ((p + q) * f) →
    0 ≤ cIw → cIw ≤ (C ^ dimN j n0 * (Vsph p * Vsph q /
      (Vsph (p - ∑ x, j x) * Vsph (q - ∑ x, j x) * ∏ x, Vsph (j x)))) ^ f →
    cIw * volN * (∏ x, volGL x) * volR ≤
      v ^ (-((f : ℝ) * dimN j n0 / 2)) * C' ^ ((∑ x, j x) * (p + q) * f) * res ^ a
        * ((C' / (p : ℝ)) ^ ((∑ x, j x) * (p - ∑ x, j x))
          * ((∑ x, j x : ℕ) : ℝ) ^ (((∑ x, j x : ℕ) : ℝ) ^ 2 / 2)) ^ f

def DedekindProduct : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] (j : ℕ),
    ∏ i ∈ Icc 2 j, ‖dedekindZeta E (i : ℂ)‖ ≤ C ^ Module.finrank ℚ E

def DedekindZetaResidueBound : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E], 2 ≤ Module.finrank ℚ E →
    dedekindZeta_residue E ≤
      (C * Real.log (((|discr E| : ℤ) : ℝ) ^ ((1 : ℝ) / Module.finrank ℚ E))) ^ Module.finrank ℚ E

def LogVolumeBound : Prop :=
  ∀ (a q f : ℕ) (j : Fin a → ℕ) (C₁ Y : ℝ), 1 ≤ C₁ → 2 ≤ Y → 1 ≤ q → (∀ x, j x ≤ q) →
    0 < Y ^ (-(C₁ * q)) ∧ Y ^ (-(C₁ * q)) ≤ 1 / 2 ∧
    ∏ x, (2 * (f : ℝ) * j x * Real.log (1 / (2 * Y ^ (-(C₁ * q))))) ≤
      (2 * C₁ * f * (q : ℝ) ^ 2 * Real.log Y) ^ a

def EpsSide : Prop :=
  ∀ (n q f : ℕ) (c : ℝ), 1 ≤ n → 1 ≤ f → q ^ 2 ≤ n → 0 < c → c ≤ 1 / 90000 →
    2 * (n : ℝ) ^ 2 * epsN c n f ≤ 1 ∧ epsN c n f * Real.sqrt (2 * (q : ℝ)) ≤ 1

def ThreshSide : Prop :=
  ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧ ∀ (n f : ℕ) (rd b h : ℝ), 1 ≤ n → 1 ≤ f → 2 ≤ b → 1 ≤ rd →
    C * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * Real.log (b * rd) ≤ h →
    32 * (2 * (n : ℝ) ^ 2) ≤ h * epsN c n f ∧ 16 ≤ h * epsN c n f ^ 2

def FarPrefactorOp : Prop :=
  ∀ (n f : ℕ) (τs : ℝ), 1 ≤ n → 1 ≤ f → 0 < τs →
    (3 / τs ^ 2) ^ (2 * n ^ 2 * f) * 4 ^ f ≤ (6 / τs) ^ (4 * n ^ 2 * f)

def CoveringRadius2 : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (M : Submodule ℤ V), DiscreteTopology M → Submodule.span ℝ (M : Set V) = ⊤ →
    ∀ κ : ℝ, 0 < κ → (∀ y ∈ Formalism.HadamardInequality.zdual M, y ≠ 0 → κ ≤ ‖y‖) →
    ∀ x : V, ∃ y ∈ M, ‖x - y‖ ≤ (Module.finrank ℝ V : ℝ) / (2 * κ)

def StepsRoom : Prop :=
  ∀ (n q f P : ℕ) (b : ℝ), 1 ≤ q → P0 n q f + n ^ 2 * f ≤ 2 * P0 n q f ∧
    (P ≤ 2 * P0 n q f → b ^ 2 + (P : ℝ) * n ≤ b1 n q f b)

def BasisCS : Prop :=
  ∀ (ι H : Type) [Fintype ι] [NormedAddCommGroup H] [NormedSpace ℝ H] (c : ι → ℝ) (v : ι → H)
    (B : ℝ), (∀ i, ‖v i‖ ≤ B) →
    ‖∑ i, c i • v i‖ ≤ Real.sqrt (∑ i, c i ^ 2) * Real.sqrt (Fintype.card ι) * B

def PathOsc : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℝ H] (φ φ' : ℝ → H) (T B : ℝ), 0 ≤ T →
    (∀ t ∈ Set.Icc 0 T, HasDerivWithinAt φ (φ' t) (Set.Icc 0 T) t) →
    (∀ t ∈ Set.Icc 0 T, ‖φ' t‖ ≤ B) → ‖φ T - φ 0‖ ≤ T * B

def OscBound : Prop :=
  ∀ (V H ι : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup H]
    [NormedSpace ℝ H] [Fintype ι] (e : OrthonormalBasis ι ℝ V) (φ : V → H) (φ' : V → V →L[ℝ] H)
    (s : Set V) (B : ℝ), Convex ℝ s → (∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x) →
    (∀ x ∈ s, ∀ i, ‖φ' x (e i)‖ ≤ B) →
    ∀ x ∈ s, ∀ y ∈ s, ‖φ x - φ y‖ ≤ ‖x - y‖ * Real.sqrt (Fintype.card ι) * B

def PeriodicSup : Prop :=
  ∀ (V H ι : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [Fintype ι] (e : OrthonormalBasis ι ℝ V) (M : Submodule ℤ V) (D : Set V) (φ : V → H)
    (φ' : V → V →L[ℝ] H) (ρ B : ℝ),
    DiscreteTopology M → Submodule.span ℝ (M : Set V) = ⊤ →
    IsAddFundamentalDomain M D (volume : Measure V) →
    (∀ x, HasFDerivAt φ (φ' x) x) → (∀ x, ∀ y ∈ M, φ (x + y) = φ x) →
    (∫ x in D, φ x) = 0 → (∀ x : V, ∃ y ∈ M, ‖x - y‖ ≤ ρ) → (∀ x i, ‖φ' x (e i)‖ ≤ B) →
    ∀ x, ‖φ x‖ ≤ ρ * Real.sqrt (Fintype.card ι) * B

def SobolevCube : Prop :=
  ∀ (m : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Dv : Finset (Fin m) → (Fin m → ℝ) → H) (s : ℝ), 0 < s →
    (∀ S, ContinuousOn (Dv S) (Set.Icc (0 : Fin m → ℝ) (fun _ => s))) →
    (∀ (S : Finset (Fin m)) (i : Fin m), i ∉ S → ∀ t ∈ Set.Icc (0 : Fin m → ℝ) (fun _ => s),
      HasDerivWithinAt (fun r : ℝ => Dv S (Function.update t i r)) (Dv (insert i S) t)
        (Set.Icc 0 s) (t i)) →
    ‖Dv ∅ 0‖ ^ 2 ≤ (2 / s) ^ m * ∑ S : Finset (Fin m), s ^ (2 * S.card) *
      ∫ t in Set.Icc (0 : Fin m → ℝ) (fun _ => s), ‖Dv S t‖ ^ 2

def SobolevSum : Prop :=
  ∀ (m : ℕ) (s β X : ℝ) (I : Finset (Fin m) → ℝ), 0 < s → 0 ≤ β → s * β ≤ 1 → 0 ≤ X →
    (∀ S, I S ≤ β ^ (2 * S.card) * X) →
    (2 / s) ^ m * ∑ S : Finset (Fin m), s ^ (2 * S.card) * I S ≤ (4 / s) ^ m * X

end Formalism.HermitianLatticeCounting.S7
end
end

-- bundled from Formalism.FlagUnipotentLattices.LiftFixesBaseVector
section
namespace Formalism.HermitianLatticeCounting.Final.S6

theorem lift_fixes_base_vector : Formalism.HermitianLatticeCounting.S6.LiftUnitaryFixesBase := Formalism.HermitianLatticeCounting.P.lifting_fixes_base_vector
theorem liftUnitary : Formalism.HermitianLatticeCounting.S6.LiftUnitary := Formalism.HermitianLatticeCounting.P.lifting_unitary
theorem liftIsoW : Formalism.HermitianLatticeCounting.S6.LiftIsoW := Formalism.HermitianLatticeCounting.P.lifting_isometry_weight
theorem relIndexInter : Formalism.HermitianLatticeCounting.S6.RelIndexInter := Formalism.HermitianLatticeCounting.P.relIndex_intersection
theorem indexChain : Formalism.HermitianLatticeCounting.S6.IndexChain := Formalism.HermitianLatticeCounting.P.index_chain
theorem pairsLoss : Formalism.HermitianLatticeCounting.S6.PairsLoss := Formalism.HermitianLatticeCounting.P.pairs_loss_bound
theorem ratioSum : Formalism.HermitianLatticeCounting.S6.RatioSum := Formalism.HermitianLatticeCounting.P.ratio_sum_bound
theorem ratioBound : Formalism.HermitianLatticeCounting.S6.RatioBound := Formalism.HermitianLatticeCounting.P.ratio_bound_alt
theorem sEqKClose : Formalism.HermitianLatticeCounting.S6.SEqKClose := Formalism.HermitianLatticeCounting.P.equal_rank_close

end Formalism.HermitianLatticeCounting.Final.S6
end

