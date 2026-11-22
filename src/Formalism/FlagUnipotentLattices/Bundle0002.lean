import Formalism.FlagUnipotentLattices.GramSubmersionSplit
import Mathlib
import Formalism.HyperbolicPlaceProducts.Bundle0001
import Formalism.FlagUnipotentLattices.Bundle0001

-- bundled from Formalism.FlagUnipotentLattices.ConductorCharacterLeakBound
section
namespace Formalism.HermitianLatticeCounting.S4

open Finset

def WeightedAmplitudeSqSumBoundTwoTypeClasses : Prop :=
  ∀ (k r q : ℕ) (H nn : ℝ) (D Ty : Type) [Fintype D] [Fintype Ty]
    (w : D → ℝ) (amp : Ty → D → ℂ) (μ : Ty → D → ℝ) (be : Ty → ℝ) (isBe : Ty → Prop),
    4 * r + 7 ≤ k → 2 ≤ q → 1 ≤ H → (Nonempty Ty → (q : ℝ) ≤ H) → 0 ≤ nn →
    (∀ d, 0 ≤ w d) → (Fintype.card Ty : ℝ) ≤ H ^ (r + 2) →
    (∀ t, 1 ≤ be t) → (∀ t d, 0 ≤ μ t d) →
    (∀ t d, isBe t → μ t d ≤ 2 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * be t ^ (k - 1)) →
    (∀ t d, ¬ isBe t → μ t d ≤ 2 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (be t / q) ^ (k - 1)) →
    (∀ t, ∑ d, w d * μ t d ≤ 4 * H ^ (4 * (r + 1)) * (be t ^ (k - 1))⁻¹ * nn) →
    (∀ t d, ‖amp t d‖ ≤ μ t d) →
    (∀ t d, isBe t → ‖amp t d‖ ≤ 7 * (q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * μ t d) →
    ∑ d, w d * ‖∑ t, amp t d‖ ^ 2
      ≤ H ^ (39 * (r + 1) ^ 2) * (q : ℝ) ^ (-((k : ℤ) - 2 * r - 5)) * nn

def NonGenericBoundLargeHeight : Prop :=
  ∀ (k r : ℕ) (H nn : ℝ) (D Ty : Type) [Fintype D] [Fintype Ty]
    (w : D → ℝ) (amp : Ty → D → ℂ) (μ : Ty → D → ℝ) (be : Ty → ℝ),
    2 ≤ H → 0 ≤ nn → (∀ d, 0 ≤ w d) → (Fintype.card Ty : ℝ) ≤ H →
    (∀ t, 1 ≤ be t) → (∀ t d, 0 ≤ μ t d) →
    (∀ t d, μ t d ≤ 2 * H ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * be t ^ (k - 1)) →
    (∀ t, ∑ d, w d * μ t d ≤ 4 * H ^ (4 * (r + 1)) * (be t ^ (k - 1))⁻¹ * nn) →
    (∀ t d, ‖amp t d‖ ≤ μ t d) →
    ∑ d, w d * ‖∑ t, amp t d‖ ^ 2 ≤ H ^ (39 * (r + 1) ^ 2) * nn

def GeomPowers : Prop :=
  ∀ (q k N : ℕ), 2 ≤ q → 2 ≤ k →
    ∑ i ∈ range (N + 1), ((q : ℝ) ^ i) ^ (k - 1) ≤ 2 * ((q : ℝ) ^ N) ^ (k - 1)

def TypeCount : Prop :=
  ∀ (r a q : ℕ) (H : ℝ), 2 ≤ q → 1 ≤ a → (q : ℝ) ^ a ≤ H →
    ((r * (a + 1) ^ 2 + a : ℕ) : ℝ) ≤ H ^ (r + 2)

def CongruenceGroupIndexBound : Prop :=
  ∀ (q A S : ℝ) (r vth : ℕ), 1 ≤ q → 0 ≤ S → (vth : ℝ) + S ≤ A →
    q ^ ((r : ℝ) * (r + 1) * vth) * q ^ ((5 / 2 : ℝ) * (r + 1) * S) ≤ (q ^ A) ^ (9 * ((r : ℝ) + 1) ^ 2)

def GaussSumZeroCountBound : Prop :=
  ∀ (U T : Type) [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (χ : U → ℂ) (cond : AddChar T ℂ → ℕ) (q a ρ : ℕ),
    2 ≤ q → 4 ≤ ρ → Fintype.card T = q ^ a →
    (∀ ψ, cond ψ = 0 ↔ ψ = 0) →
    (∀ i, 1 ≤ i → ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) ≤ (q : ℝ) ^ i) →
    ∑ u, χ u = 0 →
    (∀ ψ : AddChar T ℂ, ψ ≠ 0 →
      ‖∑ u, ψ (Q u) * χ u‖ ≤ ((q : ℝ) ^ (cond ψ * ρ))⁻¹ * (Fintype.card U : ℝ)) →
    (∀ ψ : AddChar T ℂ, ψ ≠ 0 →
      ‖∑ u, ψ (Q u)‖ ≤ ((q : ℝ) ^ (cond ψ * ρ))⁻¹ * (Fintype.card U : ℝ)) →
    |((univ.filter fun u => Q u = 0).card : ℝ) - (Fintype.card U : ℝ) / (q : ℝ) ^ a|
        ≤ 8 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ)) * ((Fintype.card U : ℝ) / (q : ℝ) ^ a) ∧
    ‖∑ u ∈ univ.filter (fun u => Q u = 0), χ u‖
        ≤ 8 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ)) * ((Fintype.card U : ℝ) / (q : ℝ) ^ a)

def CondCountLe : Prop :=
  ∀ (o T : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [AddCommGroup T] [Fintype T]
    [DecidableEq T] (ϖ : o) (red : o →+ T) (cond : AddChar T ℂ → ℕ) (q a : ℕ),
    Irreducible ϖ → Nat.card (IsLocalRing.ResidueField o) = q → 2 ≤ q →
    Function.Surjective red → (∀ x, red x = 0 ↔ ϖ ^ a ∣ x) →
    (∀ ψ i, cond ψ ≤ i ↔ ∀ x, ψ (red (ϖ ^ i * x)) = 1) →
    ∀ j, ((univ.filter fun ψ : AddChar T ℂ => cond ψ ≤ j).card : ℝ) ≤ (q : ℝ) ^ j

def ConductorCharacterLeakBound : Prop :=
  ∀ (U T : Type) [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (cond : AddChar T ℂ → ℕ) (q a ρ j : ℕ),
    2 ≤ q → 4 ≤ ρ → Fintype.card T = q ^ a →
    ((univ.filter fun ψ : AddChar T ℂ => cond ψ ≤ j).card : ℝ) ≤ (q : ℝ) ^ j →
    (∀ i, j < i → ((univ.filter fun ψ : AddChar T ℂ => cond ψ = i).card : ℝ) ≤ (q : ℝ) ^ i) →
    (∀ ψ : AddChar T ℂ,
      ‖∑ u, ψ (Q u)‖ ≤ ((q : ℝ) ^ ((cond ψ - j) * ρ))⁻¹ * (Fintype.card U : ℝ)) →
    ((univ.filter fun u => Q u = 0).card : ℝ)
      ≤ 8 / 7 * (q : ℝ) ^ j * ((Fintype.card U : ℝ) / (q : ℝ) ^ a)

def TwistedRowSumsBound : Prop :=
  ∀ (B U Pl X Mv : Type) [Fintype B] [Fintype U] [Fintype Pl] [Fintype X]
    [Fintype Mv] [DecidableEq B] [DecidableEq U] [DecidableEq X]
    (vol : B → ℝ) (Z : Finset U) (UP : Pl → Finset U) (jj : Pl → ℕ) (χ : B → U → ℂ)
    (bb : Mv → B) (uu : Mv → U) (tgt : Mv → Option X) (μ : Mv → ℝ) (ω : X → ℂ) (ω₀ : ℂ) (q a ρ : ℕ),
    2 ≤ q → 4 ≤ ρ → Fintype.card Pl ≤ 2 → (∀ P, 1 ≤ jj P) → 0 < Fintype.card U →
    (∀ b, 0 ≤ vol b) → 0 < ∑ b, vol b → (∀ m, 0 ≤ μ m) →
    (∀ b u, ∑ m ∈ univ.filter (fun m => bb m = b ∧ uu m = u), μ m
      = if u ∈ Z then vol b / ((∑ b', vol b') * ((Fintype.card U : ℝ) / (q : ℝ) ^ a)) else 0) →
    |(Z.card : ℝ) - (Fintype.card U : ℝ) / (q : ℝ) ^ a|
        ≤ 8 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ)) * ((Fintype.card U : ℝ) / (q : ℝ) ^ a) →
    (∀ b, ‖∑ u ∈ Z, χ b u‖ ≤ 8 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ)) * ((Fintype.card U : ℝ) / (q : ℝ) ^ a)) →
    (∀ b u, ‖χ b u‖ = 1) →
    (∀ P, ((UP P).card : ℝ) = (Fintype.card U : ℝ) / (q : ℝ) ^ (jj P * ρ)) →
    (∀ P, ((Z ∩ UP P).card : ℝ) ≤ 8 / 7 * (q : ℝ) ^ jj P * (((UP P).card : ℝ) / (q : ℝ) ^ a)) →
    (∀ m, tgt m = none → ∃ P, uu m ∈ UP P) →
    (∀ m x, tgt m = some x → ω x = ω₀ * χ (bb m) (uu m)) →
    |(∑ x, ∑ m ∈ univ.filter (fun m => tgt m = some x), μ m) - 1| ≤ 24 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ)) ∧
    ‖∑ x, ((∑ m ∈ univ.filter (fun m => tgt m = some x), μ m : ℝ) : ℂ) * ω x‖
        ≤ 24 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ)) * ‖ω₀‖

def KernelAvg7 : Prop :=
  ∀ (ι : Type) (μ : ι → ℝ) (M : ι → ι → ℝ) (ω : ι → ℂ) (q ρ : ℕ),
    (∀ i, 0 ≤ μ i) → Summable μ → (∀ i j, 0 ≤ M i j) → (∀ i, Summable (M i)) →
    (∀ i j, μ i * M i j = μ j * M j i) → (∀ i, ‖ω i‖ = 1) →
    (∀ i, |(∑' j, M i j) - 1| ≤ 24 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ))) →
    (∀ i, ‖∑' j, (M i j : ℂ) * ω j‖ ≤ 24 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ))) →
    ‖∑' i, (μ i : ℂ) * ω i‖ ≤ 7 * (q : ℝ) ^ (1 - (ρ : ℤ)) * ∑' i, μ i

def TotientSqrt : Prop := ∀ w : ℕ, w ≤ 2 * Nat.totient w ^ 2

def NormalCount6 : Prop :=
  ∀ (f T T' NG : ℕ), 1 ≤ f → 3 ≤ T → 3 ≤ T' → 1 ≤ NG →
    (8 * f ^ 2) ^ 2 * (T ^ f * NG) ^ 2 * (T' ^ f * NG) ^ 2 ≤ (NG * (T * T') ^ f) ^ 6

end Formalism.HermitianLatticeCounting.S4
end

-- bundled from Formalism.FlagUnipotentLattices.IdealCountLeW
section
noncomputable section

open scoped BigOperators
open NumberField

namespace Formalism.HermitianLatticeCounting.S6

def IotaDual : Prop :=
  ∀ (K U : Type) [Field K] [StarRing K] [AddCommGroup U] [Module K U] (h : U →ₗ[K] U →ₗ⋆[K] K)
    (O : Subring K) (g : K) (L₀ L₀' : AddSubgroup U) (ι' : U → U),
    g ∈ O → star g = g → g ≠ 0 → (∀ x ∈ L₀, ∀ y ∈ L₀, h x y ∈ O) → (∀ x ∈ L₀', ι' x ∈ L₀) →
    (∀ x ∈ L₀', ∀ y ∈ L₀', ∃ t ∈ O, h (ι' x) (ι' y) - h x y = g * t) →
      (∀ l' ∈ L₀', ∀ x ∈ L₀ ⊓ L₀', (∃ l ∈ L₀, ι' x - x = g • l) → h (g⁻¹ • (l' - ι' l')) x ∈ O) ∧
      (∀ l' ∈ L₀ ⊓ L₀', (∃ l ∈ L₀, ι' l' - l' = g • l) → g⁻¹ • (l' - ι' l') ∈ L₀)

def IotaDetermined : Prop :=
  ∀ (K U : Type) [Field K] [AddCommGroup U] [Module K U] (g : K) (L₀ : AddSubgroup U) (ι₁ ι₂ : U → U) (l' : U),
    g ≠ 0 → g⁻¹ • (l' - ι₁ l') - g⁻¹ • (l' - ι₂ l') ∈ L₀ → ∃ l ∈ L₀, ι₁ l' - ι₂ l' = g • l

def hdual {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U] (h : U →ₗ[K] U →ₗ⋆[K] K)
    (O : Subring K) (M : AddSubgroup U) : AddSubgroup U where
  carrier := {x | ∀ y ∈ M, h x y ∈ O}
  add_mem' := by
    intro a b ha hb y hy
    simpa using O.add_mem (ha y hy) (hb y hy)
  zero_mem' := by
    intro y _
    simp
  neg_mem' := by
    intro a ha y hy
    simpa using O.neg_mem (ha y hy)

def DualIndex : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (U : Type) [AddCommGroup U] [Module E U]
    [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] [FiniteDimensional E U] (h : U →ₗ[E] U →ₗ⋆[E] E)
    (M N : Submodule (𝓞 E) U), (∀ x : U, (∀ y : U, h x y = 0) → x = 0) → N ≤ M → M.FG →
    Submodule.span E (N : Set U) = ⊤ →
      (hdual h (algebraMap (𝓞 E) E).range M.toAddSubgroup).relIndex
          (hdual h (algebraMap (𝓞 E) E).range N.toAddSubgroup) =
        N.toAddSubgroup.relIndex M.toAddSubgroup

def SubGen : Prop :=
  ∀ (R Q : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup Q] [Module R Q] [Finite Q] (e : ℕ)
    (s : Fin e → Q), Submodule.span R (Set.range s) = ⊤ →
      ∀ N : Submodule R Q, ∃ t : Fin e → Q, Submodule.span R (Set.range t) = N

def ExtGen : Prop :=
  ∀ (R Q : Type) [CommRing R] [AddCommGroup Q] [Module R Q] (N : Submodule R Q) (e₁ e₂ : ℕ)
    (s : Fin e₁ → Q) (t : Fin e₂ → Q ⧸ N), Submodule.span R (Set.range s) = N →
    Submodule.span R (Set.range t) = ⊤ → ∃ u : Fin (e₁ + e₂) → Q, Submodule.span R (Set.range u) = ⊤

def ColonScale : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (U : Type) [AddCommGroup U] [Module E U] (Lam₁ : Set U) (y : U)
    (c : E) (aa aa' : Ideal (𝓞 E)), c ≠ 0 →
    (∀ a : E, a • y ∈ Lam₁ ↔ ∃ a₀ ∈ aa, algebraMap (𝓞 E) E a₀ = a) →
    (∀ a : E, a • (c • y) ∈ Lam₁ ↔ ∃ a₀ ∈ aa', algebraMap (𝓞 E) E a₀ = a) →
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) c *
          (aa' : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) =
        (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)

def ColonNorm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (L : Type) [AddCommGroup L] [Module (𝓞 E) L]
    (Lam₁ : Submodule (𝓞 E) L) (y : L),
      Ideal.absNorm (Lam₁.comap (LinearMap.toSpanSingleton (𝓞 E) L y) : Ideal (𝓞 E)) ∣
        Lam₁.toAddSubgroup.index ∧
      (Lam₁.toAddSubgroup.index ≠ 0 →
        1 ≤ Ideal.absNorm (Lam₁.comap (LinearMap.toSpanSingleton (𝓞 E) L y) : Ideal (𝓞 E)) ∧
        Ideal.absNorm (Lam₁.comap (LinearMap.toSpanSingleton (𝓞 E) L y) : Ideal (𝓞 E)) ≤
          Lam₁.toAddSubgroup.index)

def IdealCountEq : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), 1 ≤ n →
    {I : Ideal (𝓞 E) | Ideal.absNorm I = n}.Finite ∧
      {I : Ideal (𝓞 E) | Ideal.absNorm I = n}.ncard ≤
        Module.finrank ℚ E ^ (Nat.primeFactorsList n).length

def IdealCountLe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (f y : ℕ), Module.finrank ℚ E = 2 * f →
    {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y}.Finite ∧
      (({I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y}.ncard : ℕ) : ℝ) ≤
        (y : ℝ) ^ (1 + Real.logb 2 (2 * f))

def TotientBound : Prop := ∀ n : ℕ, n ≤ 2 * Nat.totient n ^ 2

def TorsionBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (f : ℕ), Module.finrank ℚ E = 2 * f →
    Nat.card (NumberField.Units.torsion E) ≤ 8 * f ^ 2

def cSet (E : Type) [Field E] [NumberField E] (D : ℕ) : Set E :=
  {c : E | (∀ w : InfinitePlace E, w c = 1) ∧ ∃ aa aa' : Ideal (𝓞 E),
    1 ≤ Ideal.absNorm aa ∧ Ideal.absNorm aa ≤ D ∧ 1 ≤ Ideal.absNorm aa' ∧ Ideal.absNorm aa' ≤ D ∧
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) c *
        (aa' : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) =
      (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)}

def CCount : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (f D : ℕ), Module.finrank ℚ E = 2 * f →
    (cSet E D).Finite ∧
      (((cSet E D).ncard : ℕ) : ℝ) ≤ 8 * (f : ℝ) ^ 2 * (D : ℝ) ^ (2 * (1 + Real.logb 2 (2 * f)))

def CCountAsm : Prop := IdealCountLe → TorsionBound → CCount

def IdealCountLeW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (f y : ℕ), Module.finrank ℚ E = 2 * f →
    {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y}.Finite ∧
      (({I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y}.ncard : ℕ) : ℝ) ≤
        (y : ℝ) ^ (1 + (1 + Real.logb 2 (2 * f)))

def IdealCountLeW' : Prop := Formalism.SLP.SubmoduleIndexCountO → Formalism.SLP.OmegaPow → IdealCountLeW

def CCountW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (f D : ℕ), Module.finrank ℚ E = 2 * f →
    (cSet E D).Finite ∧
      (((cSet E D).ncard : ℕ) : ℝ) ≤ 8 * (f : ℝ) ^ 2 * (D : ℝ) ^ (2 + 2 * (1 + Real.logb 2 (2 * f)))

def CCountWAsm : Prop := IdealCountLeW → TorsionBound → CCountW

def TorsionBoundAsm : Prop := TotientBound → TorsionBound

def QuotCard : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite (𝓞 E) M] [Module.Projective (𝓞 E) M] (I : Ideal (𝓞 E)),
      Nat.card (M ⧸ (I • (⊤ : Submodule (𝓞 E) M))) = Ideal.absNorm I ^ Module.finrank (𝓞 E) M

def CostBound : Prop :=
  ∀ (C C₂ r : ℕ) (Db Del NT Ncc : ℝ), 1 ≤ r → 1 ≤ Del → Del ≤ Db → 1 ≤ NT → 0 ≤ Ncc →
    Ncc ≤ (Db * Del * NT) ^ (C * r) →
      Ncc ^ (2 * (2 * r + 1) ^ 2) * (Del * NT) ^ (2 * (2 * r + 1)) * (Ncc ^ 2) ^ (C₂ * r ^ 2) ≤
        (Db * NT) ^ ((36 * C + 4 * C * C₂ + 6) * r ^ 3)

def HLoss : Prop :=
  ∀ (C C' r f : ℕ) (b : ℝ), 1 ≤ b →
    (b ^ (C * (2 * r + 2) ^ 2 * f)) ^ (C' * r ^ 4) ≤
      Real.exp ((C : ℝ) * C' * ((2 * r + 2 : ℕ) : ℝ) ^ 6 * f * Real.log b)

end Formalism.HermitianLatticeCounting.S6
end
end

-- bundled from Formalism.FlagUnipotentLattices.UnitSumBound
section
open Finset

noncomputable section

namespace Formalism.HermitianLatticeCounting.LocalIntegralStructure

def UnitSumBound : Prop :=
  ∀ (V ι : Type) [SeminormedAddCommGroup V] [NormedSpace ℂ V] (s : Finset ι) (a : ι → ℂ)
    (x : ι → V) (w B : ℝ), 0 ≤ w → (∀ i ∈ s, w * ‖x i‖ ^ 2 ≤ B) →
    w * ‖∑ i ∈ s, a i • x i‖ ^ 2 ≤ B * (∑ i ∈ s, ‖a i‖) ^ 2

def volU (j : ℕ) : ℝ := ∏ i ∈ Icc 1 j, (2 * Real.pi) ^ i / ((i - 1).factorial : ℝ)

def VolStep : Prop :=
  ∀ j : ℕ, volU j / volU (j + 1) = (j.factorial : ℝ) / (2 * Real.pi) ^ (j + 1)

def VolRatio : Prop :=
  ∀ k p : ℕ, volU (k + p) / volU k * ∏ i ∈ Ico k (k + p), (i.factorial : ℝ) =
    (2 * Real.pi) ^ (p * k + p * (p + 1) / 2)

def ConstProduct : Prop :=
  ∀ (j r : ℕ) (T T' g v n0 κ dimpi Vd VV : ℝ), 0 < T → 0 < T' → 0 < g → 0 < v → VV ≠ 0 →
    n0 * (j.factorial : ℝ) / (2 * Real.pi) ^ (j + 1) =
      κ / (g ^ (2 * r + 2) * T * (2 * v)) ^ (j + 1) →
    n0 * (T * T') ^ j *
      (dimpi * (Vd / ∏ i ∈ range (j + 1), (i.factorial : ℝ)) * volU (j + 1 + (2 * r + 1)) * volU j /
        (VV / (∏ i ∈ range (j + 1 + (2 * r + 1)), (i.factorial : ℝ)) * volU (j + 1) ^ 2 *
          (2 * v) ^ (2 * r * (j + 1)))) =
      dimpi * (T' / g ^ (2 * r + 2) * (Real.pi / v) ^ (2 * r + 1)) ^ (j + 1) * (Vd / VV) *
        (κ * (2 * Real.pi) ^ ((2 * r + 1) * (2 * r + 2) / 2) / (T * T'))

def TcritForm : Prop :=
  ∀ (k r : ℕ) (T' g v rd Vd VV Tc : ℝ), 0 < T' → 0 < g → 0 < v → 0 < rd → Vd ≠ 0 → VV ≠ 0 →
    0 < Tc →
    Tc ^ k * ((Real.pi / v) ^ ((2 * r + 1) * k + (2 * r + 2) * (2 * r + 1) / 2) *
        rd ^ (((2 * r + 1 : ℕ) : ℝ) / 2)) =
      g ^ (k * (2 * r + 2) + (2 * r + 2) * (2 * r + 1) / 2) * (VV / Vd) →
    (T' / g ^ (2 * r + 2) * (Real.pi / v) ^ (2 * r + 1)) ^ k * (Vd / VV) =
      (Tc / T')⁻¹ ^ k *
        ((g / (Real.pi / v)) ^ ((2 * r + 2) * (2 * r + 1) / 2) / rd ^ (((2 * r + 1 : ℕ) : ℝ) / 2))

def PlaceRoot : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (x y : ι → ℝ) (K B₁ B₂ : ℝ), 0 ≤ K → 0 ≤ B₁ → 0 ≤ B₂ →
    (∀ v, 0 < y v) → (∀ v, x v = K * y v) →
    B₁ ^ Fintype.card ι * ∏ v, y v ≤ ∏ v, x v → ∏ v, x v ≤ B₂ ^ Fintype.card ι * ∏ v, y v →
    ∀ v, B₁ * y v ≤ x v ∧ x v ≤ B₂ * y v

end Formalism.HermitianLatticeCounting.LocalIntegralStructure
end
end

