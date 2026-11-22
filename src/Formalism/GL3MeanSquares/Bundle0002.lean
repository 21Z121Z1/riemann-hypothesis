import Mathlib
import Formalism.GL3MeanSquares.OrbitPointsDistinct
import Formalism.HermitianLattices.Bundle0003
import Formalism.LogVandermondeBounds.Bundle0001
import Formalism.LogVandermondeBounds.Bundle0002
import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne
import Formalism.GL3MeanSquares.HookFormulaTorsion.ConditionIffDualEqFunctional
import Formalism.GL3MeanSquares.HookFormulaTorsion.FourierCommutesHeckeScalar
import Formalism.GL3MeanSquares.HookFormulaTorsion.LengthQuotientBoundGeneral
import Formalism.GL3MeanSquares.HookFormulaTorsion.LemmaCTwistRamified

-- bundled from Formalism.GL3MeanSquares.CongruenceTorsion
section
open NumberField IntermediateField Ideal IsDedekindDomain
open scoped Pointwise TensorProduct

noncomputable section

namespace Formalism.HermitianLattices.StabilizerLevels

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.HermitianLattices.FiltrationBoundaryCriterion

def HostEOverF : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ x : hostE ζ a b,
    (∃ u ∈ hostF ζ a b, ∃ v ∈ hostF ζ a b, x = u + v * bE ζ a b) ∧
    (∃ u ∈ hostF ζ a b, ∃ v ∈ hostF ζ a b, x = u + v * aE ζ a b)

def HostQuadSub : Prop :=
  ∀ (e q d : ℕ), 1 ≤ e → HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ m : ℤ, Squarefree m →
    ((∃ x : hostE ζ a b, x ^ 2 = (m : hostE ζ a b)) ↔
      (m = 1 ∨ m = 2 ∨ m = -(q : ℤ) ∨ m = -(d : ℤ) ∨ m = (q : ℤ) * d ∨ m = -2 * (q : ℤ) ∨
        m = -2 * (d : ℤ) ∨ m = 2 * (q : ℤ) * d))

def CongruenceTorsion : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (g k : ℕ), g.Prime → (g : R) ∈ I →
    (⨅ m : ℕ, I ^ m) = ⊥ →
  ∀ A : Matrix (Fin k) (Fin k) R, (∀ i j, (A - 1) i j ∈ I) →
  ∀ N : ℕ, 0 < N → A ^ N = 1 → ∃ m : ℕ, A ^ (g ^ m) = 1

def UnipotentPowers : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (g k : ℕ), g.Prime → (g : R) ∈ I →
  ∀ A : Matrix (Fin k) (Fin k) R, (∀ i j, j ≤ i → (A - 1) i j ∈ I) →
  ∀ s : ℕ, k ≤ g ^ s → ∀ i j, (A ^ (g ^ s) - 1) i j ∈ I

def NilpotentPowers : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (g k : ℕ), g.Prime → (g : R) ∈ I →
  ∀ (A : Matrix (Fin k) (Fin k) R) (N : ℕ), (∀ i j, ((A - 1) ^ N) i j ∈ I) →
  ∀ s : ℕ, N ≤ g ^ s → ∀ i j, (A ^ (g ^ s) - 1) i j ∈ I

def StabLevelG : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (k : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E),
    (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    Formalism.UG.IsHerm (σ : E →+* E) J → IsUnit J.det → Formalism.UG.IsTotDef σ J →
  ∀ U : Subgroup (Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    U ≤ Formalism.UG.levelAf σ J →
  ∀ (w : HeightOneSpectrum (𝓞 F)) (g : ℕ), g.Prime → (g : 𝓞 F) ∈ w.asIdeal →
    Module.finrank ℚ E * k < g - 1 →
    (∀ x ∈ U, ∀ i j : Fin k,
      ∃ r ∈ Formalism.UG.tensInt (F := F) (w.adicCompletion F) (Formalism.UG.intOE E)
        (w.adicCompletionIntegers F).toSubring,
      ((Formalism.UG.bc (Formalism.UG.prV (E := E) w) x :
          Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin k) (Fin k) (E ⊗[F] w.adicCompletion F)) i j -
        (1 : Matrix (Fin k) (Fin k) (E ⊗[F] w.adicCompletion F)) i j =
          (g : E ⊗[F] w.adicCompletion F) * r) →
    Formalism.UG.IsNeat
      ((Formalism.UG.ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf
        (Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)))
      (U.subgroupOf (Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)))

def StabLevelProG : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (k : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E),
    (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    Formalism.UG.IsHerm (σ : E →+* E) J → IsUnit J.det → Formalism.UG.IsTotDef σ J →
  ∀ U : Subgroup (Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    U ≤ Formalism.UG.levelAf σ J →
  ∀ (w : HeightOneSpectrum (𝓞 F)) (g : ℕ), g.Prime → (g : 𝓞 F) ∈ w.asIdeal →
    Module.finrank ℚ E * k < g - 1 →
    (∀ x ∈ U, ∃ s : ℕ, ∀ i j : Fin k,
      ∃ r ∈ Formalism.UG.tensInt (F := F) (w.adicCompletion F) (Formalism.UG.intOE E)
        (w.adicCompletionIntegers F).toSubring,
      (((Formalism.UG.bc (Formalism.UG.prV (E := E) w) x :
          Matrix.GeneralLinearGroup (Fin k) (E ⊗[F] w.adicCompletion F)) :
        Matrix (Fin k) (Fin k) (E ⊗[F] w.adicCompletion F)) ^ (g ^ s)) i j -
        (1 : Matrix (Fin k) (Fin k) (E ⊗[F] w.adicCompletion F)) i j =
          (g : E ⊗[F] w.adicCompletion F) * r) →
    Formalism.UG.IsNeat
      ((Formalism.UG.ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf
        (Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)))
      (U.subgroupOf (Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)))

def IsForm {G W : Type} [Group G] (Γ U : Subgroup G) [MulAction U W] (f : G → W) : Prop :=
  ∀ γ ∈ Γ, ∀ (u : U) (g : G), f (γ * g * (u : G)) = u⁻¹ • f g

def FormsExact : Prop :=
  ∀ (G : Type) [Group G] (Γ U : Subgroup G),
    (∀ y : G, ∀ γ ∈ Γ, y⁻¹ * γ * y ∈ U → γ = 1) →
  ∀ (W₁ W₂ W₃ : Type) [AddCommGroup W₁] [AddCommGroup W₂] [AddCommGroup W₃]
    [DistribMulAction U W₁] [DistribMulAction U W₂] [DistribMulAction U W₃]
    (a : W₁ →+ W₂) (b : W₂ →+ W₃),
    (∀ (u : U) (x : W₁), a (u • x) = u • a x) → (∀ (u : U) (x : W₂), b (u • x) = u • b x) →
    (∀ y : W₂, b y = 0 ↔ ∃ x : W₁, a x = y) →
    (∀ f : G → W₂, IsForm Γ U f → (∀ g, b (f g) = 0) →
      ∃ f' : G → W₁, IsForm Γ U f' ∧ ∀ g, a (f' g) = f g) ∧
    (Function.Surjective b → ∀ f'' : G → W₃, IsForm Γ U f'' →
      ∃ f : G → W₂, IsForm Γ U f ∧ ∀ g, b (f g) = f'' g)

def PrincipalRiemann : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ = cc e →
  ∀ 𝔟 : Ideal (𝓞 (hostE ζ a b)),
    differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟 * (σ • 𝔟) →
  ∀ 𝔠 : Ideal (𝓞 (KinE ζ a b)), 𝔠 ≠ ⊥ →
  ∀ ξ : hostE ζ a b, ξ * (((Ideal.absNorm 𝔠 : ℕ) : hostE ζ a b) * bE ζ a b) = -1 →
    σ ξ = -ξ ∧
    (∀ φ ∈ cmType ζ a b d, 0 < (φ ξ).im) ∧
    ∀ x : hostE ζ a b,
      x ∈ (((𝔠.map (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) : Ideal (𝓞 (hostE ζ a b))) :
            FractionalIdeal (nonZeroDivisors (𝓞 (hostE ζ a b))) (hostE ζ a b)) *
          ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 (hostE ζ a b))) (hostE ζ a b))⁻¹)) ↔
        ∀ y ∈ (((𝔠.map (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) :
              Ideal (𝓞 (hostE ζ a b))) :
            FractionalIdeal (nonZeroDivisors (𝓞 (hostE ζ a b))) (hostE ζ a b)) *
          ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 (hostE ζ a b))) (hostE ζ a b))⁻¹)),
          Algebra.trace ℚ (hostE ζ a b) (ξ * x * σ y) ∈ (algebraMap ℤ ℚ).range

end Formalism.HermitianLattices.StabilizerLevels
end
end

-- bundled from Formalism.GL3MeanSquares.MassLowerBoundClosed
section
open NumberField Finset

namespace Formalism.HermitianLattices.SiegelMassBounds

def SiegelMassRatioThm : Prop := Formalism.HermitianLatticesTheory.SiegelMassRatio

def MassLowerBoundClosed : Prop :=
  ∀ (ε C₀ : ℝ), 0 < ε → ε < 1 / 52 → 0 ≤ C₀ → ∃ C : ℝ, ∀ (x : ℝ), 1 ≤ x →
    let L := x ^ ε
    let B := Real.exp L
    let a := x * B
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [Module (RingOfIntegers K) V]
      [IsScalarTower (RingOfIntegers K) K V] [AddCommGroup V'] [Module K V']
      [Module (RingOfIntegers K) V'] [IsScalarTower (RingOfIntegers K) K V']
      (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K)
      (Lk : Submodule (RingOfIntegers K) V) (Lr : Submodule (RingOfIntegers K) V')
      (m k : ℕ) (Δ g₁ g₂ : ℝ) (u v b w : ℕ → ℕ → ℝ) (Dstar dstar Isig Ipi : ℝ),
    h.IsSymm → h'.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h Lk k →
    Formalism.HermitianLatticesTheory.IsOrthoLattice h' Lr (k - 1 + m) →
    1 ≤ Formalism.HermitianLatticesTheory.fDeg K → 1 ≤ m → 2 ≤ k → (k : ℝ) ≤ x ^ C₀ →
    Real.pi ≤ Formalism.HermitianLatticesTheory.vInv K → Real.log (Formalism.HermitianLatticesTheory.vInv K) ≤ L → 1 ≤ Δ → 1 ≤ g₁ → 1 ≤ g₂ →
    (∀ ρ, ρ < Formalism.HermitianLatticesTheory.fDeg K → Formalism.LogVandermondeBounds.StandardLattice.PlaceData x Δ a B k m (u ρ) (v ρ) (b ρ) (w ρ)) →
    0 < Formalism.HermitianLatticesTheory.mass h Lk → 0 < Formalism.HermitianLatticesTheory.mass h' Lr → 0 < Isig → 0 < Ipi →
    (∀ M ∈ Ico (k + 1) (k - 1 + m + 1), 0 < Formalism.HermitianLatticesTheory.lValEta K M ∧
      |Real.log (Formalism.HermitianLatticesTheory.lValEta K M)| ≤ Formalism.HermitianLatticesTheory.fDeg K * Real.log (Formalism.LogVandermondeBounds.StandardLattice.zetaR M)) →
    (hidx : ((2 : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K))⁻¹ *
      (g₁ * g₂) ^ ((Formalism.HermitianLatticesTheory.fDeg K : ℝ) * m * (2 * k + m - 1) / 2) ≤ Isig / Ipi) →
    (hD : (2 / 3 : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg K * Formalism.HermitianLatticesTheory.mass h' Lr * Isig *
      ∏ ρ ∈ range (Formalism.HermitianLatticesTheory.fDeg K), Formalism.LogVandermondeBounds.StandardLattice.dimVN (Formalism.LogVandermondeBounds.StandardLattice.rowPar k (v ρ) (b ρ)) (k - 1 + m)
        ≤ Dstar) →
    (hd : dstar = Formalism.HermitianLatticesTheory.mass h Lk * Ipi * ∏ ρ ∈ range (Formalism.HermitianLatticesTheory.fDeg K), Formalism.LogVandermondeBounds.StandardLattice.dimVN (u ρ) k) →
    (∑ j ∈ range m, (1 / (Formalism.HermitianLatticesTheory.fDeg K : ℝ)) * ∑ ρ ∈ range (Formalism.HermitianLatticesTheory.fDeg K),
        Real.log (w ρ j * Formalism.HermitianLatticesTheory.vInv K / Real.pi))
        + m * (Real.log g₁ + Real.log g₂) - C * (L + (m : ℝ) ^ 2 * L / k)
      ≤ (1 / ((Formalism.HermitianLatticesTheory.fDeg K : ℝ) * k)) * Real.log (Dstar / dstar)

def MassUpperBoundClosed : Prop :=
  ∀ (ε C₀ C₃ : ℝ), 0 < ε → ε < 1 / 52 → 0 ≤ C₀ → 1 ≤ C₃ → ∃ C : ℝ, ∀ (x : ℝ), 1 ≤ x →
    let L := x ^ ε
    let B := Real.exp L
    let a := x * B
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [Module (RingOfIntegers K) V]
      [IsScalarTower (RingOfIntegers K) K V] [AddCommGroup V'] [Module K V']
      [Module (RingOfIntegers K) V'] [IsScalarTower (RingOfIntegers K) K V']
      (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K)
      (Lk : Submodule (RingOfIntegers K) V) (Lr : Submodule (RingOfIntegers K) V')
      (m k : ℕ) (Δ g₁ g₂ : ℝ) (u v b w : ℕ → ℕ → ℝ) (Dstar dstar Isig Ipi : ℝ) (dsig : ℕ → ℝ),
    h.IsSymm → h'.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h Lk k →
    Formalism.HermitianLatticesTheory.IsOrthoLattice h' Lr (k - 1 + m) →
    1 ≤ Formalism.HermitianLatticesTheory.fDeg K → 2 ≤ m → Even m → 2 ≤ k → (m : ℝ) ^ 2 * L ≤ k → (k : ℝ) ≤ x ^ C₀ →
    Real.pi ≤ Formalism.HermitianLatticesTheory.vInv K → Real.log (Formalism.HermitianLatticesTheory.vInv K) ≤ L → 1 ≤ Δ → 1 ≤ g₁ → 1 ≤ g₂ →
    Real.log g₁ ≤ C₀ * L → Real.log g₂ ≤ C₀ * L →
    (∀ ρ, ρ < Formalism.HermitianLatticesTheory.fDeg K → Formalism.LogVandermondeBounds.StandardLattice.PlaceData x Δ a B k m (u ρ) (v ρ) (b ρ) (w ρ) ∧
      (∀ i j, i < j → j < k → 1 ≤ u ρ i - u ρ j)) →
    0 < Formalism.HermitianLatticesTheory.mass h Lk → 0 < Formalism.HermitianLatticesTheory.mass h' Lr → 0 < Isig → 0 < Ipi →
    (∀ M ∈ Ico (k + 1) (k - 1 + m + 1), 0 < Formalism.HermitianLatticesTheory.lValEta K M ∧
      |Real.log (Formalism.HermitianLatticesTheory.lValEta K M)| ≤ Formalism.HermitianLatticesTheory.fDeg K * Real.log (Formalism.LogVandermondeBounds.StandardLattice.zetaR M)) →
    (hidx : Isig / Ipi ≤ (2 : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) *
      (g₁ * g₂) ^ ((Formalism.HermitianLatticesTheory.fDeg K : ℝ) * m * (2 * k + m - 1) / 2)) →
    (hD : Dstar = Formalism.HermitianLatticesTheory.mass h' Lr * Isig * ∏ ρ ∈ range (Formalism.HermitianLatticesTheory.fDeg K), dsig ρ) →
    (h3 : ∀ ρ, ρ < Formalism.HermitianLatticesTheory.fDeg K → 0 < dsig ρ ∧
      dsig ρ ≤ 4 * Formalism.LogVandermondeBounds.StandardLattice.dTau k m (Formalism.LogVandermondeBounds.StandardLattice.rowPar k (v ρ) (b ρ)) *
      (C₃ * ((k - 1 + m / 2 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) * ((k - 1 + m : ℕ) : ℝ) *
        (v ρ 0 + b ρ (m - 1))) ^ ((k - 1 + m / 2) * (m / 2))) →
    (hd : dstar = Formalism.HermitianLatticesTheory.mass h Lk * Ipi * ∏ ρ ∈ range (Formalism.HermitianLatticesTheory.fDeg K), Formalism.LogVandermondeBounds.StandardLattice.dimVN (u ρ) k) →
    (1 / ((Formalism.HermitianLatticesTheory.fDeg K : ℝ) * k)) * Real.log (Dstar / dstar) ≤ C * m * L

end Formalism.HermitianLattices.SiegelMassBounds
end

-- bundled from Formalism.GL3MeanSquares.ModelCocycleExponent
section
namespace Formalism.HermitianLattices.ModelCocycles

open Finset Formalism.HermitianLattices.IntegralLatticeDensity

def AdjointFromNorm : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm : O → Z),
    (∀ α, algebraMap Z O (nm α) = star α * α) →
    (∀ (z : Z) a b, cob φ a (algebraMap Z O z • b) = z • cob φ a b) →
    ∀ α : Oˣ, (∀ u, φ ((α : O) • u) = nm α • φ u) →
      ∀ a b, cob φ ((α : O) • a) b = cob φ a (star (α : O) • b)

def AdjointAdd : Prop :=
  ∀ (O M Q : Type) [CommRing O] [StarRing O] [AddCommGroup M] [Module O M] [AddCommGroup Q]
    (φ : M → Q), (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    ∀ α α' : O, (∀ a b, cob φ (α • a) b = cob φ a (star α • b)) →
      (∀ a b, cob φ (α' • a) b = cob φ a (star α' • b)) →
      ∀ a b, cob φ ((α + α') • a) b = cob φ a (star (α + α') • b)

def SplitVanish : Prop :=
  ∀ (Z M Q : Type) [CommRing Z] [AddCommGroup M] [Module Z M] [AddCommGroup Q] [Module Z Q]
    (φ : M → Q) (a abar : Z),
    (∀ x x' y, cob φ (x + x') y = cob φ x y + cob φ x' y) →
    (∀ (z : Z) x y, cob φ (z • x) y = z • cob φ x y) →
    (∀ x y, cob φ (a • x) y = cob φ x (abar • y)) →
    IsUnit (a - abar) → (∀ u, φ (-u) = φ u) → φ 0 = 0 → (∀ x : Q, x + x = 0 → x = 0) →
    (∀ x y, cob φ x y = 0) ∧ ∀ u, φ u = 0

def IsotropicZero : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm : O → Z),
    Function.Injective (algebraMap Z O) →
    (∀ α, algebraMap Z O (nm α) = star α * α) →
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b)) →
    (∀ (α : O) u, φ (α • u) = nm α • φ u) →
    ∀ (n ι : Type) [Fintype n] [Fintype ι] (f : ι → n → O),
      (∀ e e', ∑ i, star (f e i) * f e' i = 0) →
      ∀ t : ι → M, ∑ i, φ (∑ e, f e i • t e) = 0

def CrossTermsVanish : Prop :=
  ∀ (M N Q : Type) [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q] (Φ : M × N → Q),
    (∀ a a' b, cob Φ (a + a') b = cob Φ a b + cob Φ a' b) →
    (∀ x y, Φ (-x, y) = Φ (x, y)) →
    ∀ x y, cob Φ (x, 0) (0, y) + cob Φ (x, 0) (0, y) = 0

def EqualPowers : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (σ : Type) (N : ℕ)
    (f g : MvPowerSeries σ R), 0 < N →
    MvPowerSeries.constantCoeff f = 1 → MvPowerSeries.constantCoeff g = 1 → f ^ N = g ^ N → f = g

def JetsOfLogUnit : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (U f : PowerSeries K),
    (∀ n, PowerSeries.coeff n U ∈ R) → PowerSeries.constantCoeff U = 1 →
    PowerSeries.derivative K f * U = PowerSeries.derivative K U →
    ∀ n : ℕ, 1 ≤ n → (n.factorial : K) * PowerSeries.coeff n f ∈ R

def GenusOneCharacter : Prop :=
  ∀ x : ZMod 2 × ZMod 2,
    (if x = 0 then (1 : ℤ) else -1) * (-1) ^ (x.1 + x.2).val = (-1) ^ (x.1 * x.2).val

def EpsTeichAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ ε : WittVector p (AlgebraicClosure (ZMod p)),
      ε ^ (p ^ 2 - 1) = -1 → WittVector.frobenius (WittVector.frobenius ε) = -ε

def ChiPower : Prop :=
  ∀ (E : Type) [Field E] [StarRing E] (Ψ : Finset (E →+* ℂ))
    (A : Type) [CommGroup A] (ι : unitary E →* A) (K : Subgroup A) (χ : A →* Circle),
    (∀ k ∈ K, χ k = 1) →
    (∀ z : unitary E, ((χ (ι z) : Circle) : ℂ) = ∏ τ ∈ Ψ, (τ (z : E))⁻¹) →
    ∀ (t : A) (h : ℕ) (z : unitary E) (k : A), k ∈ K → t ^ h = ι z * k →
      ((χ t : Circle) : ℂ) ^ h = ∏ τ ∈ Ψ, (τ (z : E))⁻¹

def ChiModulusAll : Prop :=
  ∀ (E : Type) [Field E] [StarRing E] (Ψ : Finset (E →+* ℂ))
    (A : Type) [CommGroup A] (ι : unitary E →* A) (K : Subgroup A) (χ : A →* Circle),
    (∀ (τ : E →+* ℂ) (x : E), τ (star x) = (starRingEnd ℂ) (τ x)) →
    (∀ k ∈ K, χ k = 1) →
    (∀ z : unitary E, ((χ (ι z) : Circle) : ℂ) = ∏ τ ∈ Ψ, (τ (z : E))⁻¹) →
    ∀ (t : A) (h : ℕ) (z : unitary E) (k : A), 0 < h → k ∈ K → t ^ h = ι z * k →
      ∀ s : ℂ →+* ℂ, ‖s ((χ t : Circle) : ℂ)‖ = 1

def ModelCocycleExponent : Prop :=
  ∀ (E V : Type) [Field E] [CharZero E] [StarRing E] [AddCommGroup V] (h : V → V → E) (s : E),
    (∀ x x' y, h (x + x') y = h x y + h x' y) → (∀ x y, h x y = star (h y x)) → star s = -s →
    ∀ (x y : V) (a b : E), star a = a → star b = b → h x y = (a + b * s) / 2 →
      b / 2 - (h (x + y) (x + y) - h x x - h y y) / 2 = (b - a) / 2

def ModelCocycleTwo : Prop :=
  ∀ d : ℕ, d % 8 = 7 →
    (∃ δ : ℚ_[2], δ ^ 2 = -(d : ℚ_[2])) ∧
    ∀ δ : ℚ_[2], δ ^ 2 = -(d : ℚ_[2]) →
      ‖(1 - δ) / (2 * δ)‖ ≤ 1 ∧ ‖(-(1 + δ)) / (2 * δ)‖ ≤ 1 ∧
      ∀ a b : ℚ_[2],
        ((1 - δ) / (2 * δ)) * ((a + b * δ) / 2) + ((-(1 + δ)) / (2 * δ)) * ((a - b * δ) / 2) =
          (b - a) / 2

end Formalism.HermitianLattices.ModelCocycles
end

-- bundled from Formalism.GL3MeanSquares.PrimeOrderRamificationResults
section
namespace Formalism.HermitianLattices.Final

theorem coset_kernel_results :
    Formalism.HermitianLattices.LocalLatticeBases.SumZeroLatticeSpanning ∧
    Formalism.HermitianLattices.LocalLatticeBases.SlopeTensorProductAdditive ∧
    Formalism.HermitianLattices.LocalLatticeBases.LemmaB'_avg ∧
    Formalism.HermitianLattices.LocalLatticeBases.LemmaB'_twist ∧
    Formalism.HermitianLattices.LocalLatticeBases.SupportCosetStructure ∧
    Formalism.HermitianLattices.LocalLatticeBases.LinearFormIntegralityOnSupport ∧
    Formalism.HermitianLattices.LocalLatticeBases.ExponentLossPerEmbedding ∧
    Formalism.HermitianLattices.LocalLatticeBases.IndicatorKernelSum ∧
    Formalism.HermitianLattices.LocalLatticeBases.NonintegralMatrixPreservesThirdOverlattice ∧
    Formalism.HermitianLattices.LocalLatticeBases.SupportVolumeIndex ∧
    Formalism.HermitianLattices.LocalLatticeBases.OddHalfShiftSignDichotomyBound ∧
    Formalism.HermitianLattices.LocalLatticeBases.HeckeKernelScalarInvariance ∧
    Formalism.HermitianLattices.LocalLatticeBases.HeckeProductCommutation ∧
    Formalism.HermitianLattices.LocalLatticeBases.LengthQuotientPowerInjective ∧
    Formalism.HermitianLattices.LocalLatticeBases.LengthQuotientTwistFormula ∧
    Formalism.HermitianLattices.LocalLatticeBases.ConsecutiveRatioPowerBound ∧
    Formalism.HermitianLattices.LocalLatticeBases.ExponentTotalBound ∧
    Formalism.HermitianLattices.LocalLatticeBases.KroneckerRootOfUnity ∧
    Formalism.HermitianLattices.LocalLatticeBases.InterlacingDegreeDifference ∧
    Formalism.HermitianLattices.LocalLatticeBases.KernelDimensionCount ∧
    Formalism.HermitianLattices.LocalLatticeBases.CharacterSumCancellation ∧
    Formalism.HermitianLattices.LocalLatticeBases.PrimitiveOrbitFunctionalUnique ∧
    Formalism.HermitianLattices.LocalLatticeBases.FourierCommutesHeckeScalar ∧
    Formalism.HermitianLattices.LocalLatticeBases.FourierTransformKernelSurjective ∧
    Formalism.HermitianLattices.LocalLatticeBases.QuotientLengthEmbeddingBound ∧
    Formalism.HermitianLattices.LocalLatticeBases.Joint_coef :=
  ⟨Formalism.HermitianLattices.LocalLatticeBases.sum_zero_lattice_spanning,
   Formalism.HermitianLattices.LocalLatticeBases.slope_kronecker_formula,
   Formalism.HermitianLattices.LocalLatticeBases.length_average_bound,
   Formalism.HermitianLattices.LocalLatticeBases.length_bound_under_twist,
   Formalism.HermitianLattices.LocalLatticeBases.coset_decomposition,
   Formalism.HermitianLattices.LocalLatticeBases.linear_form_integrality_on_support,
   Formalism.HermitianLattices.LocalLatticeBases.exponent_loss_per_embedding,
   Formalism.HermitianLattices.LocalLatticeBases.kernel_description,
   Formalism.HermitianLattices.LocalLatticeBases.weaker_displayed_bound,
   Formalism.HermitianLattices.LocalLatticeBases.supportVolumeIndex_statement,
   Formalism.HermitianLattices.LocalLatticeBases.odd_half_shift_sign_dichotomy_bound,
   Formalism.HermitianLattices.LocalLatticeBases.hecke_kernel_scalar_invariance,
   Formalism.HermitianLattices.LocalLatticeBases.commuting_operators,
   Formalism.HermitianLattices.LocalLatticeBases.length_quotient_power_injective,
   Formalism.HermitianLattices.LocalLatticeBases.length_quotient_twist_formula,
   Formalism.HermitianLattices.LocalLatticeBases.consecutive_ratio_power_bound,
   Formalism.HermitianLattices.LocalLatticeBases.exponent_total_bound,
   Formalism.HermitianLattices.LocalLatticeBases.kronecker_root_of_unity',
   Formalism.HermitianLattices.LocalLatticeBases.interlacing_degree_difference,
   Formalism.HermitianLattices.LocalLatticeBases.point_count_formula,
   Formalism.HermitianLattices.LocalLatticeBases.fourier_jacobi_count,
   Formalism.HermitianLattices.LocalLatticeBases.primitive_orbit_functional_unique,
   Formalism.HermitianLattices.LocalLatticeBases.fourier_commutes_hecke_scalar,
   Formalism.HermitianLattices.LocalLatticeBases.fourier_transform_kernel_surjective,
   Formalism.HermitianLattices.LocalLatticeBases.quotient_length_embedding_bound,
   Formalism.HermitianLattices.LocalLatticeBases.joint_coefficient_formula⟩

theorem prime_order_ramification_results :
    Formalism.HermitianLattices.RamifiedHeckeModels.RationalMatrixPrimeOrderBound ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.LogRatioAtMostOne ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.LemmaC_twist ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.LemmaC_twist_ram ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.TableauExponentRange ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.ConjRatioPowUnitModulus ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.HeckeKernelPreservesRamified ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.LatticeColumnOperatorBound ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.CauchySchwarzUnitModulus ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.ImprimitiveOrbitCondition :=
  ⟨Formalism.HermitianLattices.RamifiedHeckeModels.prime_order_element,
   Formalism.HermitianLattices.RamifiedHeckeModels.logarithmic_bound,
   Formalism.HermitianLattices.RamifiedHeckeModels.lemma_c_under_twist,
   Formalism.HermitianLattices.RamifiedHeckeModels.lemma_c_twist_ramified,
   Formalism.HermitianLattices.RamifiedHeckeModels.exponent_bounds,
   Formalism.HermitianLattices.RamifiedHeckeModels.coprime_case_decomposition,
   Formalism.HermitianLattices.RamifiedHeckeModels.ramified_decomposition,
   Formalism.HermitianLattices.RamifiedHeckeModels.column_decomposition,
   Formalism.HermitianLattices.RamifiedHeckeModels.cauchy_schwarz_bound,
   Formalism.HermitianLattices.RamifiedHeckeModels.imprimitive_case_count⟩

end Formalism.HermitianLattices.Final
end

