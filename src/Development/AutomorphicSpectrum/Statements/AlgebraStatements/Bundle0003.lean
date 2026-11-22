import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison

-- bundled from Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

def HodgeTateNormComparison : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C],
    v.Integers O → ∀ (E : Type) [Field E] [NumberField E] (c : E ≃+* E), (∀ x, c (c x) = x) →
    ∀ (κ : O) (N : ℕ) (V Ω : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
      [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] (P : HTPoint C O c κ N V Ω)
      (Ψ : Type) [Fintype Ψ] (τ : Ψ → (E →+* C)) (j k : Ψ → ℕ)
      (bW : ∀ s, Basis (Fin (j s)) C (P.Wsp (τ s))) (bΩ : ∀ s, Basis (Fin (k s)) C (P.Ωsp (τ s)))
      (lW : ∀ s, Fin (j s) → ℝ) (lΩ : ∀ s, Fin (k s) → ℝ),
      |P.phiDiff v τ bW bΩ lW lΩ| ≤
        ∑ s, (-Real.log (v (algebraMap O C κ)) * ((∑ i, |lW s i|) + ∑ i, |lΩ s i|) +
          -Real.log (diffAbs v (τ s)) * |∑ i, lW s i|)

def ChartSequence : Prop :=
  ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K]
    [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E), (∀ x, c (c x) = x) →
    ∀ (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
      (D : HTChart A K c p R N Ω) (κ : A) (m : ℕ), κ * (p : A) ^ m ∣ (p : A) ^ R → D.HasTestPoints κ →
      Module.Projective A D.om' →
      (D.om' ≤ D.om ∧ ∀ x ∈ D.om, κ • x ∈ D.om') ∧
      ∀ (σ : E →+* K) (d d' : A), GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' →
        Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) →
        ∃ i, D.IsDualMap σ d m i ∧ D.ExactMod σ m i

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.Statements.AlgebraStatements.RelationsStatement
section
namespace GlobalTheory.CompanionTheory.Ar.Num

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

def RelationsStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) [CharZero O] (ϖ : O), Irreducible ϖ → ∀ (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → ∀ (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ))), (∀ τ, (∃ b b' : Module.Basis (Fin (r τ)) Ω (Fin (r τ) → Ω), IsFlagPair ϖ x (Lie τ) (W τ) b b' (lie τ).x (lie τ).x' (lie τ).f (lie τ).g) ∧ ∃ b b' : Module.Basis (Fin (s τ)) Ω (Fin (s τ) → Ω), IsFlagPair ϖ x (Om τ) (OmHT τ) b b' (om τ).x (om τ).x' (om τ).f (om τ).g) → Relations (pointIdeal O x) d p φ lie om

end GlobalTheory.CompanionTheory.Ar.Num
end

