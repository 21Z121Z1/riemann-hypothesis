import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SeesawThetaDualPair
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0009
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.HeisenbergCommutingOperatorScalarStatement
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0008
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0011

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.SeesawThetaDualPairStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_theta_equivariance : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (ξ : E) (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (JA : Matrix α α E) (JB : Matrix β β E) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → IsQuad c ξ → IsHerm c JA → IsHerm c JB → ∀ (d : Darboux (symp (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] ξ) (JA.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) (JB.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E))) κ) (d₀ : Matrix α β E ≃ₗ[F] (κ → F) × (κ → F)), (∀ x, d.e (x.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) = (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((d₀ x).1 i), fun i => algebraMap F (AdeleRing (𝓞 F) F) ((d₀ x).2 i))) → ∀ (χ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ →* Circle) (ν : Type) [Fintype ν] [DecidableEq ν] (Cy : Matrix β ν E) (om : UG (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) (JB.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)), (∀ (z : E) (u : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ), (u : AdeleRing (𝓞 F) F ⊗[F] E) = (1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z → χ u = 1) → IsLagr c JB Cy → IsSplitting (adeleClass F) ψ d (actB (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c)) om → SiegelRule (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) (adeleClass F) ψ ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] ξ) (JA.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) (JB.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) d χ (Cy.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) om → ∀ g : UG (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) c) (JB.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)), (∃ γ : Matrix β β E, ((g : GL β (AdeleRing (𝓞 F) F ⊗[F] E)) : Matrix β β (AdeleRing (𝓞 F) F ⊗[F] E)) = γ.map fun z => ((1 : AdeleRing (𝓞 F) F) ⊗ₜ[F] z : AdeleRing (𝓞 F) F ⊗[F] E)) → ∀ Φ ∈ schA F κ, thetaSum F (om g Φ) = thetaSum F Φ := by
  first | exact @GlobalTheory.CompanionTheory.ThetaSplit.theta_split | exact GlobalTheory.CompanionTheory.ThetaSplit.theta_split | (intros; apply GlobalTheory.CompanionTheory.ThetaSplit.theta_split <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.WeilRepresentationThetaEquivariance
section
open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.AdelicSchur

theorem schur : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → ∀ T : Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ), (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) → (∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ) → (∀ w, ∀ Φ ∈ schA F κ, T (schr ψ w Φ) = schr ψ w (T Φ)) → ∃ a : ℂ, ∀ Φ ∈ schA F κ, T Φ = a • Φ := by
  intro F _ _ _ _ κ _ ψ hψc hψ1 hψF T hTS hTadm hTcomm
  obtain ⟨-, ⟨l₀, hl₀adm, hl₀⟩, -⟩ :=
    GlobalTheory.T.theta_distribution_nonzero_admissible F κ
  obtain ⟨hρS, hθinv⟩ :=
    GlobalTheory.T.theta_distribution_heisenberg_invariant F κ ψ hψc hψ1 hψF
  obtain ⟨a, ha⟩ := GlobalTheory.T.admissible_functional_rational_invariance F κ ψ hψc hψ1 hψF
    (l₀ ∘ₗ T) (hTadm l₀ hl₀adm) (by
      intro w Φ hΦ
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hTcomm _ Φ hΦ,
        hl₀ _ (hρS _ _ (hTS Φ hΦ)), hl₀ _ (hTS Φ hΦ)]
      exact hθinv w (T Φ))
  have ha' : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, l₀ (T Φ) = a * _ := ha
  refine ⟨a, fun Φ hΦ => ?_⟩
  have hlin : ∀ w, GlobalTheory.WeilM.schr ψ w (T Φ - a • Φ) =
      GlobalTheory.WeilM.schr ψ w (T Φ) - a • GlobalTheory.WeilM.schr ψ w Φ := by
    intro w
    funext x
    simp only [GlobalTheory.WeilM.schr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hmem : T Φ - a • Φ ∈ GlobalTheory.WeilM.schA F κ :=
    Submodule.sub_mem _ (hTS Φ hΦ) (Submodule.smul_mem _ a hΦ)
  refine sub_eq_zero.mp (GlobalTheory.T.theta_heisenberg_translates_separate F κ ψ hψc hψ1
    hψF _ hmem fun w => ?_)
  rw [← hl₀ _ (hρS w _ hmem), hlin w, map_sub, map_smul, ← hTcomm w Φ hΦ,
    ha' _ (hρS w Φ hΦ), hl₀ _ (hρS w Φ hΦ), smul_eq_mul, sub_self]

end GlobalTheory.CompanionTheory.AdelicSchur
end

