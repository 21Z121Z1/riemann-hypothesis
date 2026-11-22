import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0269
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0311
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0339
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ImportsBis
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem strongApproxSU : GlobalTheory.Published.StrongApproxSU := by
  intro F E _ _ _ _ _ σ hCM M J hM hJ S₁ S₂ ε hε hnc g hg
  obtain ⟨N, hN⟩ := GlobalTheory.CompanionTheory.StrongApproxSub.propSub F E σ M J ε
  have hcl : IsClosed (N : Set (HA (AF F) σ J)) := hN ▸ isClosed_closure
  have hS : SUSupp σ J ε ⊆ N := by
    intro h hh
    have : h ∈ closure (SASet σ J ε) := subset_closure ⟨1, one_mem _, h, hh, (one_mul h).symm⟩
    rw [← hN] at this
    exact this
  have hplane : ∀ u₀ u₁ : Fin M → E, PlaneND σ J u₀ u₁ → ¬ IsCompact (PlaneSupp σ J ε u₀ u₁) →
      ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (δ : AF F), IsPlacesIdem T₁ T₂ δ →
        PlaneSupp σ J δ u₀ u₁ ⊆ N := by
    intro u₀ u₁ hnd hc T₁ T₂ δ hδ x hx
    have h := GlobalTheory.T.plane_strong_approx_holds F E σ hCM M J hM hJ S₁ S₂ ε hε u₀ u₁ hnd hc T₁ T₂ δ hδ hx
    rw [← hN] at h
    exact h
  have hgen := GlobalTheory.T.plane_strong_approx_generator F E σ hCM M J hM hJ S₁ S₂ ε hε hnc N hcl hS hplane
  have hmem : g ∈ N := GlobalTheory.T.plane_strong_approx_product F E σ M J N hcl hgen g hg
  have : g ∈ (N : Set (HA (AF F) σ J)) := hmem
  rwa [hN] at this

end GlobalTheory.CompanionTheory.Hypotheses₂

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def thetaInt (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) : ℂ :=
  ∫ h in 𝓕, theta σ J Φ h ∂μ

def thetaPart (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) (S : Set (Fin 1 → Fin M → E)) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) : ℂ :=
  ∫ h in 𝓕, ∑' x : S, thetaTerm σ J Φ h x.1 ∂μ

def lev (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) : Set (Fin 1 → Fin M → E) :=
  {x | x ≠ 0 ∧ gramE σ J x = fun _ _ => algebraMap F E t}

def starT (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (b : AF F) : ℂ :=
  ∫ x, Φ x * ψ (b * qR (AF F) σ J (x 0)) ∂dx

def coefT (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (db : Measure (AF F))
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (t : F) : ℂ :=
  ∫ b, starT σ J ψ dx Φ b * ψ (-(algebraMap F (AF F) t * b)) ∂db

def fouV (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ)
    (y : Fin 1 → Fin M → AF F ⊗[F] E) : ℂ :=
  ∫ x, Φ x * ψ (BR (AF F) σ J x y) ∂dx

def unipV (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ) (b : AF F)
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (x : Fin 1 → Fin M → AF F ⊗[F] E) : ℂ :=
  ψ (b * qR (AF F) σ J (x 0)) * Φ x

def dilV {M : ℕ} (θ : ℝ →+* Ainf F) (a : ℝ) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ)
    (x : Fin 1 → Fin M → AF F ⊗[F] E) : ℂ :=
  Φ fun i j => (pairA F (θ a) 1 ⊗ₜ[F] (1 : E)) * x i j

def IsCovolOne (db : Measure (AF F)) : Prop :=
  db.IsAddHaarMeasure ∧ ∃ D : Set (AF F),
    IsAddFundamentalDomain (algebraMap F (AF F)).toAddMonoidHom.range D db ∧ db D = 1

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV
end
end

