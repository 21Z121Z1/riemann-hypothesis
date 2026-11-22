import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLocalMultComap
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights (localMult)

theorem LocalMultComap.proof : LocalMultComap.Statement := by
  intro R S _ _ σ I W hσ hW
  set P := W.comap σ with hPdef
  have hPW : P = W.comap σ := rfl
  unfold localMult
  rw [dif_pos hW, dif_pos (Ideal.comap_isPrime σ W)]

  have hM : P.primeCompl.map σ = W.primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := hσ y
      exact ⟨x, hy, rfl⟩
  have : IsLocalization (P.primeCompl.map σ) (Localization.AtPrime W) := by
    rw [hM]; infer_instance
  let φ : Localization.AtPrime P →+* Localization.AtPrime W := Localization.localRingHom P W σ hPW
  have hφ : Function.Surjective φ := IsLocalization.map_surjective_of_surjective _ _ _ hσ
  let _ : Algebra (Localization.AtPrime P) (Localization.AtPrime W) := φ.toAlgebra
  set J : Ideal (Localization.AtPrime P) := (I.comap σ).map (algebraMap R (Localization.AtPrime P))
  set I' : Ideal (Localization.AtPrime W) := I.map (algebraMap S (Localization.AtPrime W))
  have hcomp : φ.comp (algebraMap R (Localization.AtPrime P)) =
      (algebraMap S (Localization.AtPrime W)).comp σ :=
    RingHom.ext fun x => Localization.localRingHom_to_map P W σ hPW x
  have hJ : J.map φ = I' := by
    simp only [J, I', Ideal.map_map, hcomp]
    rw [← Ideal.map_map, Ideal.map_comap_of_surjective σ hσ]
  have hker : RingHom.ker φ ≤ J := by
    intro x hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    have h0 : φ (IsLocalization.mk' _ r s) = 0 := hx
    simp only [φ, Localization.localRingHom, IsLocalization.map_mk'] at h0
    obtain ⟨⟨t, ht⟩, htr⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp h0
    obtain ⟨t', rfl⟩ := hσ t
    have hmem : t' * r ∈ I.comap σ := by
      simp only [Ideal.mem_comap, map_mul]
      rw [htr]; exact I.zero_mem
    have ht' : t' ∈ P.primeCompl := ht
    rw [IsLocalization.mk'_mem_iff]
    have h1 : algebraMap R (Localization.AtPrime P) (t' * r) ∈ J := Ideal.mem_map_of_mem _ hmem
    rw [map_mul] at h1
    have hu : IsUnit (algebraMap R (Localization.AtPrime P) t') :=
      IsLocalization.map_units _ (⟨t', ht'⟩ : P.primeCompl)
    exact (Submodule.smul_mem_iff_of_isUnit J hu).mp h1

  let ψ : Localization.AtPrime P →ₐ[Localization.AtPrime P] Localization.AtPrime W ⧸ I' :=
    (Ideal.Quotient.mkₐ _ I').comp (Algebra.ofId (Localization.AtPrime P) (Localization.AtPrime W))
  have hψ : Function.Surjective ψ :=
    (Ideal.Quotient.mkₐ_surjective (Localization.AtPrime P) I').comp hφ
  have hkerψ : RingHom.ker ψ = J := by
    have : RingHom.ker ψ = I'.comap φ := by
      ext x
      simp only [ψ, RingHom.mem_ker, Ideal.mem_comap, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Algebra.ofId_apply]
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [this, ← hJ, Ideal.comap_map_of_surjective' φ hφ, sup_eq_left.mpr hker]
  have e := (Submodule.quotEquivOfEq J (RingHom.ker ψ) hkerψ.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hψ).toLinearEquiv
  rw [e.length_eq, Module.length_eq_of_surjective hφ]

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDehomogPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def ChartDehomogPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (W : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    IsProjPrime W → linForm t ∉ W → (W ⊔ Ideal.span {linForm t - 1}).IsPrime

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StVarIntGraph
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open GroundTheory.Heights₂.Heights (varInt SmoothNear euclPot contDiff_euclPot)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
open scoped ContDiff

def VarIntGraph.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) (F : (Fin (n + 1) → ℂ) → ℝ)
    (Φ : Fin e → (Fin (n + 1) → ℂ) → ℝ),
    J.IsPrime → SmoothNear (zeroSet (graphIdeal J p)) F → (∀ k, SmoothNear (zeroSet (graphIdeal J p)) (Φ k)) →
      varInt (graphIdeal J p) e F Φ = varInt J e (fun x => F (graphPt p x)) (fun k x => Φ k (graphPt p x))

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StVarIntGraphInt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory
open GroundTheory.Heights₂.Heights (varInt SmoothNear chartAbsDens)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet IsFiniteProjection)

def VarIntGraphInt.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) (F : (Fin (n + 1) → ℂ) → ℝ)
    (Φ : Fin e → (Fin (n + 1) → ℂ) → ℝ),
    J.IsPrime → SmoothNear (zeroSet (graphIdeal J p)) F → (∀ k, SmoothNear (zeroSet (graphIdeal J p)) (Φ k)) →
    (∀ B : Matrix (Fin e) (Fin (n + 1)) ℂ, IsFiniteProjection (graphIdeal J p) B →
      Integrable (chartAbsDens (graphIdeal J p) B F Φ)) →
      varInt (graphIdeal J p) e F Φ = varInt J e (fun x => F (graphPt p x)) (fun k x => Φ k (graphPt p x))

end GroundTheory.Heights₂.Heights.Targets
end
end

