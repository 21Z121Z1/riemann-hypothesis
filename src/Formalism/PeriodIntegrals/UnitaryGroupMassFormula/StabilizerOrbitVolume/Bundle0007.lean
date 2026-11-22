import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibInfEx
import Formalism.PeriodIntegrals.Bundle0025

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RestrProd
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def LocEx : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ →
    ∃ (μinf : Measure (Fin a → Fin M → Ainf F ⊗[F] E)) (νinf : Measure (HermR (Ainf F) σ a))
      (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E))
      (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a))
      (fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E))
      (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
      SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf ∧ SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf ∧
      (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) ∧
      (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) ∧
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf ∧
      ∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)

def SdUniq : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ →
    (∀ μ1 μ2, SdW F E σ M J (Ainf F) (psiInf F ψ) a μ1 → SdW F E σ M J (Ainf F) (psiInf F ψ) a μ2 →
      μ1 = μ2) ∧
    (∀ ν1 ν2, SdHerm F E σ (Ainf F) (psiInf F ψ) a ν1 → SdHerm F E σ (Ainf F) (psiInf F ψ) a ν2 →
      ν1 = ν2) ∧
    ∀ v : HeightOneSpectrum (𝓞 F),
      (∀ μ1 μ2, SdW F E σ M J (Fv F v) (psiV F ψ v) a μ1 → SdW F E σ M J (Fv F v) (psiV F ψ v) a μ2 →
        μ1 = μ2) ∧
      (∀ ν1 ν2, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν1 →
        SdHerm F E σ (Fv F v) (psiV F ψ v) a ν2 → ν1 = ν2)

def FibPin : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ →
    (∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
      ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
      ∀ fib1 fib2 : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fib1 →
      IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fib2 →
      ∀ Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φinf → HasCompactSupport Φinf →
        ∫ X, Φinf X ∂(fib1 (hermOf (Ainf F) σ (gramE σ J X0) hT)) =
          ∫ X, Φinf X ∂(fib2 (hermOf (Ainf F) σ (gramE σ J X0) hT))) ∧
    ∀ v : HeightOneSpectrum (𝓞 F),
      ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
      ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
      ∀ fib1 fib2 : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
      IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fib1 →
      IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fib2 →
      ∀ Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φv →
        ∫ X, Φv X ∂(fib1 (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
          ∫ X, Φv X ∂(fib2 (hermOf (Fv F v) σ (gramE σ J X0) hT))

def MultFib : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ →
    ∀ (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) →
    ∀ (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a)),
    (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) →
    ∀ (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)) →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv →
      Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)))

def RestrProd : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ →
    ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) a (μv v)) →
    ∀ (νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (HermR (Fv F v) σ a)),
    (∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (νv v)) →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
        {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∀ (fibV : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E)),
    (∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
        {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fibV v)) →
    (∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv →
      Multipliable (fun v => ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)))) →
    ∃ νX : Measure (Fin a → Fin M → AF F ⊗[F] E),
      νX {X | gramR (AF F) σ J X ≠ (gramE σ J X0).map (inclR (AF F))} = 0 ∧
      ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ)
        (Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
        (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
        Continuous Φinf → HasCompactSupport Φinf → IsPureFin b Φf Φv → IsProdInfFin Φ Φinf Φf →
        Integrable Φ νX ∧
        ∫ X, Φ X ∂νX = (∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))) *
          ∏' v, ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))

theorem exOmT_of (h1 : LocEx) (h2 : SdUniq) (h3 : FibPin) (h4 : MultFib) (h5 : RestrProd) :
    ExOmT := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c1 := h1 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c2 := h2 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c3 := h3 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c4 := h4 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have c5 := h5 F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  obtain ⟨μinf, νinf, μv, νv, fibInf, fibV, hμi, hνi, hμv, hνv, hfi, hfv⟩ := c1
  obtain ⟨νX, hsupp, hform⟩ :=
    c5 μinf hμi νinf hνi μv hμv νv hνv fibInf hfi fibV hfv (c4 μv hμv νv hνv fibV hfv)
  refine ⟨νX, hsupp, ⟨μinf, hμi⟩, fun μinf' hμi' => ?_⟩
  obtain rfl := c2.1 _ _ hμi hμi'
  refine ⟨⟨νinf, hνi⟩, fun νinf' hνi' => ?_⟩
  obtain rfl := c2.2.1 _ _ hνi hνi'
  refine ⟨⟨μv, hμv⟩, fun μv' hμv' => ?_⟩
  obtain rfl : μv = μv' := funext fun v => (c2.2.2 v).1 _ _ (hμv v) (hμv' v)
  refine ⟨⟨νv, hνv⟩, fun νv' hνv' => ?_⟩
  obtain rfl : νv = νv' := funext fun v => (c2.2.2 v).2 _ _ (hνv v) (hνv' v)
  refine ⟨⟨fibInf, hfi⟩, fun fibInf' hfi' => ⟨⟨fibV, hfv⟩, fun fibV' hfv' => ?_⟩⟩
  intro d b Φ Φinf Φf Φv hc1 hc2 hp hpr
  obtain ⟨hI, hF⟩ := hform d b Φ Φinf Φf Φv hc1 hc2 hp hpr
  refine ⟨hI, c4 μv hμv νv hνv fibV' hfv' d b Φf Φv hp, ?_⟩
  rw [hF, c3.1 μinf hμi νinf hνi fibInf fibInf' hfi hfi' Φinf hc1 hc2]
  congr 1
  exact tprod_congr fun v => c3.2 v (μv v) (hμv v) (νv v) (hνv v) (fibV v) (fibV' v) (hfv v)
    (hfv' v) (Φv v) (hp.1 v)

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.VolStabFromSWOf
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem volStabFromSW_of (h1 : ExChar) (h2 : ExOmT) (h3 : ExStab) (h4 : ExFDStab)
    (h5 : SWeqOm) (h6 : Unfold) (h7 : PosTest) : PI.VolFromSW.VolStabFromSW := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc hJ' a ha1 ha2 X0 hT hdet
  refine ⟨h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet, fun ψ hψ => ?_⟩
  refine ⟨ha.1, fun μ hμ => ?_⟩
  refine ⟨h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ, fun νX hν => ?_⟩
  refine ⟨h3 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν, fun μ' hμ' => ?_⟩
  obtain ⟨hμ'H, hμ'C⟩ := hμ'
  refine ⟨(ha.2 μ hμ).1, fun 𝓕 h𝓕 => ?_⟩
  refine ⟨h4 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ' hμ'H, fun 𝓕' h𝓕' => ?_⟩
  obtain ⟨φ, hφ0, hadm, hI⟩ := h7 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν μ' hμ'H hμ'C
  have e1 := h5 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν _ hadm
  unfold meanC at e1
  have hθ : ∫ h in 𝓕, thetaS F E σ M J (fun X => (φ X : ℂ))
      {X | gramE σ J X = gramE σ J X0} h ∂μ ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at e1
    exact hI e1.symm
  obtain ⟨hfin, e2⟩ :=
    h6 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν μ' hμ'H hμ'C 𝓕' h𝓕'
      φ hφ0 hadm hθ
  rw [e2, smul_smul] at e1
  have hc1 : (μ 𝓕).toReal⁻¹ * (μ' 𝓕').toReal = 1 := by
    have e3 : ((((μ 𝓕).toReal⁻¹ * (μ' 𝓕').toReal : ℝ)) : ℂ) * ∫ X, (φ X : ℂ) ∂νX =
        1 * ∫ X, (φ X : ℂ) ∂νX := by
      rw [one_mul, ← Complex.real_smul]
      exact e1
    exact_mod_cast mul_right_cancel₀ hI e3
  have h0 : (μ 𝓕).toReal ≠ 0 := by
    intro h0
    rw [h0, inv_zero, zero_mul] at hc1
    exact zero_ne_one hc1
  have e4 : (μ 𝓕).toReal = (μ' 𝓕').toReal := (inv_mul_eq_one₀ h0).1 hc1
  exact (ENNReal.toReal_eq_toReal_iff' hfin ((ha.2 μ hμ).2 𝓕 h𝓕).ne).1 e4.symm

end PI.VolStabSW
end
end

