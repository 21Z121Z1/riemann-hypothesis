import Formalism.PeriodIntegrals.ExplicitFormulaCounts.ExplicitFormula
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FamilyExplicitFormulaHolds
section
namespace Formalism.MainNotions.ShortIntervalPrimes

theorem explicit_formula_bound_holds : ∃ C : ℝ, 0 < C ∧ ∀ D : Formalism.BasicNotions.D7, adm7 D C :=
  let ⟨C, hC, hh⟩ := explicitFormula_closed
  ⟨C, hC, fun _ => hh⟩

theorem family_explicit_formula_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : adm7F Fm :=
  let ⟨C, hC, hh⟩ := explicit_formula_bound_holds
  ⟨C, hC, fun _ _ _ => hh _⟩

theorem zero_window_bound_holds : ∃ C : ℝ, 0 < C ∧ ∀ D : Formalism.BasicNotions.D7, adm11 D C :=
  let ⟨C, hC, hh⟩ := zerosWindow_closed
  ⟨C, hC, fun _ => hh⟩

theorem family_zero_window_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : ComplementTwoFamily Fm :=
  let ⟨C, hC, hh⟩ := zero_window_bound_holds
  ⟨C, hC, fun _ _ _ => hh _⟩

end Formalism.MainNotions.ShortIntervalPrimes
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.NonvanishingBesselPeriod
section
namespace Formalism.MainNotions.StandardLattice

theorem nonvanishing_bessel_period (D : Formalism.BasicNotions.D7) : NonvanishingBesselPeriod D :=
  fun _ _ lam _ _ _ _ _ σ h => Formalism.MainNotions.BridgeCSchur.fdeg_of_DS lam σ h

end Formalism.MainNotions.StandardLattice
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.UnitaryKronecker
section
open NumberField IsDedekindDomain TensorProduct Formalism.MainNotions.UnusedSlot33 Matrix ComplexOrder

namespace Formalism.MainNotions.Ext

def FinOrdG : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  (∀ φ : F →+* ℂ, ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ)) →
  ∀ (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E), IsHerm (σ : E →+* E) J → IsDef σ J →
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  ∀ U : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    U ≤ UPts σ J (FiniteAdeleRing (𝓞 F) F) →
    IsCompact (U : Set (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) →
  ∀ y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F),
  ∀ γ ∈ UJ (σ : E →+* E) J,
    bc (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) γ ∈ U.map (MulAut.conj y).toMonoidHom →
    IsOfFinOrder γ

def UnitaryKronecker : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x)) →
  ∀ (k : ℕ) (J γ : Matrix (Fin k) (Fin k) E),
    (∀ φ : E →+* ℂ, (J.map φ).PosDef ∨ (-(J.map φ)).PosDef) →
    (γ.map c)ᵀ * J * γ = J → (∀ i, IsIntegral ℤ (γ.charpoly.coeff i)) →
    ∃ n : ℕ, 0 < n ∧ γ ^ n = 1

end Formalism.MainNotions.Ext
end

