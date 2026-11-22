import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0111
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0115
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0109

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsSplitPeriod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem exists_isSplit_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ i, ∃ (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), IsSplit hP := by
  intro E _ _ _ H D l Xo σ g ty F _ _ hty _ hc i
  have hp : (F.Di i).p = D.p := (F.sig i).1
  have hq : (F.Di i).q = D.q := (F.sig i).2
  refine GlobalTheory.T.exists_splitPureTypePeriod_of_signatureSplit E H (F.Di i) g ty (by rw [hp, hq]; exact hty) ?_
  by_cases h0 : D.p = 0 ∨ D.q = 0
  · exact GlobalTheory.T.hermitianLatticeSignatureSplit_of_definite E H (F.Di i) (by rw [hp, hq]; exact h0)
  · have h1 : D.p ≠ 0 := fun h => h0 (Or.inl h)
    have h2 : D.q ≠ 0 := fun h => h0 (Or.inr h)
    rcases hc with h | h | ⟨h3, h4⟩
    · exact absurd h h1
    · exact absurd h h2
    · exact GlobalTheory.T.hermitianLatticeSignatureSplit_of_indefinite E H (F.Di i) h4 (by omega) (by omega) (by omega)

end GlobalTheory.CompRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitPeriodAnyLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_period_any_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ i, ∃ (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), IsSplit hP := by
  first | exact @GlobalTheory.CompRat.exists_isSplit_period_anyLevel | exact GlobalTheory.CompRat.exists_isSplit_period_anyLevel | (intros; apply GlobalTheory.CompRat.exists_isSplit_period_anyLevel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingAtConjugateSplitPointTransportedTwistedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.marking_at_conjugate_splitPoint_transported_twisted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P'), IsSplit hP → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → ∀ s, C.ActsBy τ io l.M' s → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a, Φ a ∈ lat hP' H.rt0 ↔ a ∈ lat hP H.rt0) ∧ (∀ a, Φ a ∈ lat hP' (-H.rt0) ↔ a ∈ lat hP (-H.rt0)) ∧ (∀ v : D.La, ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), F.t i v = a + b → ∃ e, F.t i' v = Φ (wE H s • a + H.bar (wE H s) • b) + l.A • e) ∧ ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∀ a ∈ lat hP H.rt0, ∀ b ∈ lat hP (-H.rt0), F.t i v = a + b → ∃ e, F.t i' v = Φ (wE H s • a + H.bar (wE H s) • b) + l.M • e := by
  first | exact @GlobalTheory.CompRat.marking_conj_lcm | exact GlobalTheory.CompRat.marking_conj_lcm | (intros; apply GlobalTheory.CompRat.marking_conj_lcm <;> assumption)
end

